import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Tactic.Rify
import Paperproof

variable (α : Type)

class DedekindHasseDomain extends CommRing α, IsDomain α where
  r : α → α → Prop
  r_wellFounded : WellFounded r
  linear_comb : ∀ u v: α, (u ∣ v) ∨ (∃ s t: α, r 0 (s * u + t * v) ∧ r (s * u + t * v) u)

theorem dedekind_hasse_domain_implies_pid [δ : DedekindHasseDomain α] : IsPrincipalIdealRing α := by
  apply IsPrincipalIdealRing.mk
  intro ideal
  apply Submodule.IsPrincipal.mk
  cases em (∃ x : α, x ≠ 0 ∧ ideal.carrier x) with
  | inl normal =>
    let non_zero : Set α := λ x => x ≠ 0 ∧ ideal.carrier x
    have min_not_small := by
      apply WellFounded.has_min (δ.r_wellFounded) non_zero
      apply normal.elim
      intro v hv
      exact Exists.intro v hv
    apply min_not_small.elim
    intro γ hγ
    apply Exists.intro ↑↑γ
    apply Ideal.ext
    intro v
    apply Iff.intro
    . intro in_ideal
      cases em (↑↑γ ∣ v) with
      | inl div =>
        rw [Submodule.mem_span_singleton]
        apply Exists.elim div
        intro κ hκ
        apply Exists.intro κ
        simp
        rw [mul_comm]
        exact hκ.symm
      | inr abs =>
        cases δ.linear_comb γ v with
        | inl =>
          contradiction
        | inr lin =>
          apply Exists.elim lin
          intro s hs
          apply Exists.elim hs
          intro t ht
          let lin_comb : non_zero := by
            apply Subtype.mk (s * ↑↑γ + t * v)
            apply And.intro
            . simp
              by_contra abs
              apply (WellFounded.wellFounded_iff_no_descending_seq.mp δ.r_wellFounded).false
              apply Subtype.mk (λ _ => 0)
              intro
              conv in (occs := 2) 0 => rw [←abs]
              exact ht.left
            . apply ideal.add_mem'
              . simp
                exact ideal.smul_mem' s hγ.left.right
              . simp
                exact ideal.smul_mem' t in_ideal
          have := ht.right
          have := hγ.right lin_comb lin_comb.property
          contradiction
    . rw [Submodule.mem_span_singleton]
      intro in_span_γ
      apply in_span_γ.elim
      intro κ hκ
      rw [←hκ]
      exact ideal.smul_mem' κ hγ.left.right
  | inr stupid =>
    apply Exists.intro 0
    simp
    apply Ideal.ext
    intro v
    apply Iff.intro
    . intro in_id
      apply Submodule.mem_span.mpr
      intro p hp
      have v_zero : v = 0 := by
        by_contra abs
        apply stupid
        apply Exists.intro v
        apply And.intro
        repeat assumption
      rw [v_zero]
      simp
    . intro in_span_zero
      rw [eq_zero_of_zero_dvd (Ideal.mem_span_singleton.mp in_span_zero)]
      exact ideal.zero_mem

def small [δ : CommRing α] [IsDomain α] : Set α :=
  λ x => x = 0 ∨ ∃ x' : α, x * x' = 1

def is_universal_side_divisor [δ : CommRing α] [IsDomain α] (u : α) :=
  ∀ x : α, ∃ q r : α, x = u * q + r ∧ r ∈ small α

theorem euclidean_domain_has_usd [δ : EuclideanDomain α] : (small α)ᶜ.Nonempty → ∃ u : α, is_universal_side_divisor α u := by
  intro has_not_small
  have min_not_small := WellFounded.has_min (δ.r_wellFounded) (small α)ᶜ has_not_small
  apply min_not_small.elim
  intro m hm
  apply Exists.intro m
  intro v
  apply Exists.intro (v / m)
  apply Exists.intro (v % m)
  apply And.intro
  . exact (δ.quotient_mul_add_remainder_eq v m).symm
  . have in_r : δ.r (v % m) m := by
      apply δ.remainder_lt v
      have prop : ¬(m = 0 ∨ _) := hm.left
      simp at prop
      exact prop.left
    have alt := imp_not_comm.mp (hm.right (v % m)) in_r
    simp at alt
    exact alt

def R : Set ℂ :=
  λ c => ∃ x y : ℤ, (c = Complex.mk ((Int.cast x) / 2) (√19 * (Int.cast y) / 2)) ∧ x ≡ y [ZMOD 2]

lemma div_and_mul_by_k_on_mult {k : ℤ} (x : ℤ) : x ≡ 0 [ZMOD k] → k * (x / k) = x := by
  intro mult
  have th := Int.ediv_add_emod x k
  rw [mult] at th
  simp at th
  exact th

lemma div_by_k_exact_on_mult {k : ℤ} (x : ℤ) : k ≠ 0 → x ≡ 0 [ZMOD k] → (x : ℝ) / k = ↑(x / k) := by
  intro k_not_zero mult
  rify at k_not_zero
  let x' := x / k
  let xr := (x : ℝ) / k

  have two_xr_eq_x : k * xr = x := calc
    k * xr = k * (↑x / (k : ℝ)) := by rfl
    _ = k * (↑x * (k : ℝ)⁻¹) := by rw [div_eq_mul_inv ↑x (k : ℝ)]
    _ = k * ((k : ℝ)⁻¹ * ↑x) := by conv in ((k : ℝ)⁻¹ * ↑x) => rw [mul_comm]
    _ = k * (k : ℝ)⁻¹ * ↑x := by rw [←mul_assoc]
    _ = x := by rw [Field.mul_inv_cancel (k : ℝ) k_not_zero]; simp

  have two_x'_eq_x : (k * x' : ℝ) = (x : ℝ) := by
    have th := div_and_mul_by_k_on_mult x mult
    rify at th
    exact th

  calc
    xr = (k * (k : ℝ)⁻¹) * xr := by rw [Field.mul_inv_cancel (k : ℝ) k_not_zero]; simp
    _ = ((k : ℝ)⁻¹ * k) * xr := by conv in ((k : ℝ)⁻¹ * k) => rw [mul_comm]
    _ = (k : ℝ)⁻¹ * (k * xr) := by rw [mul_assoc]
    _ = (k : ℝ)⁻¹ * (x : ℝ) := by rw [two_xr_eq_x]
    _ = (k : ℝ)⁻¹ * (k * x' : ℝ) := by rw [two_x'_eq_x]
    _ = ((k : ℝ)⁻¹ * k) * (x' : ℝ) := by rw [←mul_assoc]
    _ = (k * (k : ℝ)⁻¹) * (x' : ℝ) := by conv in ((k : ℝ)⁻¹ * k) => rw [mul_comm]
    _ = x' := by rw [Field.mul_inv_cancel (k : ℝ) k_not_zero]; simp

theorem R_closed_under_complex_addition (z₁ z₂ : ℂ) : R z₁ → R z₂ → R (z₁ + z₂) := by
  intro h₁ h₂
  apply h₁.elim
  intro x₁ h₁'
  apply h₁'.elim
  intro y₁ h₁''
  apply h₂.elim
  intro x₂ h₂'
  apply h₂'.elim
  intro y₂ h₂''
  apply Exists.intro (x₁ + x₂)
  apply Exists.intro (y₁ + y₂)
  apply And.intro
  . rw [h₁''.left]
    rw [h₂''.left]
    apply Complex.ext
    . simp [Complex.add_re]
      ring_nf
    . simp [Complex.add_im]
      ring_nf
  . have ε₁ := h₁''.right
    have ε₂ := h₂''.right
    exact Int.ModEq.add ε₁ ε₂

theorem R_closed_under_complex_multiplication (z₁ z₂ : ℂ) : R z₁ → R z₂ → R (z₁ * z₂) := by
  intro h₁ h₂
  apply h₁.elim
  intro x₁ h₁'
  apply h₁'.elim
  intro y₁ h₁''
  apply h₂.elim
  intro x₂ h₂'
  apply h₂'.elim
  intro y₂ h₂''

  let x := x₁ * x₂ - (y₁ * y₂) * 19
  let y := (x₁ * y₂) + (y₁ * x₂)

  have x_even := calc
    x₁ * x₂ - (y₁ * y₂) * 19 ≡ x₁ * x₂ - 19 * (y₁ * y₂) [ZMOD 2] := by conv in (19 * (y₁ * y₂)) => rw [mul_comm]
    _ ≡ y₁ * y₂ - 19 * (y₁ * y₂) [ZMOD 2] := by
      apply Int.ModEq.sub_right (19 * (y₁ * y₂))
      exact Int.ModEq.mul h₁''.right h₂''.right
    _ ≡ 1 * (y₁ * y₂) - 19 * (y₁ * y₂) [ZMOD 2] := by conv in (y₁ * y₂) => rw [←one_mul (y₁ * y₂)]
    _ ≡ (-18) * (y₁ * y₂) [ZMOD 2] := by
      rw [←mul_sub_right_distrib 1 19 (y₁ * y₂)]
      simp
    _ ≡ 0 * (y₁ * y₂) [ZMOD 2] := Int.ModEq.mul_right (y₁ * y₂) rfl
    _ ≡ 0 [ZMOD 2] := by simp

  have y_even := calc
    (x₁ * y₂) + (y₁ * x₂) ≡ (x₁ * y₂) + (x₂ * y₁) [ZMOD 2] := by conv in (y₁ * x₂) => rw [mul_comm]
    _ ≡ (x₁ * x₂) + (x₂ * x₁) [ZMOD 2] := by
      apply Int.ModEq.add
      . apply Int.ModEq.mul rfl h₂''.right.symm
      . apply Int.ModEq.mul rfl h₁''.right.symm
    _ ≡ (x₁ * x₂) + (x₁ * x₂) [ZMOD 2] := by rw [mul_comm]
    _ ≡ (1 * (x₁ * x₂)) + (1 * (x₁ * x₂)) [ZMOD 2] := by rw [one_mul]
    _ ≡ 2 * (x₁ * x₂) [ZMOD 2] := by
      rw [←right_distrib 1 1 (x₁ * x₂)]
      simp
    _ ≡ 0 * (x₁ * x₂) [ZMOD 2] := Int.ModEq.mul_right (x₁ * x₂) rfl
    _ ≡ 0 [ZMOD 2] := by simp

  have eqx := div_by_k_exact_on_mult x two_ne_zero x_even
  have eqy := div_by_k_exact_on_mult y two_ne_zero y_even

  apply Exists.intro (x / 2)
  apply Exists.intro (y / 2)
  apply And.intro
  . rw [h₁''.left]
    rw [h₂''.left]
    apply Complex.ext
    . simp [Complex.mul_re]
      ring_nf
      simp
      ring_nf
      rw [←eqx]
      ring_nf
      rify
      rw [mul_sub_right_distrib]
      ring_nf
    . simp [Complex.mul_im]
      ring_nf
      simp
      rw [←eqy]
      ring_nf
      rify
      rw [left_distrib (√19) (x₁ * y₂) (y₁ * x₂)]
      rw [right_distrib (√19 * ((x₁ : ℝ) * (y₂ : ℝ))) (√19 * ((y₁ : ℝ) * (x₂ : ℝ))) (1 / 4)]
      ring_nf
  . have div4 : 4 ∣ (((x₁ * x₂) + (y₁ * y₂)) - ((x₁ * y₂) + (y₁ * x₂))) := by
      apply (Int.ModEq.dvd h₁''.right).elim
      intro n hn
      apply (Int.ModEq.dvd h₂''.right).elim
      intro m hm
      apply Exists.intro (n * m)
      calc
        ((x₁ * x₂) + (y₁ * y₂)) - ((x₁ * y₂) + (y₁ * x₂)) = (y₁ - x₁) * (y₂ - x₂) := by ring_nf
        _ = (2 * n) * (2 * m) := by rw [hn, hm]
        _ = 4 * (n * m) := by ring_nf

    have obv : -20 ≡ 0 [ZMOD 4] := rfl
    have sub := Int.ModEq.mul_right (y₁ * y₂) obv
    simp at sub

    have eq : 2 * (x / 2) ≡ 2 * (y / 2) [ZMOD 4] := by
      rw [div_and_mul_by_k_on_mult x x_even]
      rw [div_and_mul_by_k_on_mult y y_even]
      calc
        x₁ * x₂ - (y₁ * y₂) * 19 = (-(20 * (y₁ * y₂))) + ((x₁ * x₂) + (y₁ * y₂)) := by ring_nf
        _ ≡ 0 + ((x₁ * x₂) + (y₁ * y₂)) [ZMOD 4] := Int.ModEq.add sub rfl
        _ ≡ (x₁ * x₂) + (y₁ * y₂) [ZMOD 4] := by simp
        _ ≡ y [ZMOD 4] := (Int.modEq_of_dvd div4).symm

    apply Int.ModEq.cancel_left_div_gcd (Int.sign_eq_one_iff_pos.mp rfl) eq

def R_subsemigroup : Subsemigroup ℂ := by
  apply Subsemigroup.mk R
  intro a b ha hb
  exact R_closed_under_complex_multiplication a b ha hb

def R_submonoid : Submonoid ℂ := by
  apply Submonoid.mk R_subsemigroup
  apply Exists.intro 2
  apply Exists.intro 0
  apply And.intro
  . simp
    rfl
  . rfl

def R_add_subsemigroup : AddSubsemigroup ℂ := by
  apply AddSubsemigroup.mk R
  intro a b ha hb
  exact R_closed_under_complex_addition a b ha hb

def R_add_submonoid : AddSubmonoid ℂ := by
  apply AddSubmonoid.mk R_add_subsemigroup
  apply Exists.intro 0
  apply Exists.intro 0
  apply And.intro
  . simp
    rfl
  . rfl

def R_add_subgroup : AddSubgroup ℂ := by
  apply AddSubgroup.mk R_add_submonoid
  intro x hx
  apply hx.elim
  intro n hn
  apply hn.elim
  intro m hm
  apply Exists.intro (-n)
  apply Exists.intro (-m)
  apply And.intro
  . rw [hm.left]
    apply Complex.ext
    . field_simp
    . field_simp
  . simp
    exact hm.right

def R_subring : Subring ℂ :=
  Subring.mk' R R_submonoid R_add_subgroup rfl rfl

def D : CommRing R_subring :=
  Subring.toCommRing R_subring

def D' : IsDomain R_subring :=
  Subring.instIsDomainSubtypeMem R_subring

lemma sq_of_eq_mod_two_eq_mod_four {n m : ℤ} : n ≡ m [ZMOD 2] → n * n ≡ m * m [ZMOD 4] := by
  intro h
  rw [Int.modEq_iff_dvd] at h
  rw [Int.modEq_iff_dvd]
  apply h.elim
  intro k hk
  have eq : 2 * k + n = m := calc
    2 * k + n = (m - n) + n := by rw [←hk]
    _ = m := by simp
  apply Exists.intro (k * k + k * n)
  calc
    m * m - n * n = (2 * k + n) * (2 * k + n) - n * n := by rw [eq]
    _ = 4 * (k * k + k * n) := by ring

lemma pos_eq_to_nat {n : ℤ} : 0 ≤ n → n = n.toNat := by
  intro
  cases n with
  | ofNat n => simp
  | negSucc n => contradiction

theorem sq_norm_is_integer_on_R (r : R) : ∃ n : ℕ, Complex.normSq r = n := by
  apply r.property.elim
  intro x hx
  apply hx.elim
  intro y hy

  let n := ((x * x + 19 * y * y) : ℝ) / 4
  let nn := (x * x + 19 * y * y) / 4
  let nn_nat := ((x * x + 19 * y * y) / 4).toNat

  have n_eq_nn := by
    apply div_by_k_exact_on_mult (x * x + 19 * y * y)
    . exact four_ne_zero
    . have eq : x * x ≡ y * y [ZMOD 4] := sq_of_eq_mod_two_eq_mod_four hy.right
      calc
        _ ≡ y * y + 19 * y * y [ZMOD 4] := Int.ModEq.add_right (19 * y * y) eq
        _ = 20 * y * y := by ring
        _ ≡ 0 [ZMOD 4] := by
          rw [Int.modEq_iff_dvd]
          simp
          apply Exists.intro (5 * y * y)
          ring

  have nn_nat_eq_nn : nn = nn_nat := by
    apply pos_eq_to_nat
    apply Int.ediv_nonneg
    . apply Int.add_nonneg
      . exact mul_self_nonneg x
      . rw [mul_assoc]
        apply Int.mul_nonneg
        . exact Int.le.intro_sub (19 + 0) rfl
        . exact mul_self_nonneg y
    . exact zero_le_four

  rify at nn_nat_eq_nn
  rify at n_eq_nn

  apply Exists.intro nn_nat
  rw [←nn_nat_eq_nn]
  rw [←n_eq_nn]
  rw [hy.left]
  repeat (simp; ring_nf)

def dh_rel_on_r (r₁ r₂ : R) : Prop :=
  Complex.normSq r₁ < Complex.normSq r₂

theorem dh_rel_on_r_well_founded : WellFounded dh_rel_on_r := by
  apply WellFounded.wellFounded_iff_no_descending_seq.mpr
  by_contra abs
  simp at abs
  apply abs.elim
  intro f hf
  let g : ℕ → ℕ := λ n => ⌊Complex.normSq (f n)⌋₊
  have abs : ∀ n : ℕ, (g (n + 1)) < (g n) := by
    intro n
    have eq : ∀ n : ℕ, g n = Complex.normSq (f n) := by
      intro x
      apply (sq_norm_is_integer_on_R (f x)).elim
      intro n hn
      rw [hn]
      simp
      calc
        ⌊Complex.normSq (f x)⌋₊ = ⌊(n : ℝ)⌋₊ := by rw [hn]
        _ = n := by simp
    rify
    rw [eq n, eq (n + 1)]
    exact hf n
  apply (WellFounded.wellFounded_iff_no_descending_seq.mp (Nat.lt_wfRel.wf)).false
  exact Subtype.mk g abs
