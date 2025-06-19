import Mathlib.Tactic.IntervalCases
import NonEuclideanPid.RingConstruction

variable (α : Type u)

class DedekindHasseDomain extends CommRing α, IsDomain α where
  r : α → α → Prop
  r_wellFounded : WellFounded r
  linear_comb {u v : α} : (u ≠ 0) → ¬(u ∣ v) → (∃ s t: α, r 0 (s * u + t * v) ∧ r (s * u + t * v) u)

theorem dedekind_hasse_domain_implies_pid [δ : DedekindHasseDomain α] : IsPrincipalIdealRing α := by
  apply IsPrincipalIdealRing.mk
  intro ideal
  apply Submodule.IsPrincipal.mk
  cases em (∃ x : α, x ≠ 0 ∧ ideal.carrier x) with
  | inl normal =>
    let non_zero : Set α := λ x => x ≠ 0 ∧ ideal.carrier x
    have min_not_small := WellFounded.has_min (δ.r_wellFounded) non_zero normal
    apply min_not_small.imp
    intro γ hγ
    apply Ideal.ext
    intro v
    apply Iff.intro
    . intro in_ideal
      cases em (γ ∣ v) with
      | inl div =>
        rw [Submodule.mem_span_singleton]
        apply div.imp
        intro κ hκ
        rw [smul_eq_mul, mul_comm]
        exact hκ.symm
      | inr abs =>
          have ⟨s, t, h⟩ := δ.linear_comb hγ.left.left abs
          let lin_comb : non_zero := by
            apply Subtype.mk (s * γ + t * v)
            apply And.intro
            . by_contra abs
              apply (WellFounded.wellFounded_iff_no_descending_seq.mp δ.r_wellFounded).false
              apply Subtype.mk (λ _ => 0)
              intro
              conv in (occs := 2) 0 => rw [←abs]
              exact h.left
            . have := ideal.smul_mem' s hγ.left.right
              have := ideal.smul_mem' t in_ideal
              apply ideal.add_mem'
              repeat simpa
          have := h.right
          have := hγ.right lin_comb lin_comb.property
          contradiction
    . rw [Submodule.mem_span_singleton]
      intro in_span_γ
      have ⟨κ, hκ⟩ := in_span_γ
      rw [←hκ]
      exact ideal.smul_mem' κ hγ.left.right
  | inr stupid =>
    rw [not_exists] at stupid
    conv at stupid in ¬_ => rw [not_and', ne_eq, not_not]
    exists 0
    rw [Ideal.submodule_span_eq]
    apply Ideal.ext
    intro v
    apply Iff.intro
    . intro in_id
      have v_zero : v = 0 := stupid v in_id
      simp [v_zero]
    . intro in_span_zero
      rw [eq_zero_of_zero_dvd (Ideal.mem_span_singleton.mp in_span_zero)]
      exact ideal.zero_mem

@[simp]
def dh_rel_on_r (r₁ r₂ : R) : Prop :=
  Complex.normSq r₁ < Complex.normSq r₂

theorem dh_rel_on_r_well_founded : WellFounded dh_rel_on_r := by
  apply WellFounded.wellFounded_iff_no_descending_seq.mpr
  by_contra abs
  simp only [dh_rel_on_r, not_isEmpty_iff, nonempty_subtype] at abs
  have ⟨f, hf⟩ := abs
  have ⟨g', hg⟩ := Classical.skolem.mp sq_norm_is_integer_on_R
  let g := g' ∘ f
  have abs : ∀ n : ℕ, g (n + 1) < g n := by
    simp [g]
    rify
    conv in _ < _ => rw [←hg, ←hg]
    exact hf
  apply (WellFounded.wellFounded_iff_no_descending_seq.mp (Nat.lt_wfRel.wf)).false
  exact ⟨g, abs⟩

lemma norm_frac (s t u v : R) :
  u.val ≠ 0 →
  Complex.normSq u * Complex.normSq (s + t * v / u) = Complex.normSq (s * u + t * v : R)
:= by
  intro nzero_c
  rw [←Complex.normSq_mul, mul_add, mul_comm]
  conv in _ * (_ / _) => rw [mul_comm, div_eq_mul_inv, mul_assoc]
  conv in (_⁻¹ * _) => rw [mul_comm, Field.mul_inv_cancel (u : ℂ) nzero_c]
  simp [mul_one, Subring.coe_add R_subring, Subring.coe_mul R_subring]

lemma in_strip_low_distance {h k : ℤ} {u v : R} (t : R) :
  ((u : ℂ) ≠ 0) →
  (h ≡ k [ZMOD 2] ∧ |(t * v.val / u).re - ↑h / 2| ≤ 1 / 2) →
  (t * v.val / u).im ∈ Set.Ioo (↑k * √19 / 2 - √3 / 2) (↑k * √19 / 2 + √3 / 2) →
  ∃ s, dh_rel_on_r (s * u + t * v) u
:= by
  intro nzero_c hh hk
  let s : R := by
    apply Subtype.mk (Complex.mk (-h / 2) (-k / 2 * √19))
    exists -h, -k
    apply And.intro
    . simp only [Int.cast_neg, mul_neg, Complex.mk.injEq, true_and]
      ring_nf
    . have := hh.left
      simpa
  exists s
  rw [dh_rel_on_r]
  have eq2 : Complex.normSq u = Complex.normSq u * 1 := by simp
  rw [←norm_frac s t u v nzero_c]
  conv_rhs => rw [eq2]
  apply mul_lt_mul_of_pos_left
  . simp only [Complex.normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re, Complex.add_im]
    rw [(rfl : s.val.re = - h / 2), (rfl : s.val.im = - k / 2 * √19)]

    let re_sq := ((t * v.val / u).re - ↑h / 2)
    let im_sq := (-↑k / 2 * √19 + (t * v.val / u).im)
    have eq3 : re_sq ^ 2 = (-↑h / 2 + (t * v.val / u).re) * (-↑h / 2 + (t * v.val / u).re) := by ring
    have eq4 : im_sq ^ 2 = (-↑k / 2 * √19 + (t * v.val / u).im) * (-↑k / 2 * √19 + (t * v.val / u).im) := by ring
    have eq5 : (1 / 2) ^ 2 + (√3 / 2) ^ 2 = 1 := by
      field_simp
      norm_cast
    rw [←eq3, ←eq4, ←eq5]

    apply add_lt_add_of_le_of_lt
    . have diseq : √(re_sq ^ 2) ≤ (1 / 2) := by
        simp only [Real.sqrt_sq_eq_abs, re_sq]
        exact hh.right
      exact (Real.sqrt_le_iff.mp diseq).right
    . have diseq : √(im_sq ^ 2) < (√3 / 2) := by
        simp only [Real.sqrt_sq_eq_abs, im_sq]
        apply abs_lt.mpr
        apply And.intro
        . rw [add_comm]
          conv in -↑k / 2 * √19 => rw [neg_eq_neg_one_mul, div_eq_mul_inv, mul_assoc, mul_assoc, ←neg_eq_neg_one_mul, ←div_eq_inv_mul]
          apply lt_sub_iff_add_lt.mpr
          rw [add_comm, ←sub_eq_add_neg]
          have tg := hk.left
          ring_nf at tg
          ring_nf
          exact tg
        . rw [neg_eq_neg_one_mul, div_eq_mul_inv, mul_assoc, mul_assoc, ←neg_eq_neg_one_mul, neg_add_eq_sub, ←div_eq_inv_mul]
          apply sub_lt_iff_lt_add.mpr
          conv_rhs => rw [add_comm, mul_div_assoc']
          exact hk.right
      exact Real.lt_sq_of_sqrt_lt diseq
  . simpa

lemma small_of_small_sum (x y : ℝ) : x + y ≤ 1 → x ≤ 1 / 2 ∨ y ≤ 1 / 2 := by
  intro
  by_contra abs
  simp only [not_or] at abs
  linarith

lemma close_int (x : ℝ) : ∃ l : ℤ, |x - l| ≤ 1 / 2 := by
  have poss : |x - ⌊x⌋| ≤ 1 / 2 ∨ |x - ⌈x⌉| ≤ 1 / 2 := by
    rw [abs_of_nonneg (sub_nonneg_of_le (Int.floor_le x))]
    rw [abs_of_nonpos (tsub_nonpos.mpr (Int.le_ceil x))]
    apply small_of_small_sum
    calc
      x - ↑⌊x⌋ + -(x - ↑⌈x⌉) = ⌈x⌉ - ⌊x⌋ := by ring
      _ ≤ 1 := by
        norm_cast
        exact sub_left_le_of_le_add (Int.ceil_le_floor_add_one x)
  apply poss.elim
  . intro h
    exists ⌊x⌋
  . intro h
    exists ⌈x⌉

lemma real_part (x : ℝ) : ∀ k : ℤ, ∃ l : ℤ, l ≡ k [ZMOD 2] ∧ |x - l / 2| ≤ 1 / 2 := by
  intro k
  have th : ∀ x : ℝ, ∃ l : ℤ, l ≡ 0 [ZMOD 2] ∧ |x - l / 2| ≤ 1 / 2 := by
    intro x
    have ⟨l, hl⟩ := close_int x
    exists 2 * l
    apply And.intro
    . apply Int.modEq_iff_dvd.mpr
      exists -l
      simp
    . simp at hl
      simpa
  cases Int.emod_two_eq_zero_or_one k with
  | inl zero =>
    apply (th x).imp
    intro k hk
    apply And.intro
    . exact Int.ModEq.trans hk.left zero.symm
    . exact hk.right
  | inr one =>
    have ⟨k, hk⟩ := th (x - 1 / 2)
    exists k + 1
    apply And.intro
    . exact Int.ModEq.trans (Int.ModEq.add_right 1 hk.left) one.symm
    . rify
      ring_nf
      have tg := hk.right
      ring_nf at tg
      exact tg

lemma fract_not_zero_of_mod_not_zero {a b : ℤ} : b > 0 → ¬ a ≡ 0 [ZMOD b] → ¬Int.fract ((a : ℝ) / b) = 0 := by
  intro pos neq
  have pos_r : (b : ℝ) > 0 := by norm_cast
  have nzero_r : (b : ℝ) ≠ 0 := by
    apply ne_of_gt
    norm_cast
  rw [←Int.euclideanDomain.quotient_mul_add_remainder_eq a b]
  push_cast
  have eq₀ : Int.euclideanDomain.quotient = (· / ·) := rfl
  have eq₁ : Int.euclideanDomain.remainder = (· % ·) := rfl
  rw [eq₀, eq₁, ←ne_eq, add_div, mul_comm, mul_div_assoc, div_self nzero_r, mul_one, Int.fract_int_add, ne_eq]
  apply ne_of_gt
  apply Int.fract_pos.mpr
  have rhs_zero : ⌊((a % b) : ℝ) / b⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    apply And.intro
    . push_cast
      apply div_nonneg
      . norm_cast
        exact Int.emod_nonneg a (ne_of_gt pos)
      . exact le_of_lt pos_r
    . rw [Int.cast_zero, zero_add]
      apply (div_lt_one pos_r).mpr
      norm_cast
      exact Int.emod_lt_of_pos a pos
  rw [rhs_zero]
  have th : (a % b : ℝ) / b ≠ 0 := by
    refine div_ne_zero ?_ (ne_of_gt pos_r)
    norm_cast
  norm_cast at th
  norm_cast

lemma fract_not_zero_of_mod_not_zero_q {a b : ℤ} : b > 0 → ¬ a ≡ 0 [ZMOD b] → ¬Int.fract (Rat.divInt a b) = 0 := by
  intro pos neq
  rify
  exact fract_not_zero_of_mod_not_zero pos neq

lemma odd_one_mod_eight {n : ℤ} : n ≡ 1 [ZMOD 2] → n ^ 2 ≡ 1 [ZMOD 8] := by
  intro h
  generalize hn : n % 8 = k
  have : 0 ≤ k := by omega
  have : k ≤ 7 := by omega
  interval_cases k
  all_goals
  by_contra
  simp_all [Int.ModEq, Int.pow_succ, Int.mul_emod]
  try omega

lemma even_zero_or_two_mod_four {n : ℤ} : n ≡ 0 [ZMOD 2] → (n ≡ 0 [ZMOD 4] ∨ n ≡ 2 [ZMOD 4]) := by
  intro h
  generalize hn : n % 4 = k
  have : 0 ≤ k := by omega
  have : k ≤ 3 := by omega
  interval_cases k
  all_goals
  simp_all [Int.ModEq, Int.pow_succ, Int.mul_emod]
  try omega

lemma sq_zero_mod_four_zero_mod_eight {n : ℤ} : n ≡ 0 [ZMOD 4] → n ^ 2 ≡ 0 [ZMOD 8] := by
  intro h
  have ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h.symm
  rw [sub_zero] at hk
  rw [hk]
  apply Int.modEq_iff_dvd.mpr
  exists -2 * k ^ 2
  ring_nf

lemma sq_two_mod_four_four_mod_eight {n : ℤ} : n ≡ 2 [ZMOD 4] → n ^ 2 ≡ 4 [ZMOD 8] := by
  intro h
  have ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h.symm
  rw [Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hk)))]
  apply Int.modEq_iff_dvd.mpr
  exists (-2 * k ^ 2 - 2 * k)
  ring_nf

@[simp]
lemma strip_diseq : (√19 - 2 * √3) / 2 < √3 / 2 := by
  cancel_denoms
  apply sub_right_lt_of_lt_add
  refine (Real.sqrt_lt' ?_).mpr ?_
  . ring_nf
    exact mul_pos (Real.sqrt_pos_of_pos three_pos) three_pos
  . ring_nf
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
    norm_cast

lemma twice_in_strip {x : ℝ} :
(¬∃ k : ℤ, x ∈ Set.Ioo (↑k * √19 / 2 - √3 / 2) (↑k * √19 / 2 + √3 / 2)) →
(∃ k : ℤ, 2 * x ∈ Set.Ioo (k * √19 / 2 - √3 / 2) (k * √19 / 2 + √3 / 2)) := by
  intro not_in_strip
  have in_strip : ∃ k : ℤ, x ∈ Set.Icc (k * (√19 / 2) + √3 / 2) ((k + 1) * (√19 / 2) - √3 / 2) := by
    let k := ⌊x / (√19 / 2)⌋
    exists k
    apply And.intro
    . by_contra abs
      rw [not_le] at abs
      have lb : x ≥ (x / (√19 / 2)) * (√19 / 2) := by
        simp
      have lb : x ≥ ⌊x / (√19 / 2)⌋ * (√19 / 2) := by
        refine ge_trans lb ?_
        apply mul_le_mul_of_nonneg_right
        . exact Int.floor_le _
        . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
      have lb : x > k * (√19 / 2) - (√3 / 2) := add_lt_of_le_of_neg lb (neg_neg_of_pos (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two))
      apply not_in_strip
      exists k
      apply And.intro
      . conv_rhs at lb => rw [mul_div_assoc']
        exact lb
      . conv_rhs at abs => rw [mul_div_assoc']
        exact abs
    . by_contra abs
      rw [not_le] at abs
      have ub : x ≤ (x / (√19 / 2)) * (√19 / 2) := by simp
      have ub : x ≤ ⌈x/ (√19 / 2)⌉ * (√19 / 2) := by
        apply le_trans
        . exact ub
        . apply mul_le_mul_of_nonneg_right
          . exact Int.le_ceil _
          . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
      have ub : x < ⌈x / (√19 / 2)⌉ * (√19 / 2) + (√3 / 2) := lt_add_of_le_of_pos ub (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two)
      have ub : x < (k + 1) * (√19 / 2) + (√3 / 2) := by
        refine gt_of_ge_of_gt ?_ ub
        have diseq := Int.ceil_le_floor_add_one (x / (√19 / 2))
        rify at diseq
        simpa
      apply not_in_strip
      exists k + 1
      apply And.intro
      . rw [mul_div_assoc'] at abs
        norm_cast at abs
      . rw [←mul_div_assoc] at ub
        norm_cast at ub
  have in_strip' : ∃ k : ℤ, 2 * x ∈ Set.Icc (k * √19 / 2 - ((√19 - 2 * √3) / 2)) (k * √19 / 2 + ((√19 - 2 * √3) / 2)) := by
    have ⟨k, hk⟩ := in_strip
    exists 2 * k + 1
    rw [Set.mem_Icc] at hk
    conv_lhs at hk => rw [←mul_le_mul_iff_of_pos_left zero_lt_two]
    conv_rhs at hk => rw [←mul_le_mul_iff_of_pos_left zero_lt_two]
    ring_nf at hk
    norm_cast at hk
    push_cast
    ring_nf
    exact hk
  have in_strip'' : ∃ k : ℤ, 2 * x ∈ Set.Ioo (k * √19 / 2 - √3 / 2) (k * √19 / 2 + √3 / 2) := by
    apply in_strip'.imp
    intro k hk
    rw [Set.mem_Icc] at hk
    apply And.intro
    . apply gt_of_ge_of_gt hk.left (by simp)
    . apply lt_of_le_of_lt hk.right (by simp)
  exact in_strip''

lemma special_case_subcases {s : R} {n m : ℤ} :
  s.val / 2 ∉ R →
  s.val = ⟨n / 2, √19 * m / 2⟩ ∧ n ≡ m [ZMOD 2] →
  (
    (n ≡ 1 [ZMOD 2] ∧ m ≡ 1 [ZMOD 2]) ∨
    (n ≡ 0 [ZMOD 4] ∧ m ≡ 2 [ZMOD 4]) ∨
    (n ≡ 2 [ZMOD 4] ∧ m ≡ 0 [ZMOD 4])
  )
:= by
  intro not_int_r eq
  rw [or_iff_not_imp_left]
  intro not_odd
  have eq' : m ≡ 1 [ZMOD 2] ↔ n ≡ 1 [ZMOD 2] := by
    apply Iff.intro
    . exact λ h => Int.ModEq.trans eq.right h
    . exact λ h => Int.ModEq.trans eq.right.symm h
  simp only [eq', and_self] at not_odd
  have n_even : n ≡ 0 [ZMOD 2] := (Int.emod_two_eq_zero_or_one n).resolve_right not_odd
  have m_even : m ≡ 0 [ZMOD 2] := Int.ModEq.trans eq.right.symm n_even

  apply (even_zero_or_two_mod_four n_even).elim
  all_goals apply (even_zero_or_two_mod_four m_even).elim
  case left.right =>
    intro hm hn
    exact Or.inl ⟨hn, hm⟩
  case right.left =>
    intro hm hn
    exact Or.inr ⟨hn, hm⟩
  case left.left | right.right =>
    intro hm hn
    have : s.val / 2 ∈ R := by
      exists n / 2, m / 2
      rw [←div_by_k_exact_on_mult n two_ne_zero n_even]
      rw [←div_by_k_exact_on_mult m two_ne_zero m_even]
      apply And.intro
      . apply Complex.ext
        repeat simp [eq]; cancel_denoms
      . have rn : ∀ n : ℤ, n ≡ 0 [ZMOD 2] → (n / 2) * 2 = n := by
          intro n hn
          rify
          rw [←div_by_k_exact_on_mult n two_ne_zero hn]
          simp
        have abs : (n / 2) * 2 ≡ (m / 2) * 2 [ZMOD 4] := by
          rw [rn n n_even, rn m m_even]
          exact Int.ModEq.trans hn hm.symm
        exact Int.ModEq.cancel_right_div_gcd zero_lt_four abs
    contradiction

lemma special_case {u v : R} (s : ↑R) :
  u.val ≠ 0 →
  s * u + 2 * v = 0 →
  s.val / 2 ∉ R →
  ∃ s t, dh_rel_on_r 0 (s * u + t * v) ∧ dh_rel_on_r (s * u + t * v) u
:= by
  intro nzero_c eq not_in_r
  have ⟨n, m, h⟩ := s.property
  let t' : R := by
    apply Subtype.mk ⟨(-n / 2), (√19 * m / 2)⟩
    exists -n, m
    simp only [Int.cast_neg, true_and]
    refine Int.ModEq.trans ?_ h.right
    apply Int.modEq_iff_add_fac.mpr
    exists n
    ring
  let s'' := -⌊(t'.val * v.val / u).re⌋
  let s' := (s'' : R)
  have eq' : v.val / u = -s / 2 := by
    field_simp
    rw [eq_neg_iff_add_eq_zero, add_comm]
    conv in v.val * 2 =>
      rw [←one_add_one_eq_two, ←Subring.coe_one R_subring, ←Subring.coe_add R_subring, one_add_one_eq_two, mul_comm]
    rw [←Subring.coe_mul R_subring, ←Subring.coe_mul R_subring, ←Subring.coe_add R_subring]
    norm_cast
  have eq₀ : s'.val.re = s'' := rfl
  have eq₁ : s'.val.im = 0 := rfl
  have eq₂ : (t' * v.val / u).im = 0 := by
    rw [mul_div_assoc, eq']
    simp only [Complex.mul_im, Complex.div_ofNat_im, Complex.neg_im, Complex.div_ofNat_re, Complex.neg_re]
    rw [(congr_arg Complex.re h.left : s.val.re = n / 2)]
    rw [(congr_arg Complex.im h.left : s.val.im = √19 * m / 2)]
    rw [(rfl : t'.val.re = -n / 2)]
    rw [(rfl : t'.val.im = (√19 * m / 2))]
    ring_nf
  exists s', t'
  apply And.intro
  . rw [dh_rel_on_r]
    have is_zero : Complex.normSq (0 : R) = 0 := by
      simp [Subring.coe_zero R_subring]
    rw [is_zero, Complex.normSq_pos, ne_eq]
    have th : (s'.val * u + t' * v) / u ≠ 0 := by
      rw [add_div, mul_div_assoc, div_self nzero_c, mul_one, ne_eq]
      apply ne_of_apply_ne Complex.re
      simp only [Complex.add_re, Complex.zero_re, ne_eq]
      have ne_zero_of_ne_zero_fract : ∀ a : ℝ, a = 0 → Int.fract a = 0 := λ a => λ ha => by simp [ha]
      apply not_imp_not.mpr (ne_zero_of_ne_zero_fract ((s'.val + (t'.val * v / u)).re))
      simp only [Complex.add_re, eq₀, Int.fract_int_add s'', mul_div_assoc, eq', h.left, t']
      simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.neg_re, Complex.div_ofNat_im, Complex.neg_im]
      ring_nf
      simp only [one_div, Nat.ofNat_nonneg, Real.sq_sqrt]
      rw [←right_distrib, ←div_eq_mul_inv]
      norm_cast
      apply fract_not_zero_of_mod_not_zero_q
      . exact Int.sign_eq_one_iff_pos.mp rfl
      . rcases special_case_subcases not_in_r h with ⟨odd, modd⟩ | ⟨zeron, twom⟩ | ⟨twon, zerom⟩
        . have eq1 := odd_one_mod_eight odd
          have eq2 := odd_one_mod_eight modd
          intro abs'
          have abs : n ^ 2 + 19 * m ^ 2 ≡ 1 + 19 [ZMOD 8] := by
            apply Int.ModEq.add
            . exact eq1
            . exact Int.ModEq.mul_left 19 eq2
          have := Int.ModEq.trans abs.symm abs'
          contradiction
        . intro abs'
          have abs : n ^ 2 + 19 * m ^ 2 ≡ 0 + 76 [ZMOD 8] := by
            apply Int.ModEq.add
            . exact sq_zero_mod_four_zero_mod_eight zeron
            . exact Int.ModEq.mul_left 19 (sq_two_mod_four_four_mod_eight twom)
          have := Int.ModEq.trans abs.symm abs'
          contradiction
        . intro abs'
          have abs : n ^ 2 + 19 * m ^ 2 ≡ 4 + 0 [ZMOD 8] := by
            apply Int.ModEq.add
            . exact sq_two_mod_four_four_mod_eight twon
            . exact Int.ModEq.mul_left 19 (sq_zero_mod_four_zero_mod_eight zerom)
          have := Int.ModEq.trans abs.symm abs'
          contradiction
    exact (div_ne_zero_iff.mp th).left
  . rw [dh_rel_on_r]
    have eq2 : Complex.normSq u = Complex.normSq u * 1 := by simp
    rw [←norm_frac s' t' u v nzero_c]
    conv_rhs => rw [eq2]
    refine mul_lt_mul_of_pos_left ?_ (by simpa)
    rw [Complex.normSq]
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re, Complex.add_im]
    simp only [eq₀, eq₁, eq₂, add_zero, mul_zero, s'']
    rw [(by simp : (1 : ℝ) = 1 * 1)]
    push_cast
    rw [neg_add_eq_sub]
    apply mul_lt_mul_of_nonneg
    repeat
      rw [sub_lt_comm]
      exact Int.sub_one_lt_floor (t' * v.val / u).re
    repeat
      exact sub_nonneg_of_le (Int.floor_le _)

theorem dh_rel_on_r_linear_comb {u v : R} : (u ≠ 0) → ¬(u ∣ v) → ∃ s t : R, dh_rel_on_r 0 (s * u + t * v) ∧ dh_rel_on_r (s * u + t * v) u := by
  intro nzero ndiv
  have nzero_c : (u : ℂ) ≠ 0 := by
    rwa [←Subring.coe_zero R_subring, Subtype.coe_ne_coe]
  cases em (∃ k : ℤ, (v.val / u.val).im ∈ Set.Ioo (k * √19 / 2 - √3 / 2) (k * √19 / 2 + √3 / 2)) with
  | inl in_strip =>
    have ⟨k, hk⟩ := in_strip
    have ⟨h, hh⟩ := real_part (v.val / u).re k
    have eq : v.val = 1 * v.val := by simp
    rw [eq] at hh
    rw [eq] at hk
    have ⟨s, hs⟩ := in_strip_low_distance 1 nzero_c hh hk
    exists s, 1
    refine And.intro ?_ hs
    simp only [dh_rel_on_r, Subring.coe_zero R_subring, map_zero, one_mul, Complex.normSq_pos, ne_eq]
    intro abs
    rw [←Subring.coe_zero R_subring, SetCoe.ext_iff] at abs
    apply ndiv
    exists -s
    rw [←mul_neg_one, ←mul_assoc, mul_neg_one]
    apply eq_neg_of_add_eq_zero_left
    rwa [add_comm, mul_comm]
  | inr not_in_strip =>
    have in_strip'' : ∃ k : ℤ, (2 * v.val / u).im ∈ Set.Ioo (k * √19 / 2 - √3 / 2) (k * √19 / 2 + √3 / 2) := by
      have := twice_in_strip not_in_strip
      rw [mul_div_assoc, Complex.mul_im]
      simpa
    have ⟨k, hk⟩ := in_strip''
    have ⟨h, hh⟩ := real_part (2 * v.val / u).re k
    have ⟨s, hs⟩ := in_strip_low_distance 2 nzero_c hh hk
    cases em (s * u + 2 * v ≠ 0 ∨ (s : ℂ) / 2 ∈ R) with
    | inl normal =>
      exists s, 2
      refine And.intro ?_ hs
      rw [dh_rel_on_r]
      have is_zero : Complex.normSq (0 : R) = 0 := by
        simp [Subring.coe_zero R_subring]
      cases em (s * u + 2 * v = 0) with
      | inl eq =>
        have in_r := normal.resolve_left (not_ne_iff.mpr eq)
        simp only [is_zero, Complex.normSq_pos, ne_eq]
        by_contra abs
        apply ndiv
        have eq := congr_arg Subtype.val (eq_neg_of_add_eq_zero_left eq)
        have eq := congr_arg (· / (-2 : ℂ)) eq
        have r : (-(2 * v)).val = -2 * v.val := by
          rw [neg_eq_neg_one_mul, ←mul_assoc, neg_one_mul]
          rfl
        simp only [r, neg_mul, neg_div_neg_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀] at eq
        let s' : R := -(Subtype.mk ((s : ℂ) / 2) in_r)
        exists s'
        ext
        calc
          _ = (s * u).val / -2 := eq.symm
          _ = (s.val * u.val) / -2 := rfl
          _ = u.val * -(s.val / 2) := by ring
          _ = (u * s').val := by rfl
      | inr neq =>
        have := Subtype.coe_ne_coe.mpr neq
        simpa [is_zero]
    | inr special =>
      rw [not_or, not_ne_iff] at special
      exact special_case s nzero_c special.left special.right

instance R_dh_domain : DedekindHasseDomain R where
  r := dh_rel_on_r
  r_wellFounded := dh_rel_on_r_well_founded
  linear_comb := dh_rel_on_r_linear_comb
