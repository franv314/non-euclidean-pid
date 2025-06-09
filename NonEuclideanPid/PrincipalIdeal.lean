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
      cases em (↑↑γ ∣ v) with
      | inl div =>
        rw [Submodule.mem_span_singleton]
        apply div.imp
        intro κ hκ
        rw [smul_eq_mul, mul_comm]
        exact hκ.symm
      | inr abs =>
          have lin := δ.linear_comb hγ.left.left abs
          apply lin.elim
          intro s hs
          apply hs.elim
          intro t ht
          let lin_comb : non_zero := by
            apply Subtype.mk (s * ↑↑γ + t * v)
            apply And.intro
            . rw [ne_eq]
              by_contra abs
              apply (WellFounded.wellFounded_iff_no_descending_seq.mp δ.r_wellFounded).false
              apply Subtype.mk (λ _ => 0)
              intro
              conv in (occs := 2) 0 => rw [←abs]
              exact ht.left
            . have := ideal.smul_mem' s hγ.left.right
              have := ideal.smul_mem' t in_ideal
              apply ideal.add_mem'
              repeat simpa
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
    rw [Ideal.submodule_span_eq]
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
        simpa [abs]
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
  apply abs.elim
  intro f hf
  let g : ℕ → ℕ := λ n => ⌊Complex.normSq (f n)⌋₊
  have abs : ∀ n : ℕ, (g (n + 1)) < (g n) := by
    intro n
    have eq : ∀ n : ℕ, g n = Complex.normSq (f n) := by
      intro x
      apply (sq_norm_is_integer_on_R (f x)).elim
      intro n hn
      rw [hn, Nat.cast_inj]
      calc
        ⌊Complex.normSq (f x)⌋₊ = ⌊(n : ℝ)⌋₊ := by rw [hn]
        _ = n := by simp
    rify
    rw [eq n, eq (n + 1)]
    exact hf n
  apply (WellFounded.wellFounded_iff_no_descending_seq.mp (Nat.lt_wfRel.wf)).false
  exact Subtype.mk g abs

lemma in_strip_low_distance {h k : ℤ} {u v : R} (t : R) :
  ((u : ℂ) ≠ 0) →
  (h ≡ k [ZMOD 2] ∧ |(t * v.val / u).re - ↑h / 2| ≤ 1 / 2) →
  (↑k * √19 / 2 - √3 / 2 < (t * v.val / u).im ∧ (t * v.val / u).im < ↑k * √19 / 2 + √3 / 2) →
  ∃ s, dh_rel_on_r (s * u + t * v) u
:= by
  intro nzero_c hh hk
  let s : R := by
    apply Subtype.mk (Complex.mk (-h / 2) (-k / 2 * √19))
    apply Exists.intro (-h)
    apply Exists.intro (-k)
    apply And.intro
    . simp only [Int.cast_neg, mul_neg, Complex.mk.injEq, true_and]
      ring_nf
    . have := hh.left
      simpa
  apply Exists.intro s
  rw [dh_rel_on_r]
  have eq1 : Complex.normSq u * Complex.normSq (s + t * v / u) = Complex.normSq (s * u + t * v : R) := calc
    _ = Complex.normSq (u * (s + t * v / u)) := by rw [Complex.normSq_mul]
    _ = _ := by
      have eq : u * (s + t * v.val / u) = (s * u + t * v : R) := calc
        u * (s + t *v.val / u) = s * u + t * v.val * u / u := by ring
        _ = s * u + t * v.val * (u.val * u.val⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
        _ = s * u + t * v.val := by rw [Field.mul_inv_cancel u.val nzero_c]; simp
        _ = (s * u + t * v : R) := rfl
      rw [←eq]
  have eq2 : Complex.normSq u = Complex.normSq u * 1 := by simp
  rw [←eq1]
  conv_rhs => rw [eq2]
  apply mul_lt_mul_of_pos_left
  . rw [Complex.normSq]
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re, Complex.add_im]
    have eq1 : s.val.re = -h / 2 := rfl
    have eq2 : s.val.im = -k / 2 * √19 := rfl
    rw [eq1, eq2]

    let re_sq := ((t * v.val / u).re - ↑h / 2)
    let im_sq := (-↑k / 2 * √19 + (t * v.val / u).im)
    have eq3 : re_sq ^ 2 = (-↑h / 2 + (t * v.val / u).re) * (-↑h / 2 + (t * v.val / u).re) := by ring
    have eq3' : re_sq = ((t * v.val / u).re - ↑h / 2)  := by ring
    have eq4 : im_sq ^ 2 = (-↑k / 2 * √19 + (t * v.val / u).im) * (-↑k / 2 * √19 + (t * v.val / u).im) := by ring
    have eq4' : im_sq = (-↑k / 2 * √19 + (t * v.val / u).im) := by ring
    have eq5 : (1 / 2) ^ 2 + (√3 / 2) ^ 2 = 1 := by
      simp only [one_div, inv_pow]
      ring_nf
      simp only [one_div, Nat.ofNat_nonneg, Real.sq_sqrt]
      ring_nf
    rw [←eq3, ←eq4, ←eq5]

    apply add_lt_add_of_le_of_lt
    . have diseq : √(re_sq ^ 2) ≤ (1 / 2) := by
        rw [Real.sqrt_sq_eq_abs, eq3']
        exact hh.right
      exact (Real.sqrt_le_iff.mp diseq).right
    . have diseq : √(im_sq ^ 2) < (√3 / 2) := by
        rw [Real.sqrt_sq_eq_abs, eq4']
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
          conv_rhs => rw [add_comm, div_eq_mul_inv, ←mul_assoc]
          exact hk.right
      exact Real.lt_sq_of_sqrt_lt diseq
  . simpa

lemma close_int (x : ℝ) : ∃ l : ℤ, |x - l| ≤ 1 / 2 := by
    let l := ⌊x⌋
    cases em (x - l ≤ 1 / 2) with
    | inl hl =>
      apply Exists.intro l
      rw [abs_le]
      apply And.intro
      . simp only [one_div, neg_le_sub_iff_le_add]
        apply le_add_of_le_of_nonneg
        . exact Int.floor_le x
        . exact inv_nonneg_of_nonneg zero_le_two
      . simp only [one_div, tsub_le_iff_right] at hl
        simpa
    | inr hl =>
      simp only [one_div, tsub_le_iff_right, not_le] at hl
      apply Exists.intro (l + 1)
      rw [abs_le]
      apply And.intro
      . simp only [one_div, Int.cast_add, Int.cast_one, neg_le_sub_iff_le_add]
        apply le_of_lt
        have th := add_lt_add_left hl (1 / 2)
        ring_nf at th
        simp at th
        conv_lhs at th => rw [add_comm]
        conv_rhs at th => rw [add_comm]
        exact th
      . simp only [Int.cast_add, Int.cast_one, one_div, tsub_le_iff_right]
        ring_nf
        by_contra abs
        rw [not_le] at abs
        have := calc
          l + 1 ≥ (⌈x⌉ : ℝ) := by
            have diseq := Int.ceil_le_floor_add_one x
            rify at diseq
            exact diseq
          _ ≥ x := Int.le_ceil x
          _ > (3 / 2) + ↑l := abs
        linarith

lemma real_part (x : ℝ) : ∀ k : ℤ, ∃ l : ℤ, l ≡ k [ZMOD 2] ∧ |x - l / 2| ≤ 1 / 2 := by
  intro k
  have th : ∀ x : ℝ, ∃ l : ℤ, l ≡ 0 [ZMOD 2] ∧ |x - l / 2| ≤ 1 / 2 := by
    intro x
    apply (close_int x).elim
    intro l hl
    apply Exists.intro (2 * l)
    apply And.intro
    . apply Int.modEq_iff_dvd.mpr
      apply Exists.intro (-l)
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
    apply (th (x - 1 / 2)).elim
    intro k hk
    apply Exists.intro (k + 1)
    apply And.intro
    . exact Int.ModEq.trans (Int.ModEq.add_right 1 hk.left) one.symm
    . rify
      ring_nf
      have tg := hk.right
      ring_nf at tg
      exact tg

lemma fract_not_zero_of_mod_not_zero (a b : ℤ) : b > 0 → ¬ a ≡ 0 [ZMOD b] → ¬Int.fract ((a : ℝ) / b) = 0 := by
  intro pos neq
  have pos_r : (b : ℝ) > 0 := by norm_cast
  have nzero_r : (b : ℝ) ≠ 0 := by
    apply ne_of_gt
    norm_cast
  rw [←Int.euclideanDomain.quotient_mul_add_remainder_eq a b]
  push_cast
  have eq₀ : Int.euclideanDomain.quotient = (· / ·) := rfl
  have eq₁ : Int.euclideanDomain.remainder = (· % ·) := rfl
  rw [eq₀, eq₁, ←ne_eq, add_div, mul_comm, div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, div_self nzero_r, mul_one, Int.fract_int_add, ne_eq]
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

lemma fract_not_zero_of_mod_not_zero_q (a b : ℤ) : b > 0 → ¬ a ≡ 0 [ZMOD b] → ¬Int.fract (Rat.divInt a b) = 0 := by
  intro pos neq
  rify
  exact fract_not_zero_of_mod_not_zero a b pos neq

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
  apply (Int.modEq_iff_dvd.mp h.symm).elim
  intro k hk
  rw [sub_zero] at hk
  rw [hk]
  apply Int.modEq_iff_dvd.mpr
  apply Exists.intro (-2 * k ^ 2)
  ring_nf

lemma sq_two_mod_four_four_mod_eight {n : ℤ} : n ≡ 2 [ZMOD 4] → n ^ 2 ≡ 4 [ZMOD 8] := by
  intro h
  apply (Int.modEq_iff_dvd.mp h.symm).elim
  intro k hk
  rw [Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hk)))]
  apply Int.modEq_iff_dvd.mpr
  apply Exists.intro (-2 * k ^ 2 - 2 * k)
  ring_nf

theorem dh_rel_on_r_linear_comb {u v : R} : (u ≠ 0) → ¬(u ∣ v) → ∃ s t : R, dh_rel_on_r 0 (s * u + t * v) ∧ dh_rel_on_r (s * u + t * v) u := by
  intro nzero ndiv
  have nzero_c : (u : ℂ) ≠ 0 := by
    intro abs
    apply nzero
    have : u = 0 := Subtype.ext abs
    contradiction
  cases em (∃ k : ℤ, k * √19 / 2 - √3 / 2 < (v.val / u.val).im ∧ (v.val / u.val).im < k * √19 / 2 + √3 / 2) with
  | inl in_strip =>
    apply in_strip.elim
    intro k hk
    apply (real_part (v.val / u).re k).elim
    intro h hh
    have eq : v.val = 1 * v.val := by simp
    rw [eq] at hh
    rw [eq] at hk
    have lt := in_strip_low_distance 1 nzero_c hh hk
    apply lt.elim
    intro s hs
    apply Exists.intro s
    apply Exists.intro 1
    refine And.intro ?_ hs
    simp only [dh_rel_on_r, one_mul]
    have is_zero : Complex.normSq (0 : R) = 0 := calc
      _ = Complex.normSq (0 : ℂ) := rfl
      _ = 0 := by simp
    rw [is_zero]
    simp only [Complex.normSq_pos, ne_eq]
    by_contra abs
    apply ndiv
    apply Exists.intro (-s)
    symm
    calc
      u * -s = u * -s + 0 := by simp
      _ = u * -s + (s * u + v) := by rw [(Subtype.ext abs : s * u + v = 0)]
      _ = _ := by ring
  | inr not_in_strip =>
    have in_strip : ∃ k : ℤ, k * (√19 / 2) + √3 / 2 ≤ (v.val / u).im ∧ (v.val / u).im ≤ (k + 1) * (√19 / 2) - √3 / 2 := by
      let k := ⌊(v.val / u).im / (√19 / 2)⌋
      apply Exists.intro k
      apply And.intro
      . by_contra abs
        rw [not_le] at abs
        have lb : (v.val / u).im ≥ ((v.val / u).im / (√19 / 2)) * (√19 / 2) := by
          simp
        have lb : (v.val / u).im ≥ ⌊(v.val / u).im / (√19 / 2)⌋ * (√19 / 2) := by
          refine ge_trans lb ?_
          apply mul_le_mul_of_nonneg_right
          . exact Int.floor_le _
          . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
        have lb : (v.val / u).im > k * (√19 / 2) - (√3 / 2) := add_lt_of_le_of_neg lb (neg_neg_of_pos (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two))
        apply not_in_strip
        apply Exists.intro k
        apply And.intro
        . conv_rhs at lb => rw [div_eq_mul_inv, ←mul_assoc]
          exact lb
        . conv_rhs at abs => rw [div_eq_mul_inv, ←mul_assoc]
          exact abs
      . by_contra abs
        rw [not_le] at abs
        have ub : (v.val / u).im ≤ ((v.val / u).im / (√19 / 2)) * (√19 / 2) := by simp
        have ub : (v.val / u).im ≤ ⌈(v.val / u).im / (√19 / 2)⌉ * (√19 / 2) := by
          apply le_trans
          . exact ub
          . apply mul_le_mul_of_nonneg_right
            . exact Int.le_ceil _
            . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
        have ub : (v.val / u).im < ⌈(v.val / u).im / (√19 / 2)⌉ * (√19 / 2) + (√3 / 2) := lt_add_of_le_of_pos ub (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two)
        have ub : (v.val / u).im < (k + 1) * (√19 / 2) + (√3 / 2) := by
          refine gt_of_ge_of_gt ?_ ub
          have diseq := Int.ceil_le_floor_add_one ((v.val / u).im / (√19 / 2))
          rify at diseq
          simpa
        apply not_in_strip
        apply Exists.intro (k + 1)
        rify
        apply And.intro
        . conv_lhs at abs => rw [div_eq_mul_inv]
          rwa [←mul_assoc, ←div_eq_mul_inv] at abs
        . conv_rhs at ub => rw [div_eq_mul_inv]
          rwa [←mul_assoc, ←div_eq_mul_inv] at ub
    have in_strip' : ∃ k : ℤ, k * √19 / 2 - ((√19 - 2 * √3) / 2) ≤ (2 * v.val / u).im ∧ (2 * v.val / u).im ≤ k * √19 / 2 + ((√19 - 2 * √3) / 2) := by
      apply in_strip.elim
      intro k hk
      apply Exists.intro (2 * k + 1)
      conv_lhs at hk => rw [←mul_le_mul_iff_of_pos_left zero_lt_two]
      conv_rhs at hk => rw [←mul_le_mul_iff_of_pos_left zero_lt_two]
      ring_nf at hk
      rw [←Complex.im_mul_ofReal] at hk
      norm_cast at hk
      push_cast
      ring_nf
      exact hk
    have strip_diseq : (√19 - 2 * √3) / 2 < √3 / 2 := by
      refine div_lt_div_of_pos_right ?_ zero_lt_two
      rw [sub_lt_iff_lt_add]
      refine (Real.sqrt_lt' ?_).mpr ?_
      . ring_nf
        exact mul_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_three
      . ring_nf
        simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
        norm_cast
    have in_strip'' : ∃ k : ℤ, k * √19 / 2 - √3 / 2 < (2 * v.val / u).im ∧ (2 * v.val / u).im < k * √19 / 2 + √3 / 2 := by
      apply in_strip'.imp
      intro k hk
      apply And.intro
      . apply gt_of_ge_of_gt hk.left (by simpa)
      . apply lt_of_le_of_lt hk.right (by simpa)
    apply in_strip''.elim
    intro k hk
    apply (real_part (2 * v.val / u).re k).elim
    intro h hh
    have lt := in_strip_low_distance 2 nzero_c hh hk
    apply lt.elim
    intro s hs
    cases em (s * u + 2 * v = 0) with
    | inl eq =>
      cases em ((s : ℂ) / 2 ∈ R) with
      | inl in_r =>
        apply Exists.intro s
        apply Exists.intro 2
        refine And.intro ?_ hs
        rw [dh_rel_on_r]
        have is_zero : Complex.normSq (0 : R) = 0 := calc
          _ = Complex.normSq (0 : ℂ) := rfl
          _ = 0 := by simp
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
        apply Exists.intro s'
        ext
        calc
          _ = (s * u).val / -2 := eq.symm
          _ = (s.val * u.val) / -2 := rfl
          _ = u.val * -(s.val / 2) := by ring
          _ = (u * s').val := by rfl
      | inr not_in_r =>
        apply s.property.elim
        intro n hn
        apply hn.elim
        intro m hm
        let t' : R := by
          apply Subtype.mk ⟨(-n / 2), (√19 * m / 2)⟩
          apply Exists.intro (-n)
          apply Exists.intro (m)
          simp only [Int.cast_neg, true_and]
          calc
            _ ≡ n [ZMOD 2] := by
              apply Int.modEq_iff_add_fac.mpr
              apply Exists.intro n
              ring
            n ≡ m [ZMOD 2] := hm.right
        let s'' := -⌊(t'.val * v.val / u).re⌋
        let s' := (s'' : R)
        have t'_eq : t'.val = ⟨(-n / 2), (√19 * m / 2)⟩ := rfl
        have eq' : v.val / u = -s / 2 := by
          field_simp
          rw [eq_neg_iff_add_eq_zero, add_comm]
          apply Eq.symm
          calc
            (0 : R).val = (s * u + 2 * v).val := by rw[←eq.symm]
            _ = (s * u + v * 2).val := by ring_nf
            _ = s.val * u.val + v.val * 2 := rfl
        have eq₀ : s'.val.re = s'' := rfl
        have eq₁ : s'.val.im = 0 := rfl
        have eq₂ : (t' * v.val / u).im = 0 := by
          rw [div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, eq']
          simp only [Complex.mul_im, Complex.div_ofNat_im, Complex.neg_im, Complex.div_ofNat_re, Complex.neg_re]
          rw [(congr_arg Complex.re hm.left : s.val.re = n / 2)]
          rw [(congr_arg Complex.im hm.left : s.val.im = √19 * m / 2)]
          rw [(rfl : t'.val.re = -n / 2)]
          rw [(rfl : t'.val.im = (√19 * m / 2))]
          ring_nf
        have eq₃ : s'' = -⌊(t'.val * v.val / u).re⌋ := rfl
        apply Exists.intro s'
        apply Exists.intro t'
        apply And.intro
        . rw [dh_rel_on_r]
          have is_zero : Complex.normSq (0 : R) = 0 := calc
            _ = Complex.normSq (0 : ℂ) := rfl
            _ = 0 := by simp
          rw [is_zero, Complex.normSq_pos, ne_eq]
          have eq : (s' * u + t' * v).val = (s'.val * u.val + t'.val * v.val) := rfl
          rw [eq]
          have th : (s'.val * u + t' * v) / u ≠ 0 := by
            rw [add_div, div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, div_self nzero_c, mul_one, ne_eq]
            apply ne_of_apply_ne Complex.re
            simp only [Complex.add_re, Complex.zero_re, ne_eq]
            have ne_zero_of_ne_zero_fract : ∀ a : ℝ, a = 0 → Int.fract a = 0 := λ a => λ ha => by rw[ha]; simp
            apply not_imp_not.mpr (ne_zero_of_ne_zero_fract ((s'.val + (t'.val * v / u)).re))
            rw [Complex.add_re, eq₀, Int.fract_int_add s'' _, div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, eq', hm.left, t'_eq]
            simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.neg_re, Complex.div_ofNat_im, Complex.neg_im]
            ring_nf
            simp only [one_div, Nat.ofNat_nonneg, Real.sq_sqrt]
            rw [←right_distrib, ←div_eq_mul_inv]
            norm_cast
            apply fract_not_zero_of_mod_not_zero_q (n ^ 2 + 19 * m ^ 2) 8
            . exact Int.sign_eq_one_iff_pos.mp rfl
            . cases Int.emod_two_eq_zero_or_one n with
              | inl even =>
                have e : n % 2 = 0 ↔ n ≡ 0 [ZMOD 2] := Eq.to_iff rfl
                rw [e] at even
                have meven := Int.ModEq.trans hm.right.symm even
                cases even_zero_or_two_mod_four even with
                | inl zeron =>
                  cases even_zero_or_two_mod_four meven with
                  | inl zerom =>
                    have : s.val / 2 ∈ R := by
                      apply Exists.intro (n / 2)
                      apply Exists.intro (m / 2)
                      apply And.intro
                      . rw [hm.left]
                        apply Complex.ext
                        . rw [Complex.div_ofNat_re, ←div_by_k_exact_on_mult n two_ne_zero even]
                          ring_nf
                        . rw [Complex.div_ofNat_im, ←div_by_k_exact_on_mult m two_ne_zero meven]
                          ring_nf
                      . have eq : (n / 2) * 2 ≡ (m / 2) * 2 [ZMOD 4] := by
                          have rn : (n / 2) * 2 = n := by
                            rify
                            rw [←div_by_k_exact_on_mult n two_ne_zero even]
                            simp
                          have rm : (m / 2) * 2 = m := by
                            rify
                            rw [←div_by_k_exact_on_mult m two_ne_zero meven]
                            simp
                          rw [rn, rm]
                          exact Int.ModEq.trans zeron zerom.symm
                        exact Int.ModEq.cancel_right_div_gcd (zero_lt_four) eq
                    contradiction
                  | inr twom =>
                    by_contra abs'
                    have abs : n ^ 2 + 19 * m ^ 2 ≡ 0 + 76 [ZMOD 8] := by
                      apply Int.ModEq.add
                      . exact sq_zero_mod_four_zero_mod_eight zeron
                      . have th : 19 * m ^ 2 ≡ 19 * 4 [ZMOD 8] := Int.ModEq.mul_left 19 (sq_two_mod_four_four_mod_eight twom)
                        simp only [Int.reduceMul] at th
                        exact th
                    rw [zero_add] at abs
                    have := Int.ModEq.trans abs.symm abs'
                    contradiction
                | inr twon =>
                  cases even_zero_or_two_mod_four meven with
                  | inl zerom =>
                    by_contra abs'
                    have abs : n ^ 2 + 19 * m ^ 2 ≡ 4 + 0 [ZMOD 8] := by
                      apply Int.ModEq.add
                      . exact sq_two_mod_four_four_mod_eight twon
                      . have th : 19 * m ^ 2 ≡ 19 * 0 [ZMOD 8] := Int.ModEq.mul_left 19 (sq_zero_mod_four_zero_mod_eight zerom)
                        rw [mul_zero] at th
                        exact th
                    rw [add_zero] at abs
                    have := Int.ModEq.trans abs.symm abs'
                    contradiction
                  | inr twom =>
                    have : s.val / 2 ∈ R := by
                      apply Exists.intro (n / 2)
                      apply Exists.intro (m / 2)
                      apply And.intro
                      . rw [hm.left]
                        apply Complex.ext
                        . rw [Complex.div_ofNat_re, ←div_by_k_exact_on_mult n two_ne_zero even]
                          ring_nf
                        . rw [Complex.div_ofNat_im, ←div_by_k_exact_on_mult m two_ne_zero meven]
                          ring_nf
                      . have eq : (n / 2) * 2 ≡ (m / 2) * 2 [ZMOD 4] := by
                          have rn : (n / 2) * 2 = n := by
                            rify
                            rw [←div_by_k_exact_on_mult n two_ne_zero even]
                            simp
                          have rm : (m / 2) * 2 = m := by
                            rify
                            rw [←div_by_k_exact_on_mult m two_ne_zero meven]
                            simp
                          rw [rn, rm]
                          exact Int.ModEq.trans twon twom.symm
                        exact Int.ModEq.cancel_right_div_gcd (zero_lt_four) eq
                    contradiction
              | inr odd =>
                have e : n % 2 = 1 ↔ n ≡ 1 [ZMOD 2] := Eq.to_iff rfl
                rw [e] at odd
                have modd := Int.ModEq.trans hm.right.symm odd
                have eq1 := odd_one_mod_eight odd
                have eq2 := odd_one_mod_eight modd
                by_contra abs'
                have abs : n ^ 2 + 19 * m ^ 2 ≡ 1 + 19 [ZMOD 8] := by
                  apply Int.ModEq.add
                  . exact eq1
                  . have th : 19 * m ^ 2 ≡ 19 * 1 [ZMOD 8] := Int.ModEq.mul_left 19 eq2
                    rw [mul_one] at th
                    exact th
                simp only [Int.reduceAdd] at abs
                have := Int.ModEq.trans abs.symm abs'
                contradiction
          exact (div_ne_zero_iff.mp th).left
        . rw [dh_rel_on_r]
          have eq1 : Complex.normSq u * Complex.normSq (s' + t' * v / u) = Complex.normSq (s' * u + t' * v : R) := calc
            _ = Complex.normSq (u * (s' + t' * v / u)) := by rw [Complex.normSq_mul]
            _ = _ := by
              have eq : u * (s' + t' * v.val / u) = (s' * u + t' * v : R) := calc
                u * (s' + t' *v.val / u) = s' * u + t' * v.val * u / u := by ring
                _ = s' * u + t' * v.val * (u.val * u.val⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
                _ = s' * u + t' * v.val := by rw [Field.mul_inv_cancel u.val nzero_c]; simp
                _ = (s' * u + t' * v : R) := rfl
              rw [←eq]
          have eq2 : Complex.normSq u = Complex.normSq u * 1 := by simp
          rw [←eq1]
          conv_rhs => rw [eq2]
          apply mul_lt_mul_of_pos_left
          . rw [Complex.normSq]
            simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re, Complex.add_im]
            rw [eq₀, eq₁, eq₂]
            simp only [add_zero, mul_zero]
            rw [((by simp) : (1 : ℝ) = 1 * 1)]
            rw [eq₃]
            push_cast
            rw [neg_add_eq_sub]
            apply mul_lt_mul'
            . apply le_of_lt
              rw [sub_lt_comm]
              exact Int.sub_one_lt_floor (t' * v.val / u).re
            . rw [sub_lt_comm]
              exact Int.sub_one_lt_floor (t' * v.val / u).re
            . exact sub_nonneg_of_le (Int.floor_le _)
            . exact zero_lt_one
          . simpa
    | inr neq =>
      apply Exists.intro s
      apply Exists.intro 2
      refine And.intro ?_ hs
      rw [dh_rel_on_r]
      have is_zero : Complex.normSq (0 : R) = 0 := calc
        _ = Complex.normSq (0 : ℂ) := rfl
        _ = 0 := by simp
      have := Subtype.coe_ne_coe.mpr neq
      simpa [is_zero]

instance R_dh_domain : DedekindHasseDomain R where
  r := dh_rel_on_r
  r_wellFounded := dh_rel_on_r_well_founded
  linear_comb := dh_rel_on_r_linear_comb
