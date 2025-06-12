import NonEuclideanPid.RingConstruction
import Mathlib.SetTheory.Cardinal.Basic

set_option maxHeartbeats 0

@[simp]
def small (α : Type u) [CommRing α] : Set α :=
  λ x => x = 0 ∨ ∃ x' : α, x * x' = 1

def is_universal_side_divisor {α : Type u} [CommRing α] (u : α) :=
  u ∉ small α ∧ ∀ x : α, ∃ q r : α, x = u * q + r ∧ r ∈ small α

theorem euclidean_domain_has_usd {α : Type u} (δ : EuclideanDomain α) : (small α)ᶜ.Nonempty → ∃ u : α, is_universal_side_divisor u := by
  intro has_not_small
  have min_not_small := WellFounded.has_min (δ.r_wellFounded) (small α)ᶜ has_not_small
  apply min_not_small.imp
  intro m hm
  refine And.intro hm.left ?_
  intro v
  apply Exists.intro (δ.quotient v m)
  apply Exists.intro (δ.remainder v m)
  apply And.intro
  . exact (δ.quotient_mul_add_remainder_eq v m).symm
  . have m_not_zero := (not_or.mp (Set.mem_def.mp hm.left)).left
    have alt := imp_not_comm.mp (hm.right (δ.remainder v m)) (δ.remainder_lt v m_not_zero)
    simp only [Set.mem_compl_iff, not_not] at alt
    exact alt

lemma norm_one_iff_one_or_minus_one {x : R} : ‖x.val‖ = 1 ↔ (x = 1 ∨ x = -1) := by
  apply Iff.intro
  . have eq : ‖x.val‖ = √(Complex.normSq x.val) := rfl
    rw [eq, Real.sqrt_eq_one]
    apply x.property.elim
    intro n hn
    apply hn.elim
    intro m hm
    rw [hm.left, Complex.normSq_mk]
    ring_nf
    simp only [one_div, Nat.ofNat_nonneg, Real.sq_sqrt]
    ring_nf
    intro h
    have m_zero : m = 0 := by
      by_contra abs
      have : n ^ 2 * ((1 : ℝ) / 4) + m ^ 2 * (19 / 4) > 1 := by
        apply lt_of_lt_of_le
        . have lt : (1 : ℝ) < (19 / 4) := by linarith
          exact lt
        . rw [Eq.symm (AddZeroClass.zero_add (19 / 4))]
          apply add_le_add
          . simp [sq_nonneg]
          . have := Int.one_le_abs abs
            simp only [zero_add, Nat.ofNat_pos, div_pos_iff_of_pos_left, le_mul_iff_one_le_left, one_le_sq_iff_one_le_abs]
            norm_cast
      linarith
    rw [m_zero] at h
    rw [m_zero] at hm
    simp only [one_div, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h
    apply (Int.modEq_iff_dvd.mp hm.right).elim
    intro k hk
    rw [zero_sub] at hk
    rify at hk
    rw [←neg_pow_two, hk] at h
    ring_nf at h
    simp only [sq_eq_one_iff, Int.cast_eq_one] at h
    rify at h
    simp only [Int.cast_zero, mul_zero, zero_div] at hm
    rw [←neg_neg n] at hm
    push_cast at hm
    rw [hk] at hm
    ring_nf at hm
    cases h with
    | inl one =>
      apply Or.inr
      rw [one] at hm
      simp [Subtype.ext_iff, hm.left, Subring.coe_neg R_subring, Subring.coe_one R_subring, Complex.ext_iff]
    | inr mone =>
      apply Or.inl
      rw [mone] at hm
      simp [Subtype.ext_iff, hm.left, Subring.coe_one R_subring, Complex.ext_iff]
  . intro h
    apply h.elim
    repeat
      intro eq
      simp [eq, Subring.coe_neg R_subring, Subring.coe_one R_subring]

lemma invertible_iff_norm_one {x : R} : (∃ x' : R, x * x' = 1) ↔ ‖x.val‖ = 1 := by
  apply Iff.intro
  . intro h
    apply h.elim
    intro x' hx'
    have hx' : (x * x').val = 1 := by rw [hx']; trivial
    have norm_eq := congr_arg Complex.normSq hx'
    rw [Subring.coe_mul R_subring, Complex.normSq_mul] at norm_eq
    apply (sq_norm_is_integer_on_R x).elim
    intro n hn
    apply (sq_norm_is_integer_on_R x').elim
    intro m hm
    rw [hn, hm, map_one] at norm_eq
    norm_cast at norm_eq
    have eq : ‖x.val‖ = √(Complex.normSq x.val) := rfl
    rw [eq, hn]
    apply Real.sqrt_eq_one.mpr
    norm_cast
    exact (mul_eq_one.mp norm_eq).left
  . rw [norm_one_iff_one_or_minus_one]
    intro h
    apply h.elim
    repeat
      intro eq
      apply Exists.intro x
      simp [eq]

lemma ne_of_re_ne (a b : ℂ) : a.re ≠ b.re → a ≠ b := by
  intro h x
  exact h (congrArg Complex.re x)

lemma ne_of_im_ne (a b : ℂ) : a.im ≠ b.im → a ≠ b := by
  intro h x
  exact h (congrArg Complex.im x)

theorem not_all_small : (small R)ᶜ.Nonempty := by
  apply Exists.intro 2
  rw [Set.mem_compl_iff, Set.mem_def, small, not_or]
  apply And.intro
  . apply Subtype.coe_ne_coe.mp
    have eq : (2 : R) = (⟨2, 0⟩ : ℂ) := rfl
    rw [eq, Subring.coe_zero R_subring]
    apply ne_of_re_ne
    simp
  . rw [invertible_iff_norm_one, norm_one_iff_one_or_minus_one, not_or]
    apply And.intro
    . apply Subtype.coe_ne_coe.mp
      apply ne_of_re_ne ↑2 ↑1
      norm_cast
    . apply Subtype.coe_ne_coe.mp
      apply ne_of_re_ne ↑2 ↑(-1)
      norm_cast
      
lemma small_norm {u : R} : u = 0 ∨ u = 1 ∨ u = -1 → ‖u.val‖ ≤ 1 := by
  intro h
  rcases h with h₁ | h₁ | h₁
  repeat
    simp_all [h₁, Subring.coe_zero R_subring, Subring.coe_neg R_subring, Subring.coe_one R_subring]

lemma less_four_is_zero_one_two_three_four {n : ℤ} : |n| ≤ 4 → (|n| = 0 ∨ |n| = 1 ∨ |n| = 2 ∨ |n| = 3 ∨ |n| = 4) := by
  have := abs_nonneg n
  omega

lemma norm_less_five {u : R} : Complex.normSq u < 5 → u = 0 ∨ u = 1 ∨ u = -1 ∨ u = 2 ∨ u = -2 := by
  intro h
  apply u.property.elim
  intro n hn
  apply hn.elim
  intro m hm
  rw [hm.left, Complex.normSq_mk] at h
  ring_nf at h
  simp only [one_div, Nat.ofNat_nonneg, Real.sq_sqrt] at h
  ring_nf at h
  have m_zero : m = 0 := by
    by_contra abs
    cases le_or_lt 2 |m| with
    | inl more =>
      have : (n : ℝ) ^ 2 * (1 / 4) + (m : ℝ) ^ 2 * (19 / 4) > 5 := calc
        _ ≥ (0 : ℝ) + (4 * (19 / 4)) := by
          apply add_le_add
          . simp [sq_nonneg]
          . simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_right]
            rw [←sq_abs]
            apply (Real.sqrt_le_left (abs_nonneg _)).mp
            rw [(Real.sqrt_eq_iff_mul_self_eq zero_le_four zero_le_two).mpr (by ring)]
            norm_cast
        _ > 5 := by
          field_simp
          norm_cast
      linarith
    | inr less =>
      have n_ne_zero : n ≠ 0 := by
        by_contra abs'
        rw [abs'] at hm
        have abs_m_one := Or.resolve_left (Int.abs_le_one_iff.mp (Int.lt_add_one_iff.mp less)) abs
        have one_mod : m ≡ 1 [ZMOD 2] := by
          apply Or.elim abs_m_one
          repeat exact λ h => congr_fun (congr_arg HMod.hMod h) 2
        have := Int.ModEq.trans hm.right one_mod
        contradiction
      have : (n : ℝ) ^ 2 * (1 / 4) + (m : ℝ) ^ 2 * (19 / 4) ≥ 5 := calc
        _ ≥ ((1 : ℝ) / 4) + (19 / 4) := by
          apply add_le_add
          . have th := Int.one_le_abs n_ne_zero
            rify at th
            simpa
          . have th := Int.one_le_abs abs
            rify at th
            simpa
        _ = _ := by ring
      linarith
  rw [m_zero] at h
  rw [m_zero] at hm
  simp only [Int.cast_zero, mul_zero, zero_div] at hm
  simp only [one_div, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h
  ring_nf at h
  have abs_n_le_two : |n| ≤ 4 := by
    by_contra abs
    rw [not_le] at abs
    have : (n : ℝ) ^ 2 * (1 / 4) ≥ 5 := calc
      _ ≥ 20 * ((1 : ℝ) / 4) := by
        apply mul_le_mul
        . rw [←sq_abs]
          apply (Real.sqrt_le_left (abs_nonneg _)).mp
          calc
            _ ≥ (5 : ℝ) := by norm_cast
            _ ≥ _ := by
              apply Real.sqrt_le_iff.mpr
              apply And.intro
              . exact Nat.ofNat_nonneg' 5
              . ring_nf
                norm_cast
        . rfl
        . exact one_div_nonneg.mpr zero_le_four
        . exact sq_nonneg _
      _ = _ := by ring
    linarith
  have abs_v := less_four_is_zero_one_two_three_four abs_n_le_two
  rcases abs_v with zero | one | two | three | four
  . rw [abs_eq_zero] at zero
    rw [zero] at hm
    simp only [Int.cast_zero, zero_div, Int.ModEq.refl, and_true] at hm
    apply Or.inl
    ext
    rwa [Subring.coe_zero R_subring]
  . have one : n = 1 ∨ n = -1 := abs_eq_abs.mp one
    have one_mod : n ≡ 1 [ZMOD 2] := by
      apply one.elim
      repeat
        intro h
        exact congr_fun (congr_arg HMod.hMod h) 2
    have := Int.ModEq.trans hm.right.symm one_mod
    contradiction
  . have two : n = 2 ∨ n = -2 := abs_eq_abs.mp two
    cases two with
    | inl two =>
      rw [two] at hm
      simp only [Int.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self] at hm
      apply Or.inr; apply Or.inl
      rw [Subtype.ext_iff, Subring.coe_one R_subring]
      exact hm.left
    | inr mtwo =>
      rw [mtwo] at hm
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, neg_div_self] at hm
      apply Or.inr; apply Or.inr; apply Or.inl
      rw [Subtype.ext_iff, Subring.coe_neg R_subring, Subring.coe_one R_subring, hm.left]
      apply Complex.ext
      repeat simp
  . have one : n = 3 ∨ n = -3 := abs_eq_abs.mp three
    have one_mod : n ≡ 1 [ZMOD 2] := by
      apply one.elim
      repeat
        intro h
        exact congr_fun (congr_arg HMod.hMod h) 2
    have := Int.ModEq.trans hm.right.symm one_mod
    contradiction
  . have four : n = 4 ∨ n = -4 := abs_eq_abs.mp four
    cases four with
    | inl four =>
      rw [four, Int.cast_ofNat] at hm
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      rw [←one_add_one_eq_two, Subtype.ext_iff, Subring.coe_add R_subring, Subring.coe_one R_subring, hm.left]
      apply Complex.ext
      . ring_nf
        rfl
      . simp
    | inr mfour =>
      rw [mfour] at hm
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at hm
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      rw [←one_add_one_eq_two, Subtype.ext_iff, Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring, hm.left]
      apply Complex.ext
      . ring_nf
        rfl
      . simp

@[simp] noncomputable def norm_5_pp : R := Subtype.mk ⟨1 / 2, √19 / 2⟩ (Exists.intro 1 (Exists.intro 1 (by simp)))
@[simp] noncomputable def norm_5_mp : R := Subtype.mk ⟨-1 / 2, √19 / 2⟩ (Exists.intro (-1) (Exists.intro 1 (by simp; rfl)))
@[simp] noncomputable def norm_5_pm : R := Subtype.mk ⟨1 / 2, -√19 / 2⟩ (Exists.intro 1 (Exists.intro (-1) (by simp; rfl)))
@[simp] noncomputable def norm_5_mm : R := Subtype.mk ⟨-1 / 2, -√19 / 2⟩ (Exists.intro (-1) (Exists.intro (-1) (by simp)))

@[simp] noncomputable def norm_7_pp : R := Subtype.mk ⟨3 / 2, √19 / 2⟩ (Exists.intro 3 (Exists.intro 1 (by simp; rfl)))
@[simp] noncomputable def norm_7_mp : R := Subtype.mk ⟨-3 / 2, √19 / 2⟩ (Exists.intro (-3) (Exists.intro 1 (by simp; rfl)))
@[simp] noncomputable def norm_7_pm : R := Subtype.mk ⟨3 / 2, -√19 / 2⟩ (Exists.intro 3 (Exists.intro (-1) (by simp; rfl)))
@[simp] noncomputable def norm_7_mm : R := Subtype.mk ⟨-3 / 2, -√19 / 2⟩ (Exists.intro (-3) (Exists.intro (-1) (by simp; rfl)))

@[simp] noncomputable def norm_9_p : R := Subtype.mk ⟨3, 0⟩ (Exists.intro 6 (Exists.intro 0 (by ring_nf; simp ; rfl)))
@[simp] noncomputable def norm_9_m : R := Subtype.mk ⟨-3, 0⟩ (Exists.intro (-6) (Exists.intro 0 (by ring_nf; simp ; rfl)))

def norm_0_1 : Set R :=
  { 0, 1, -1 }

def norm_5_9 : Set R :=
  {
    norm_5_pp, norm_5_pm, norm_5_mp, norm_5_mm,
    norm_7_pp, norm_7_pm, norm_7_mp, norm_7_mm,
    norm_9_m, norm_9_p
  }

lemma norm_5_9_norm {x : norm_5_9} : Complex.normSq x ≤ 9 := by
  rcases x.property with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁
  all_goals (rw [h₁]; field_simp; linarith)

lemma neg_neq {a : ℝ} : a ≠ 0 → a ≠ -a := by
  intro h
  apply (Iff.ne (div_left_inj' h)).mp
  field_simp
  norm_cast

@[simp]
lemma norm_0_1_card : Nat.card norm_0_1 = 3 := by
  rw [norm_0_1, Set.Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_not_mem (by simp), Set.ncard_pair]
  rw [←Subtype.coe_ne_coe, Subring.coe_neg R_subring, Subring.coe_one R_subring]
  norm_cast

lemma norm_5_9_card : Nat.card norm_5_9 = 10 := by
  have ne₀ : √19 ≠ -√19 := neg_neq (Real.sqrt_ne_zero'.mpr Nat.ofNat_pos')
  rw [norm_5_9, Set.Nat.card_coe_set_eq]
  repeat rw [Set.ncard_insert_of_not_mem (by field_simp [ne₀] <;> norm_cast)]
  simp

instance : Finite norm_0_1 := by
  simp [Nat.finite_of_card_ne_zero]

lemma usd_equivalent {u : R} :
(∀ x : R, ∃ q r : R, x = u * q + r ∧ r ∈ small R) ↔ (∀ x : R, ∃ q r : R, x = u * q + r ∧ (r = 0 ∨ r = 1 ∨ r = -1))
:= by
  apply forall_congr'
  intro x
  apply exists₂_congr
  intro q r
  rw [Set.mem_def, small, invertible_iff_norm_one, norm_one_iff_one_or_minus_one]

lemma not_usd {u : R} :
¬ is_universal_side_divisor u ↔ u ∉ small R → ∃ x, ∀ (x_1 x_2 : ↑R), x = u * x_1 + x_2 → ¬(x_2 = 0 ∨ x_2 = 1 ∨ x_2 = -1) := by
  conv_lhs =>
    rw [is_universal_side_divisor, not_and_or, or_iff_not_imp_left, not_not]
    simp only [usd_equivalent, not_forall, not_exists, not_and_or, ←imp_iff_not_or]

lemma norm_ge_10_not_usd {u : R} : Complex.normSq u ≥ 10 → ¬ is_universal_side_divisor u := by
  intro more
  rw [not_usd]
  intro not_small
  apply Exists.intro 2
  intro q r h₁ h₂
  have h₁' : (2 : R).val - r.val = u.val * q.val := by
    rw [sub_eq_add_neg]
    rw [←Subring.coe_mul R_subring, ←Subring.coe_neg R_subring, ←Subring.coe_add R_subring]
    rw [←Subtype.ext_iff]
    ring_nf
    exact sub_eq_iff_eq_add.mpr h₁
  cases em (q = 0) with
  | inl zero =>
    rw [zero, mul_zero, zero_add] at h₁
    rw [←h₁, ←one_add_one_eq_two] at h₂
    simp only [Subtype.ext_iff] at h₂
    rw [Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring, Subring.coe_zero R_subring] at h₂
    ring_nf at h₂
    simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or] at h₂
    have : (2 : ℂ) ≠ (-1 : ℂ) := by norm_cast
    contradiction
  | inr nonzero =>
    have : (3 : ℝ) > 3 := calc
      3 = 2 + 1 := by norm_cast
      _ = Complex.abs (2 : R).val + 1 := by
        have eq : Complex.abs (2 : R).val = 2 := Complex.abs_ofNat 2
        rw [eq]
      _ ≥ Complex.abs (2 : R).val + Complex.abs (-r) := by
        apply (add_le_add_iff_left _).mpr
        rw [map_neg_eq_map]
        exact small_norm h₂
      _ ≥ Complex.abs ((2 : R) + (-r)) := norm_add_le (2 : ℂ) ((-r) : ℂ)
      _ = Complex.abs ((2 : R) - r) := by ring_nf
      _ = Complex.abs (u * q) := congr_arg Complex.abs h₁'
      _ = Complex.abs u * Complex.abs q := by simp
      _ ≥ √10 * 1 := by
        refine mul_le_mul ?_ ?_ zero_le_one ?_
        . apply Real.sqrt_le_iff.mpr
          apply And.intro
          . exact AbsoluteValue.nonneg Complex.abs ↑u
          . field_simp [Complex.sq_abs]
            exact more
        . apply (sq_norm_is_integer_on_R q).elim
          intro n hn
          rw [Complex.abs]
          simp only [AbsoluteValue.coe_mk, MulHom.coe_mk, Real.one_le_sqrt]
          rw [hn]
          norm_cast
          by_contra abs
          rw [Nat.eq_zero_of_not_pos abs] at hn
          simp only [CharP.cast_eq_zero, map_eq_zero] at hn
          rw [←Subring.coe_zero R_subring] at hn
          rw [Subtype.ext_iff] at nonzero
          contradiction
        . exact AbsoluteValue.nonneg Complex.abs ↑u
      _ > _ := by
        simp only [mul_one, gt_iff_lt]
        apply Real.lt_sqrt_of_sq_lt
        norm_cast
    linarith

lemma norm_ge_5_not_usd {u : R} : Complex.normSq u ≥ 5 → Complex.normSq u < 10 → ¬ is_universal_side_divisor u := by
  intro more_than_five less
  by_contra abs
  rw [is_universal_side_divisor] at abs
  have ex_div : ∀ x : norm_5_9, ∃ q r : norm_0_1, x = u * q + r := by
    intro v
    apply (abs.right v).elim
    intro q hq
    apply hq.elim
    intro r hr
    rw [Set.mem_def, small, invertible_iff_norm_one, norm_one_iff_one_or_minus_one] at hr
    have small_r : r ∈ norm_0_1 := by
      simp [norm_0_1, Set.mem_insert, Set.mem_singleton]
      exact hr.right
    have small_q : q ∈ norm_0_1 := by
      rw [Set.mem_def]
      have eq : ({0, 1, -1} : Set R) q ↔ q = 0 ∨ q = 1 ∨ q = -1 := Eq.to_iff rfl
      rw [norm_0_1, eq]
      by_contra abs
      simp only [not_or] at abs
      have abs : Complex.normSq q ≥ 4 := by
        cases lt_or_ge (Complex.normSq q) 5 with
        | inl less =>
          have poss := norm_less_five less
          simp only [abs, false_or] at poss
          apply ge_of_eq
          cases poss with
          | inl two =>
            rw [two, ←one_add_one_eq_two, Subring.coe_add R_subring, Subring.coe_one R_subring, Complex.normSq]
            simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero, mul_zero]
            ring
          | inr mtwo =>
            rw [mtwo, ←one_add_one_eq_two, Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring, Complex.normSq]
            simp only [neg_add_rev, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.add_re,
              Complex.neg_re, Complex.one_re, Complex.add_im, Complex.neg_im, Complex.one_im,
              neg_zero, add_zero, mul_zero]
            ring
        | inr more =>
          exact ge_trans more (by linarith)
      have : (4 : ℝ) > 4 := calc
        _ = 3 + 1 := by ring
        _ ≥ Complex.abs v + 1 := by
          refine add_le_add ?_ (by rfl)
          rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk]
          refine (Real.sqrt_le_left zero_le_three).mpr ?_
          ring_nf
          exact norm_5_9_norm
        _ ≥ Complex.abs v + Complex.abs (-r) := by
          apply add_le_add (by rfl)
          rw [map_neg_eq_map]
          exact small_norm hr.right
        _ ≥ Complex.abs (v + (-r)) := norm_add_le v.val.val (-r)
        _ = Complex.abs (v - r) := by ring_nf
        _ = Complex.abs (u * q) := by
          apply congr_arg Complex.abs
          rw [sub_eq_iff_eq_add, ←Subring.coe_mul R_subring, ←Subring.coe_add R_subring]
          apply Subtype.ext_iff.mp
          exact hr.left
        _ = Complex.abs u * Complex.abs q := by simp
        _ ≥ √5 * √4 := by
          apply mul_le_mul
          . rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk]
            exact Real.sqrt_le_sqrt more_than_five
          . rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk]
            exact Real.sqrt_le_sqrt abs
          . exact Real.sqrt_nonneg _
          . exact AbsoluteValue.nonneg Complex.abs _
        _ > √4 * √4 := by
          apply mul_lt_mul
          . simp only [Nat.ofNat_nonneg, Real.sqrt_lt_sqrt_iff]
            norm_cast
          . rfl
          . exact Real.sqrt_pos_of_pos zero_lt_four
          . exact Real.sqrt_nonneg _
        _ = _ := Real.mul_self_sqrt zero_le_four
      linarith
    apply Exists.intro (Subtype.mk q small_q)
    apply Exists.intro (Subtype.mk r small_r)
    exact hr.left

  have f : ∃ f : norm_5_9 → norm_0_1 × norm_0_1, Function.Injective f := by
    conv at ex_div in (∃ _, _) => rw [←Prod.exists']
    apply (Classical.skolem.mp ex_div).imp
    intro f hf
    rw [Function.Injective]
    intro x y h
    ext
    rw [hf x, hf y, h]
  apply f.elim
  intro f inj
  have card_domain : Nat.card (norm_0_1 × norm_0_1) = 9 := by simp
  have con := Nat.card_le_card_of_injective f inj
  rw [card_domain, norm_5_9_card] at con
  linarith

lemma norm_lt_5_not_usd {u : R} : Complex.normSq u < 5 → ¬ is_universal_side_divisor u := by
  intro four_or_less
  rw [not_usd]
  intro not_small
  rw [Set.mem_def, small, invertible_iff_norm_one, norm_one_iff_one_or_minus_one, not_or, not_or] at not_small
  have poss := norm_less_five four_or_less
  simp only [not_small, false_or] at poss
  let val : R := by
    apply Subtype.mk ⟨1 / 2, √19 / 2⟩
    apply Exists.intro 1
    apply Exists.intro 1
    simp
  apply Exists.intro val
  intro q r h₁ h₂
  have h₁' : val.val - r.val = u.val * q.val := by
    rw [sub_eq_add_neg]
    rw [←Subring.coe_mul R_subring, ←Subring.coe_neg R_subring, ←Subring.coe_add R_subring]
    rw [←Subtype.ext_iff]
    ring_nf
    exact sub_eq_iff_eq_add.mpr h₁
  have q_poss : q = 0 ∨ q = 1 ∨ q = -1 := by
    by_contra abs
    simp only [not_or] at abs
    have : (4 : ℝ) > 4 := calc
      4 = 3 + 1 := by ring
      _ > Complex.abs val + 1 := by
        apply (add_lt_add_iff_right 1).mpr
        have eq : val = (⟨1 / 2, √19 / 2⟩ : ℂ) := rfl
        rw [eq, Complex.abs]
        field_simp
        ring_nf
        field_simp
        apply (div_lt_iff₀' zero_lt_two).mpr
        ring_nf
        apply (Real.sqrt_lt' Nat.ofNat_pos).mpr
        ring_nf
        norm_cast
      _ ≥ Complex.abs val + Complex.abs (-r) := by
        apply (add_le_add_iff_left (Complex.abs val)).mpr
        rw [map_neg_eq_map]
        exact small_norm h₂
      _ ≥ Complex.abs (val + (-r)) := norm_add_le (val : ℂ) ((-r) : ℂ)
      _ ≥ Complex.abs (val - r) := by ring_nf; rfl
      _ = Complex.abs (u * q) := congr_arg Complex.abs h₁'
      _ = Complex.abs u * Complex.abs q := by simp
      _ ≥ 2 * 2 := by
        refine mul_le_mul ?_ ?_ zero_le_two ?_
        . apply poss.elim
          . intro h
            conv_rhs => rw [h, ←one_add_one_eq_two, Subring.coe_add R_subring, Subring.coe_one R_subring]
            ring_nf
            simp
          . intro h
            conv_rhs => rw [h, ←one_add_one_eq_two, Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring]
            ring_nf
            simp
        . cases lt_or_le (Complex.normSq q) 5 with
          | inl less =>
            have poss := norm_less_five less
            simp only [abs, false_or] at poss
            . apply poss.elim
              . intro h
                conv_rhs => rw [h, ←one_add_one_eq_two, Subring.coe_add R_subring, Subring.coe_one R_subring]
                ring_nf
                simp
              . intro h
                conv_rhs => rw [h, ←one_add_one_eq_two, Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring]
                ring_nf
                simp
          | inr more =>
            rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk]
            apply Real.le_sqrt_of_sq_le
            ring_nf
            exact ge_trans more (by norm_cast)
        . exact AbsoluteValue.nonneg Complex.abs ↑u
      _ = 4 := by ring
    linarith
  have : val.val = u * q + r := Subtype.ext_iff.mp h₁
  have : val.val ≠ u * q + r := by
    apply ne_of_im_ne
    have val_eq : val = (⟨1 / 2, √19 / 2⟩ : ℂ) := rfl
    have u_eq : u.val.im = 0 := by
      apply poss.elim
      . intro h
        simp [h, ←one_add_one_eq_two, Subring.coe_add R_subring, Subring.coe_one R_subring]
      . intro h
        simp [h, ←one_add_one_eq_two, Subring.coe_neg R_subring, Subring.coe_add R_subring, Subring.coe_one R_subring]
    have eq : ∀ x : R, x = 0 ∨ x = 1 ∨ x = -1 → x.val.im = 0 := by
      intro x hx
      apply hx.elim
      . intro hx
        simp [hx, Subring.coe_zero R_subring]
      . intro hx
        apply hx.elim
        . intro hx
          simp [hx, Subring.coe_one R_subring]
        . intro hx
          simp [hx, Subring.coe_neg R_subring, Subring.coe_one R_subring]
    simp [Complex.add_im, Complex.mul_im, val_eq, u_eq, eq q q_poss, eq r h₂]
  contradiction

theorem no_usd_in_R : ¬ ∃ u : R, is_universal_side_divisor u := by
  apply not_exists.mpr
  intro u
  cases le_or_lt 10 (Complex.normSq u) with
  | inl more => exact norm_ge_10_not_usd more
  | inr less => cases le_or_lt 5 (Complex.normSq u) with
  | inl five => exact norm_ge_5_not_usd five less
  | inr four => exact norm_lt_5_not_usd four
