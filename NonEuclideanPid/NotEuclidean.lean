import NonEuclideanPid.RingConstruction
import Mathlib.SetTheory.Cardinal.Basic

set_option maxHeartbeats 0

@[simp]
def small : Set R :=
  λ x => x = 0 ∨ ∃ x' : R, x * x' = 1

def is_universal_side_divisor (u : R) :=
  u ∉ small ∧ ∀ x : R, ∃ q r : R, x = u * q + r ∧ r ∈ small

theorem euclidean_domain_has_usd [ed : EuclideanDomain R] (ext : ed.toCommRing = R_commring) : smallᶜ.Nonempty → ∃ u : R, is_universal_side_divisor u := by
  intro has_not_small
  have min_not_small := WellFounded.has_min (ed.r_wellFounded) smallᶜ has_not_small
  apply min_not_small.imp
  intro m hm
  refine And.intro hm.left ?_
  intro v
  apply Exists.intro (ed.quotient v m)
  apply Exists.intro (ed.remainder v m)
  apply And.intro
  . rw [←ext]
    exact (ed.quotient_mul_add_remainder_eq v m).symm
  . have m_not_zero := (not_or.mp (Set.mem_def.mp hm.left)).left
    have alt := by
      refine imp_not_comm.mp (hm.right (ed.remainder v m)) (ed.remainder_lt v ?_)
      rwa [ext]
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
        . have lt : (1 : ℝ) < (19 / 4) := by
            apply (one_lt_div zero_lt_four).mpr
            norm_cast
          exact lt
        . rw [Eq.symm (AddZeroClass.zero_add (19 / 4))]
          apply add_le_add
          . simp [sq_nonneg]
          . simp only [zero_add, Nat.ofNat_pos, div_pos_iff_of_pos_left, le_mul_iff_one_le_left, one_le_sq_iff_one_le_abs]
            norm_cast
            exact Int.one_le_abs abs
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
    . intro eq
      simp [eq, Subring.coe_one R_subring]
    . intro eq
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
  intro h
  exact λ x => h (congrArg Complex.re x)

lemma ne_of_im_ne (a b : ℂ) : a.im ≠ b.im → a ≠ b := by
  intro h
  exact λ x => h (congrArg Complex.im x)

theorem not_all_small : smallᶜ.Nonempty := by
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

lemma usd_equivalent {u : R} :
(∀ x : R, ∃ q r : R, x = u * q + r ∧ r ∈ small) ↔ (∀ x : R, ∃ q r : R, x = u * q + r ∧ (r = 0 ∨ r = 1 ∨ r = -1))
:= by
  apply forall_congr'
  intro x
  apply exists₂_congr
  intro q r
  rw [Set.mem_def, small, invertible_iff_norm_one, norm_one_iff_one_or_minus_one]

lemma small_norm {u : R} : u = 0 ∨ u = 1 ∨ u = -1 → ‖u.val‖ ≤ 1 := by
  intro h
  cases h with
  | inl zero =>
    simp [zero, Subring.coe_zero R_subring]
  | inr nonzero =>
    cases nonzero with
    | inl one =>
      simp [one, Subring.coe_one R_subring]
    | inr mone =>
      simp [mone, Subring.coe_neg R_subring, Subring.coe_one R_subring]

lemma less_four_is_zero_one_two_three_four {n : ℤ} : |n| ≤ 4 → (|n| = 0 ∨ |n| = 1 ∨ |n| = 2 ∨ |n| = 3 ∨ |n| = 4) := by
  intro
  by_contra abs
  simp only [abs_eq_zero, not_or] at abs
  have : 4 < |n| := by
    rw [←Int.natCast_natAbs]
    rw [←Int.natCast_natAbs] at abs
    norm_cast
    norm_cast at abs
    refine Nat.lt_of_le_of_ne ?_ (Ne.symm abs.right.right.right.right)
    refine Nat.lt_of_le_of_ne ?_ (Ne.symm abs.right.right.right.left)
    refine Nat.lt_of_le_of_ne ?_ (Ne.symm abs.right.right.left)
    refine Nat.lt_of_le_of_ne ?_ (Ne.symm abs.right.left)
    refine Nat.lt_of_le_of_ne ?_ (Ne.symm (Int.natAbs_ne_zero.mpr abs.left))
    exact Nat.zero_le n.natAbs
  linarith

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
  cases abs_v with
  | inl zero =>
    rw [abs_eq_zero] at zero
    rw [zero] at hm
    simp only [Int.cast_zero, zero_div, Int.ModEq.refl, and_true] at hm
    apply Or.inl
    ext
    rwa [Subring.coe_zero R_subring]
  | inr other =>
    cases other with
    | inl one =>
      have one : n = 1 ∨ n = -1 := abs_eq_abs.mp one
      have one_mod : n ≡ 1 [ZMOD 2] := by
        apply one.elim
        repeat
          intro h
          exact congr_fun (congr_arg HMod.hMod h) 2
      have := Int.ModEq.trans hm.right.symm one_mod
      contradiction
    | inr other =>
      cases other with
      | inl two =>
        have two : n = 2 ∨ n = -2 := abs_eq_abs.mp two
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
      | inr other =>
        cases other with
        | inl three =>
          have three : n = 3 ∨ n = -3 := abs_eq_abs.mp three
          have one_mod : n ≡ 1 [ZMOD 2] := by
            apply three.elim
            repeat
              intro h
              exact congr_fun (congr_arg HMod.hMod h) 2
          have := Int.ModEq.trans hm.right.symm one_mod
          contradiction
        | inr four =>
          have four : n = 4 ∨ n = -4 := abs_eq_abs.mp four
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
  have h := x.property
  cases h with
  | inl val =>
    repeat (simp only [val, norm_5_pp, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
    linarith
  | inr h =>
    cases h with
    | inl val =>
      repeat (simp only [val, norm_5_pm, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
      linarith
    | inr h =>
      cases h with
      | inl val =>
        repeat (simp only [val, norm_5_mp, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
        linarith
      | inr h =>
        cases h with
        | inl val =>
          repeat (simp only [val, norm_5_mm, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
          linarith
        | inr h =>
          cases h with
          | inl val =>
            repeat (simp only [val, norm_7_pp, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
            linarith
          | inr h =>
            cases h with
            | inl val =>
              repeat (simp only [val, norm_7_pm, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
              linarith
            | inr h =>
              cases h with
              | inl val =>
                repeat (simp only [val, norm_7_mp, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
                linarith
              | inr h =>
                cases h with
                | inl val =>
                  repeat (simp only [val, norm_7_mm, one_div, Complex.normSq_mk, ge_iff_le, Nat.ofNat_nonneg, Real.sq_sqrt]; ring_nf)
                  linarith
                | inr h =>
                  cases h with
                  | inl val =>
                    repeat (simp only [val, norm_9_m, Complex.normSq_mk, mul_neg, neg_mul, neg_neg, mul_zero, add_zero, ge_iff_le, le_refl]; ring_nf)
                    linarith
                  | inr val =>
                    rw [val]
                    repeat (simp only [norm_9_p, Complex.normSq_mk, mul_neg, neg_mul, neg_neg, mul_zero, add_zero, ge_iff_le, le_refl]; ring_nf)
                    linarith

@[simp]
lemma norm_0_1_card : Nat.card norm_0_1 = 3 := by
  rw [norm_0_1, Set.Nat.card_coe_set_eq]
  simp only [Set.mem_insert_iff, zero_ne_one, Set.mem_singleton_iff, zero_eq_neg, one_ne_zero, or_self, not_false_eq_true, Set.finite_singleton, Set.Finite.insert, Set.ncard_insert_of_not_mem, Nat.reduceEqDiff]
  apply Set.ncard_pair
  rw [←Subtype.coe_ne_coe, Subring.coe_neg R_subring, Subring.coe_one R_subring]
  norm_cast

lemma neg_neq {a : ℝ} : a ≠ 0 → a ≠ -a := by
  intro h
  apply (Iff.ne (div_left_inj' h)).mp
  field_simp
  norm_cast

lemma norm_5_9_card : Nat.card norm_5_9 = 10 := by
  have ne₀ : ¬√19 = -√19 ↔ True := Iff.intro (λ _ => trivial) (λ _ => neg_neq (Real.sqrt_ne_zero'.mpr Nat.ofNat_pos'))
  have ne₁ : (1 : ℝ) = -1 ↔ False := Iff.intro (by norm_cast) False.elim
  have ne₂ : (1 : ℝ) = -3 ↔ False := Iff.intro (by norm_cast) False.elim
  have ne₃ : (-1 : ℝ) = 3 ↔ False := Iff.intro (by norm_cast) False.elim
  have ne₄ : (3 : ℝ) = -3 ↔ False := Iff.intro (by norm_cast) False.elim

  rw [norm_5_9, Set.Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₀, ne₁, ne₂])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₁, ne₂])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₀, ne₃])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₃])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₀, ne₄])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₄])]
  rw [Set.ncard_insert_of_not_mem (by field_simp [ne₀])]
  rw [Set.ncard_insert_of_not_mem (by field_simp)]
  rw [Set.ncard_insert_of_not_mem (by field_simp [eq_comm, ne₄])]
  simp

instance : Finite norm_0_1 := by
  apply Nat.finite_of_card_ne_zero
  simp

theorem no_usd_in_R : ¬ ∃ u : R, is_universal_side_divisor u := by
  apply not_exists.mpr
  intro u
  rw [is_universal_side_divisor, not_and_or, or_iff_not_imp_left, not_not]
  intro not_small
  rw [Set.mem_def, small, invertible_iff_norm_one, norm_one_iff_one_or_minus_one] at not_small
  simp only [not_or] at not_small
  simp only [usd_equivalent, not_forall, not_exists, not_and_or, ←imp_iff_not_or]
  cases le_or_lt 10 (Complex.normSq u) with
  | inl more =>
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
            . field_simp [Complex.abs]
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
  | inr less =>
    cases le_or_lt 5 (Complex.normSq u) with
    | inl more_than_five =>
      by_contra abs
      rw [not_exists] at abs
      have f : ∃ f : norm_5_9 → norm_0_1 × norm_0_1, Function.Injective f := by
        conv at abs in (¬ ∀ _, _) => rw [not_forall]
        conv at abs in (¬ ∀ _, _) => rw [not_forall]
        conv at abs in (¬ (_ → _)) => rw [Classical.not_imp, not_not]
        let f : norm_5_9 → norm_0_1 × norm_0_1 := by
          intro v
          have ex := abs v
          let q := Classical.choose ex
          let hq := Classical.choose_spec ex
          let r := Classical.choose hq
          let hr := Classical.choose_spec hq

          simp only [q, r] at hr

          let r' : norm_0_1 := by
            apply Subtype.mk r
            rw [Set.mem_def]
            exact hr.right
          let q' : norm_0_1 := by
            apply Subtype.mk q
            rw [Set.mem_def]
            have eq : ({0, 1, -1} : Set R) q ↔ q = 0 ∨ q = 1 ∨ q = -1 := Eq.to_iff rfl
            rw [norm_0_1, eq]
            by_contra abs
            simp only [not_or] at abs
            have abs : Complex.normSq q ≥ 4 := by
              cases lt_or_ge (Complex.normSq q) 5 with
              | inl less =>
                have poss := norm_less_five less
                have poss := poss.resolve_left abs.left
                have poss := poss.resolve_left abs.right.left
                have poss := poss.resolve_left abs.right.right
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
          exact (q', r')
        apply Exists.intro f
        intro x y
        intro h
        have eq₀ := congr_arg Prod.fst h
        have eq₁ := congr_arg Prod.snd h
        have eq : ∀ z : norm_5_9, z = u * (f z).1 + (f z).2 := by
          intro z
          have ex := abs z
          let q := Classical.choose ex
          let hq := Classical.choose_spec ex
          let r := Classical.choose hq
          let hr := Classical.choose_spec hq
          simp only [Prod.fst, Prod.snd, q, r] at hr
          exact hr.left
        have eq₂ : x = u * (f x).1 + (f x).2 := eq x
        have eq₃ : y = u * (f y).1 + (f y).2 := eq y
        rw [←eq₀, ←eq₁] at eq₃
        rw [←eq₃] at eq₂
        rwa [Subtype.ext_iff]
      apply f.elim
      intro f inj
      have card_domain : Nat.card (norm_0_1 × norm_0_1) = 9 := by simp
      have con := Nat.card_le_card_of_injective f inj
      rw [card_domain, norm_5_9_card] at con
      linarith
    | inr four_or_less =>
      have poss := norm_less_five four_or_less
      have poss := poss.resolve_left not_small.left
      have poss := poss.resolve_left not_small.right.left
      have poss := poss.resolve_left not_small.right.right
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
                have poss := poss.resolve_left abs.left
                have poss := poss.resolve_left abs.right.left
                have poss := poss.resolve_left abs.right.right
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
