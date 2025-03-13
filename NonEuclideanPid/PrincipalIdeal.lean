import NonEuclideanPid.RingConstruction

variable (α : Type u)

class DedekindHasseDomain extends CommRing α, IsDomain α where
  r : α → α → Prop
  r_wellFounded : WellFounded r
  linear_comb : ∀ u v: α, (u ≠ 0) → ¬(u ∣ v) → (∃ s t: α, r 0 (s * u + t * v) ∧ r (s * u + t * v) u)

theorem dedekind_hasse_domain_implies_pid [δ : DedekindHasseDomain α] : IsPrincipalIdealRing α := by
  apply IsPrincipalIdealRing.mk
  intro ideal
  apply Submodule.IsPrincipal.mk
  cases em (∃ x : α, x ≠ 0 ∧ ideal.carrier x) with
  | inl normal =>
    let non_zero : Set α := λ x => x ≠ 0 ∧ ideal.carrier x
    have min_not_small := by
      apply WellFounded.has_min (δ.r_wellFounded) non_zero
      exact normal
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
        simp
        rw [mul_comm]
        exact hκ.symm
      | inr abs =>
          have lin := δ.linear_comb _ _ hγ.left.left abs
          apply lin.elim
          intro s hs
          apply hs.elim
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

@[simp]
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
    . simp
      ring_nf
    . simp
      exact hh.left
  apply Exists.intro s
  simp
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
    simp
    have eq1 : s.val.re = -h / 2 := rfl
    have eq2 : s.val.im = -k / 2 * √19 := rfl
    rw [eq1, eq2]

    let re_sq := ((t * v.val / u).re - ↑h / 2)
    let im_sq := (-↑k / 2 * √19 + (t * v.val / u).im)
    have eq3 : re_sq ^ 2 = (-↑h / 2 + (t * v.val / u).re) * (-↑h / 2 + (t * v.val / u).re) := by ring
    have eq3' : re_sq = ((t * v.val / u).re - ↑h / 2)  := by ring
    have eq4 : im_sq ^ 2 = (-↑k / 2 * √19 + (t * v.val / u).im) * (-↑k / 2 * √19 + (t * v.val / u).im) := by ring
    have eq4' : im_sq = (-↑k / 2 * √19 + (t * v.val / u).im) := by ring
    have eq5 : (1 / 2) ^ 2 + (√3 / 2) ^ 2 = 1 := by repeat (simp; ring_nf)
    rw [←eq3, ←eq4, ←eq5]

    apply add_lt_add_of_le_of_lt
    . have diseq : √(re_sq ^ 2) ≤ (1 / 2) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [eq3']
        exact hh.right
      exact (Real.sqrt_le_iff.mp diseq).right
    . have diseq : √(im_sq ^ 2) < (√3 / 2) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [eq4']
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
        . rw [neg_eq_neg_one_mul, div_eq_mul_inv, mul_assoc, mul_assoc]
          rw [←neg_eq_neg_one_mul, neg_add_eq_sub, ←div_eq_inv_mul]
          apply sub_lt_iff_lt_add.mpr
          conv_rhs => rw [add_comm, div_eq_mul_inv, ←mul_assoc]
          exact hk.right
      exact Real.lt_sq_of_sqrt_lt diseq
  . simp
    assumption

lemma close_int (x : ℝ) : ∃ l : ℤ, |x - l| ≤ 1 / 2 := by
    let l := ⌊x⌋
    cases em (x - l ≤ 1 / 2) with
    | inl hl =>
      apply Exists.intro l
      rw [abs_le]
      apply And.intro
      . simp
        apply le_add_of_le_of_nonneg
        . exact Int.floor_le x
        . exact inv_nonneg_of_nonneg zero_le_two
      . simp
        simp at hl
        exact hl
    | inr hl =>
      simp at hl
      apply Exists.intro (l + 1)
      rw [abs_le]
      apply And.intro
      . simp
        apply le_of_lt
        have th := add_lt_add_left hl (1 / 2)
        ring_nf at th
        simp at th
        conv_lhs at th => rw [add_comm]
        conv_rhs at th => rw [add_comm]
        exact th
      . simp
        ring_nf
        by_contra abs
        simp at abs
        have p := calc
          l + 1 ≥ (⌈x⌉ : ℝ) := by
            have diseq := Int.ceil_le_floor_add_one x
            rify at diseq
            exact diseq
          _ ≥ x := Int.le_ceil x
          _ > (3 / 2) + ↑l := abs
          _ = ↑l + (3 / 2) := by rw [add_comm]
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
    . simp
      simp at hl
      exact hl
  cases Int.emod_two_eq_zero_or_one k with
  | inl zero =>
    apply (th x).imp
    intro k hk
    apply And.intro
    . calc
        k ≡ 0 [ZMOD 2] := hk.left
        _ ≡ _ [ZMOD 2] := zero.symm
    . exact hk.right
  | inr one =>
    apply (th (x - 1 / 2)).elim
    intro k hk
    apply Exists.intro (k + 1)
    apply And.intro
    . calc
        k + 1 ≡ 0 + 1 [ZMOD 2] := Int.ModEq.add_right 1 hk.left
        _ ≡ _ [ZMOD 2] := one.symm
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
  rw [eq₀, eq₁]
  simp
  rw [add_div, mul_comm, div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, div_self nzero_r]
  simp
  apply ne_of_gt
  apply Int.fract_pos.mpr
  have rhs_zero : ⌊((a % b) : ℝ) / b⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    apply And.intro
    . push_cast
      apply div_nonneg
      . norm_cast
        refine Int.emod_nonneg a (ne_of_gt pos)
      . exact le_of_lt pos_r
    . simp
      apply (div_lt_one pos_r).mpr
      norm_cast
      apply Int.emod_lt_of_pos a pos
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
  intro neq
  apply (Int.modEq_iff_dvd.mp neq.symm).elim
  intro k hk
  rw [Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hk)))]
  ring_nf
  rw [add_assoc, ←add_mul]
  have div : 2 ∣ (k + k ^ 2) := by
    cases Int.emod_two_eq_zero_or_one k with
    | inl even =>
      have e : k % 2 = 0 ↔ k ≡ 0 [ZMOD 2] := Eq.to_iff rfl
      rw [e] at even
      apply (Int.modEq_iff_dvd.mp even.symm).elim
      intro g hg
      simp at hg
      rw [hg]
      apply Exists.intro (g + 2 * g ^ 2)
      ring_nf
    | inr odd =>
      have e : k % 2 = 1 ↔ k ≡ 1 [ZMOD 2] := Eq.to_iff rfl
      rw [e] at odd
      apply (Int.modEq_iff_dvd.mp odd.symm).elim
      intro g hg
      have hg := Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hg)))
      rw [hg]
      apply Exists.intro (1 + 3 * g + 2 * g ^ 2)
      ring_nf
  apply div.elim
  intro g hg
  rw [hg]
  apply Int.modEq_iff_dvd.mpr
  apply Exists.intro (-g)
  ring_nf

lemma even_zero_or_two_mod_four {n : ℤ} : n ≡ 0 [ZMOD 2] → (n ≡ 0 [ZMOD 4] ∨ n ≡ 2 [ZMOD 4]) := by
  intro h
  apply (Int.modEq_iff_dvd.mp h.symm).elim
  intro k hk
  simp at hk
  rw [hk]
  cases Int.emod_two_eq_zero_or_one k with
  | inl even =>
    have e : k % 2 = 0 ↔ k ≡ 0 [ZMOD 2] := Eq.to_iff rfl
    rw [e] at even
    apply (Int.modEq_iff_dvd.mp even.symm).elim
    intro g hg
    simp at hg
    apply Or.inl
    apply Int.modEq_iff_dvd.mpr
    apply Exists.intro (-g)
    rw [hg]
    ring_nf
  | inr odd =>
    have e : k % 2 = 1 ↔ k ≡ 1 [ZMOD 2] := Eq.to_iff rfl
    rw [e] at odd
    apply (Int.modEq_iff_dvd.mp odd.symm).elim
    intro g hg
    have hg := Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hg)))
    apply Or.inr
    apply Int.modEq_iff_dvd.mpr
    apply Exists.intro (-g)
    rw [hg]
    ring_nf

lemma sq_zero_mod_four_zero_mod_eight {n : ℤ} : n ≡ 0 [ZMOD 4] → n ^ 2 ≡ 0 [ZMOD 8] := by
  intro h
  apply (Int.modEq_iff_dvd.mp h.symm).elim
  intro k hk
  simp at hk
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

theorem dh_rel_on_r_linear_comb (u v : R) : (u ≠ 0) → ¬(u ∣ v) → ∃ s t : R, dh_rel_on_r 0 (s * u + t * v) ∧ dh_rel_on_r (s * u + t * v) u := by
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
    simp
    have is_zero : Complex.normSq (0 : R) = 0 := calc
      _ = Complex.normSq (0 : ℂ) := rfl
      _ = 0 := by simp
    rw [is_zero]
    simp
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
        simp at abs
        have lb : (v.val / u).im ≥ ((v.val / u).im / (√19 / 2)) * (√19 / 2) := by
          simp
        have lb : (v.val / u).im ≥ ⌊(v.val / u).im / (√19 / 2)⌋ * (√19 / 2) := by
          apply ge_trans
          . exact lb
          . apply mul_le_mul_of_nonneg_right
            . exact Int.floor_le _
            . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
        have lb : (v.val / u).im > k * (√19 / 2) - (√3 / 2) := add_lt_of_le_of_neg lb (neg_neg_of_pos (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two))
        apply not_in_strip
        apply Exists.intro k
        apply And.intro
        . conv_rhs at lb => rw [div_eq_mul_inv]
          rw [←mul_assoc] at lb
          exact gt_iff_lt.mp lb
        . conv_rhs at abs => rw [div_eq_mul_inv]
          rw [←mul_assoc] at abs
          exact abs
      . by_contra abs
        simp at abs
        have ub : (v.val / u).im ≤ ((v.val / u).im / (√19 / 2)) * (√19 / 2) := by
          simp
        have ub : (v.val / u).im ≤ ⌈(v.val / u).im / (√19 / 2)⌉ * (√19 / 2) := by
          apply le_trans
          . exact ub
          . apply mul_le_mul_of_nonneg_right
            . exact Int.le_ceil _
            . exact div_nonneg (Real.sqrt_nonneg _) zero_le_two
        have ub : (v.val / u).im < ⌈(v.val / u).im / (√19 / 2)⌉ * (√19 / 2) + (√3 / 2) := lt_add_of_le_of_pos ub (div_pos (Real.sqrt_pos.mpr zero_lt_three) zero_lt_two)
        have ub : (v.val / u).im < (k + 1) * (√19 / 2) + (√3 / 2) := by
          refine gt_of_ge_of_gt ?_ ub
          simp
          have diseq := Int.ceil_le_floor_add_one ((v.val / u).im / (√19 / 2))
          rify at diseq
          exact diseq
        apply not_in_strip
        apply Exists.intro (k + 1)
        apply And.intro
        . rify
          conv_lhs at abs => rw [div_eq_mul_inv]
          rw [←mul_assoc, ←div_eq_mul_inv] at abs
          exact abs
        . rify
          conv_rhs at ub => rw [div_eq_mul_inv]
          rw [←mul_assoc, ←div_eq_mul_inv] at ub
          exact ub
    have in_strip' : ∃ k : ℤ, k * √19 + √3 ≤ (2 * v.val / u).im ∧ (2 * v.val / u).im ≤ (k + 1) * √19 - √3 := by
      apply in_strip.imp
      intro k hk
      apply And.intro
      . have th : (k * (√19 / 2) + √3 / 2) * 2 ≤ ((v.val / u).im) * 2 := by
          apply (mul_le_mul_iff_of_pos_right zero_lt_two).mpr
          exact hk.left
        ring_nf at th
        ring_nf
        rw [←Complex.im_mul_ofReal (v.val * u.val⁻¹) 2] at th
        exact th
      . have th : ((v.val / u).im) * 2 ≤ ((k + 1) * (√19 / 2) - √3 / 2) * 2 := by
          apply (mul_le_mul_iff_of_pos_right zero_lt_two).mpr
          exact hk.right
        ring_nf at th
        ring_nf
        rw [←Complex.im_mul_ofReal (v.val * u.val⁻¹) 2] at th
        exact th
    have in_strip'' : ∃ k : ℤ, k * √19 / 2 - ((√19 - 2 * √3) / 2) ≤ (2 * v.val / u).im ∧ (2 * v.val / u).im ≤ k * √19 / 2 + ((√19 - 2 * √3) / 2) := by
      apply in_strip'.elim
      intro k hk
      apply Exists.intro (2 * k + 1)
      apply And.intro
      . have hk := hk.left
        field_simp
        ring_nf
        ring_nf at hk
        exact hk
      . have hk := hk.right
        field_simp
        ring_nf
        ring_nf at hk
        exact hk
    have strip_diseq : (√19 - 2 * √3) / 2 < √3 / 2 := by
      refine div_lt_div₀ ?_ (by rfl) (Real.sqrt_nonneg 3) zero_lt_two
      apply sub_right_lt_of_lt_add
      rw [←abs_eq_self.mpr (Real.sqrt_nonneg 19)]
      rw [←abs_eq_self.mpr (add_nonneg (Real.sqrt_nonneg 3) (mul_nonneg zero_le_two (Real.sqrt_nonneg 3)))]
      apply sq_lt_sq.mp
      repeat (simp; ring_nf)
      have diseq := Nat.lt_of_sub_eq_succ (rfl : 27 - 19 = _)
      rify at diseq
      exact diseq
    have in_strip''' : ∃ k : ℤ, k * √19 / 2 - √3 / 2 < (2 * v.val / u).im ∧ (2 * v.val / u).im < k * √19 / 2 + √3 / 2 := by
      apply in_strip''.imp
      intro k hk
      apply And.intro
      . apply gt_of_ge_of_gt
        . exact hk.left
        . simp
          exact strip_diseq
      . apply lt_of_le_of_lt
        . exact hk.right
        . simp
          exact strip_diseq

    apply in_strip'''.elim
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
        simp
        have is_zero : Complex.normSq (0 : R) = 0 := calc
          _ = Complex.normSq (0 : ℂ) := rfl
          _ = 0 := by simp
        rw [is_zero]
        simp
        by_contra abs
        apply ndiv
        have eq := congr_arg Subtype.val (eq_neg_of_add_eq_zero_left eq)
        have eq := congr_arg (· / (-2 : ℂ)) eq
        simp at eq
        have r : (-(2 * v)).val = -2 * v.val := by
          rw [neg_eq_neg_one_mul, ←mul_assoc, neg_one_mul]
          rfl
        rw [r] at eq
        simp at eq
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
          simp
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
          simp
          rw [(congr_arg Complex.re hm.left : s.val.re = n / 2)]
          rw [(congr_arg Complex.im hm.left : s.val.im = √19 * m / 2)]
          rw [(rfl : t'.val.re = -n / 2)]
          rw [(rfl : t'.val.im = (√19 * m / 2))]
          ring_nf
        have eq₃ : s'' = -⌊(t'.val * v.val / u).re⌋ := rfl
        apply Exists.intro s'
        apply Exists.intro t'
        apply And.intro
        . simp
          have is_zero : Complex.normSq (0 : R) = 0 := calc
            _ = Complex.normSq (0 : ℂ) := rfl
            _ = 0 := by simp
          rw [is_zero]
          simp
          have eq : (s' * u + t' * v).val = (s'.val * u.val + t'.val * v.val) := rfl
          rw [eq]
          have th : (s'.val * u + t' * v) / u ≠ 0 := by
            rw [add_div]
            rw [div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, div_self nzero_c]
            simp
            apply ne_of_apply_ne Complex.re
            simp
            have ne_zero_of_ne_zero_fract : ∀ a : ℝ, a = 0 → Int.fract a = 0 := λ a => λ ha => by rw[ha]; simp
            apply not_imp_not.mpr (ne_zero_of_ne_zero_fract ((s'.val + (t'.val * v / u)).re))
            rw [Complex.add_re]
            rw [eq₀, Int.fract_int_add s'' _]
            rw [div_eq_mul_inv, mul_assoc, ←div_eq_mul_inv, eq']
            rw [hm.left, t'_eq]
            simp; ring_nf; simp
            rw [←right_distrib, ←div_eq_mul_inv]
            norm_cast
            apply fract_not_zero_of_mod_not_zero_q (n ^ 2 + 19 * m ^ 2) 8
            . exact Int.sign_eq_one_iff_pos.mp rfl
            . cases Int.emod_two_eq_zero_or_one n with
              | inl even =>
                have e : n % 2 = 0 ↔ n ≡ 0 [ZMOD 2] := Eq.to_iff rfl
                rw [e] at even
                have meven : m ≡ 0 [ZMOD 2] := calc
                  m ≡ n [ZMOD 2] := hm.right.symm
                  _ ≡ 0 [ZMOD 2] := even
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
                        . simp
                          rw [←div_by_k_exact_on_mult n two_ne_zero even]
                          ring_nf
                        . simp
                          rw [←div_by_k_exact_on_mult m two_ne_zero meven]
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
                        simp at th
                        exact th
                    simp at abs
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
                        simp at th
                        exact th
                    simp at abs
                    have := Int.ModEq.trans abs.symm abs'
                    contradiction
                  | inr twom =>
                    have : s.val / 2 ∈ R := by
                      apply Exists.intro (n / 2)
                      apply Exists.intro (m / 2)
                      apply And.intro
                      . rw [hm.left]
                        apply Complex.ext
                        . simp
                          rw [←div_by_k_exact_on_mult n two_ne_zero even]
                          ring_nf
                        . simp
                          rw [←div_by_k_exact_on_mult m two_ne_zero meven]
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
                have modd : m ≡ 1 [ZMOD 2] := calc
                  m ≡ n [ZMOD 2] := hm.right.symm
                  _ ≡ 1 [ZMOD 2] := odd
                have eq1 := odd_one_mod_eight odd
                have eq2 := odd_one_mod_eight modd
                by_contra abs'
                have abs : n ^ 2 + 19 * m ^ 2 ≡ 1 + 19 [ZMOD 8] := by
                  apply Int.ModEq.add
                  . exact eq1
                  . have th : 19 * m ^ 2 ≡ 19 * 1 [ZMOD 8] := Int.ModEq.mul_left 19 eq2
                    simp at th
                    exact th
                simp at abs
                have := Int.ModEq.trans abs.symm abs'
                contradiction
          exact (div_ne_zero_iff.mp th).left
        . simp
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
            simp
            rw [eq₀, eq₁, eq₂]
            simp
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
          . simp
            assumption
    | inr neq =>
      apply Exists.intro s
      apply Exists.intro 2
      refine And.intro ?_ hs
      simp
      have is_zero : Complex.normSq (0 : R) = 0 := calc
        _ = Complex.normSq (0 : ℂ) := rfl
        _ = 0 := by simp
      rw [is_zero]
      simp
      exact Subtype.coe_ne_coe.mpr neq

instance R_dh_domain : DedekindHasseDomain R where
  r := dh_rel_on_r
  r_wellFounded := dh_rel_on_r_well_founded
  linear_comb := dh_rel_on_r_linear_comb
