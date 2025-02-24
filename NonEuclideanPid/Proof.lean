import Init.Data.Cast
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Function
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Paperproof
set_option quotPrecheck false

variable (α : Type)

/- --------------- -/
/- Subset handling -/
/- --------------- -/

theorem naturals_are_well_ordered (s : Set ℕ) : (∃ _ : s, True) → (∃ x : s, ∀ y : s, x.val ≤ y.val) := by
  intro h
  by_contra abs
  have no_less_no_me : ∀ y : ℕ, (∀ x : s, y ≤ x) → y ∉ s := by
    intro y h₁
    by_contra h₂
    apply abs
    exact (Exists.intro (Subtype.mk y  h₂) (λ z => h₁ z))
  have nothing_in_s : ∀ x : ℕ, x ∉ s := by
    intro x
    exact Nat.strongRecOn x (by
    intro n i
    apply no_less_no_me n
    intro x
    by_contra abs
    exact i x (Nat.lt_of_not_le abs) x.property)
  revert h
  apply Not.intro
  intro i
  apply i.elim
  intro v _
  exact nothing_in_s v v.property

theorem function_to_the_naturals_has_min (f : α → ℕ) : (∃ _ : α, True) → (∃ x : α, ∀ y : α, f x ≤ f y) := by
  let im : Set ℕ := λ n => ∃ a : α, f a = n
  let image : α → im := λ x => Subtype.mk (f x) (Exists.intro x rfl)
  intro h
  have im_has_min := by
    apply naturals_are_well_ordered im
    apply h.elim
    intro v _
    exact (Exists.intro (image v) trivial)
  have preimage_exists : ∀ y : im, ∃ x : α, f x = y := by
    by_contra abs
    apply (not_forall.mp abs).elim
    intro v ha
    exact ha v.property
  apply im_has_min.elim
  intro m η₁
  apply (preimage_exists m).elim
  intro n η₂
  apply Exists.intro n
  intro x
  rw [η₂]
  exact η₁ (image x)


/- ------------------------- -/
/- Basic algebra definitions -/
/- ------------------------- -/

def magma : Type :=
  α → α → α

def assoc (f : magma α) : Prop :=
  ∀ x y z : α, f (f x y) z = f x (f y z)

def is_neutral (f : magma α) (e : α) : Prop :=
  ∀ x : α, f e x = x ∧ f x e = x

def has_neutral (f : magma α) : Prop :=
  ∃ e : α, is_neutral α f e

def has_inverse (f : magma α) (x : α) : Prop :=
  ∃ y : α, is_neutral α f (f x y) ∧ is_neutral α f (f y x)

def invertible (f : magma α) : Prop :=
  ∀ x : α, has_inverse α f x

def commutative (f : magma α) : Prop :=
  ∀ x y : α, f x y = f y x

structure comm_monoid_structure (μ : magma α) where
  ass : assoc α μ
  neu : has_neutral α μ
  com : commutative α μ

def comm_monoid : Type :=
  { μ : magma α // comm_monoid_structure α μ }

structure abelian_structure (μ : magma α) where
  ass : assoc α μ
  neu : has_neutral α μ
  com : commutative α μ
  inv : invertible α μ

def abelian : Type :=
  { γ : magma α // abelian_structure α γ }

def is_submagma (μ : magma α) (s : Set α) :=
  ∀ x y : s, (μ x y) ∈ s

def submagma (μ : magma α) : Type :=
  { s: Set α // is_submagma α μ s }

theorem unique_neutral (μ : magma α) : ∀ ε₁ ε₂ : α, is_neutral α μ ε₁ ∧ is_neutral α μ ε₂ → ε₁ = ε₂ := by
  intro ε₁ ε₂ h
  calc
    ε₁ = μ ε₂ ε₁ := by rw [(h.right ε₁).left]
    _ = ε₂ := by rw [(h.left ε₂).right]

/- -------------------------- -/
/- Rings and related concepts -/
/- -------------------------- -/

/- We are only interested in commutative rings -/
structure prering where
  ϕ : abelian α
  ψ : comm_monoid α

variable (ρ' : prering α)

infix:90 " +' " => ρ'.ϕ.val
infix:95 " *' " => ρ'.ψ.val

def distrib : Prop :=
  (∀ x y z : α, x *' (y +' z) = (x *' y) +' (x *' z))
  ∧
  (∀ x y z : α, (y +' z) *' x = (y *' x) +' (z *' x))

def ring : Type :=
  { s : prering α // distrib α s }

variable (ρ : ring α)

infix:90 " +ᵣ " => ρ.val.ϕ.val
infix:95 " *ᵣ " => ρ.val.ψ.val

theorem zero_absorbs_ψ : ∀ x : α, is_neutral α ρ.val.ϕ.val x → ∀ y : α, y *ᵣ x = x := by
  intro x ε y
  have ε₁ := calc
    y *ᵣ x = y *ᵣ (x +ᵣ x) := by rw [(ε x).right]
    _ = y *ᵣ x +ᵣ y *ᵣ x := by rw [ρ.property.left]
  apply Exists.elim
  . exact ρ.val.ϕ.property.inv (y *ᵣ x)
  . intro i hi
    have ε₂ := calc
      (y *ᵣ x) +ᵣ i = (y *ᵣ x +ᵣ y *ᵣ x) +ᵣ i := by rw [←ε₁]
      _ = y *ᵣ x +ᵣ (y *ᵣ x +ᵣ i) := by rw [ρ.val.ϕ.property.ass]
      _ = y *ᵣ x := by rw [(hi.left (y *ᵣ x)).right]
    apply unique_neutral α ρ.val.ϕ.val (y *ᵣ x) x
    apply And.intro
    . rw [←ε₂]
      exact hi.left
    . exact ε

def absorbs_ψ (σ : Set α) : Prop :=
  ∀ s : σ, ∀ r : α, (r *ᵣ s) ∈ σ ∧ (s *ᵣ r) ∈ σ

structure is_ideal (α : Type) (ρ : ring α) (s : Set α) where
  subgroup : is_submagma α ρ.val.ϕ.val s
  absorbs : absorbs_ψ α ρ s
  nonempty : ∃ _ : s, True

def is_generated_ideal (s : Set α) : Prop :=
  ∃ x: α, ∀ y : α, y ∈ s ↔ ∃ r : α, (r *ᵣ x) = y

lemma generated_ideal_is_additive_subgroup (i : Set α) : is_generated_ideal α ρ i → is_submagma α ρ.val.ϕ.val i := by
  intro g
  apply g.elim
  intro γ h x y
  apply ((h y).mp y.property).elim
  apply ((h x).mp x.property).elim
  intro r₁ h₁ r₂ h₂
  have ε : x +ᵣ y = (r₁ +ᵣ r₂) *ᵣ γ := calc
    x +ᵣ y = (r₁ *ᵣ γ) +ᵣ y := by rw [h₁]
    _ = (r₁ *ᵣ γ) +ᵣ (r₂ *ᵣ γ) := by rw [h₂]
    _ = (r₁ +ᵣ r₂) *ᵣ γ := by rw [ρ.property.right]
  exact (h (x +ᵣ y)).mpr (Exists.intro (r₁ +ᵣ r₂) ε.symm)

lemma generated_ideal_absorbs_ψ (i : Set α) : is_generated_ideal α ρ i → absorbs_ψ α ρ i := by
  intro g
  apply g.elim
  intro γ h x y
  apply ((h x).mp x.property).elim
  intro r h1
  have ε₁ : y *ᵣ x = (y *ᵣ r) *ᵣ γ := calc
    y *ᵣ x = y *ᵣ (r *ᵣ γ) := by rw [h1]
    _ = (y *ᵣ r) *ᵣ γ := by rw [ρ.val.ψ.property.ass]
  have ε₂ : x *ᵣ y = (y *ᵣ r) *ᵣ γ := calc
    x *ᵣ y = y *ᵣ x := by rw [ρ.val.ψ.property.com]
    _ = (y *ᵣ r) *ᵣ γ := by rw [ε₁]
  apply And.intro
  . exact (h (y *ᵣ x)).mpr (Exists.intro (y *ᵣ r) ε₁.symm)
  . exact (h (x *ᵣ y)).mpr (Exists.intro (y *ᵣ r) ε₂.symm)

lemma generated_ideal_is_nonempty (i : Set α) : is_generated_ideal α ρ i → ∃ _ : i, True := by
  intro h
  apply h.elim
  intro γ η
  apply Exists.intro (Subtype.mk (γ *ᵣ γ) ((η (γ *ᵣ γ)).mpr (Exists.intro γ rfl)))
  trivial

theorem generated_ideal_is_ideal (i : Set α) : is_generated_ideal α ρ i → is_ideal α ρ i :=
  λ h => is_ideal.mk
    ((generated_ideal_is_additive_subgroup α ρ i) h)
    ((generated_ideal_absorbs_ψ α ρ i) h)
    ((generated_ideal_is_nonempty α ρ i) h)

def no_divisors_of_0 : Prop :=
  ∀ x y : α, is_neutral α ρ.val.ϕ.val (x *ᵣ y) → (is_neutral α ρ.val.ϕ.val x ∨ is_neutral α ρ.val.ϕ.val y)

def domain : Type :=
  { ρ // no_divisors_of_0 α ρ }

variable (δ : domain α)

infix:90 " + " => δ.val.val.ϕ.val
infix:95 " * " => δ.val.val.ψ.val

def is_principal_ideal_domain : Prop :=
  ∀ i : Set α, is_ideal α δ.val i → is_generated_ideal α δ.val i

def divides (x y : α) : Prop :=
  ∃ z : α, z * x = y

def is_dedekind_hasse_norm (h : α → ℕ) : Prop :=
  (∀ x : α, h x = 0 ↔ is_neutral α δ.val.val.ϕ.val x)
  ∧
  (∀ u v : α, (¬ divides α δ u v) → (∃ s t : α,
    h ((s * u) + (t * v)) ≠ 0 ∧ h ((s * u) + (t * v)) < h u
  ))

def nonzero : Type :=
  { x : α // ¬ is_neutral α δ.val.val.ϕ.val x }

theorem has_dedekind_hasse_norm_implies_pid (h : α → ℕ) : is_dedekind_hasse_norm α δ h → is_principal_ideal_domain α δ := by
  intro dh_norm ideal is_id
  let δ' : Type := { x : ideal // ¬ is_neutral α δ.val.val.ϕ.val x }
  apply (Classical.em (∃ _ : δ', True)).elim
  . intro ne
    have μ' : ∃ a : δ', ∀ b : δ', h b ≥ h a := function_to_the_naturals_has_min δ' (λ d => h d) ne
    have μ'' : ∃ a : δ', ∀ b : ideal, h b < h a → is_neutral α δ.val.val.ϕ.val b := by
      apply μ'.elim
      intro m η₁
      apply Exists.intro m
      intro v η₂
      by_contra abs
      have p := Nat.not_lt_of_ge (η₁ (Subtype.mk v abs))
      contradiction
    have μ : ∃ a : ideal, ∀ b : ideal, h b < h a → is_neutral α δ.val.val.ϕ.val b := by
      apply μ''.elim
      intro _ η
      apply Exists.intro
      intro x
      exact η x
    apply μ.elim
    intro γ hγ
    apply Exists.intro
    intro e
    apply Iff.intro
    . intro η
      by_contra abs
      apply ((dh_norm.right γ e) abs).elim
      intro s h₁
      apply h₁.elim
      intro t
      have comb_gives_abs : ∀ el : ideal, ¬ (h el ≠ 0 ∧ h el < h γ) := by
        intro el_abs abs
        exact abs.left ((dh_norm.left el_abs).mpr (hγ el_abs abs.right))
      have su_in_ideal := (is_id.absorbs γ s).left
      have tv_in_ideal := (is_id.absorbs (Subtype.mk e η) t).left
      have comb_in_ideal := is_id.subgroup
        (Subtype.mk (s * γ) su_in_ideal)
        (Subtype.mk (t * e) tv_in_ideal)
      exact comb_gives_abs (Subtype.mk ((s * γ) + (t * e)) comb_in_ideal)
    . intro h
      apply h.elim
      intro x w
      have sub : (x * γ) ∈ ideal → x * γ = e → e ∈ ideal := by
        intro h1 h2
        rw [←h2]
        exact h1
      exact sub (is_id.absorbs γ x).left w
  . intro Classical.em
    have all_neutral : ∀ x : ideal, is_neutral α δ.val.val.ϕ.val x := by
      by_contra abs
      apply (not_forall.mp abs).elim
      intro v ha
      exact (Classical.em (Exists.intro (Subtype.mk v ha) trivial))
    have all_equal : ∀ x y : ideal, x.val = y.val := λ x => λ y => unique_neutral α δ.val.val.ϕ.val x y (And.intro (all_neutral x) (all_neutral y))
    apply δ.val.val.ϕ.property.neu.elim
    intro z hz
    apply Exists.intro z
    intro x
    apply Iff.intro
    . intro η
      apply Exists.intro z
      let ix := Subtype.mk x η
      have x₀ : is_neutral α δ.val.val.ϕ.val x := all_neutral ix
      have iz₀' : (z * z) ∈ ideal := by
        rw [zero_absorbs_ψ α δ.val z hz z]
        rw [←zero_absorbs_ψ α δ.val z hz x]
        rw [δ.val.val.ψ.property.com]
        rw [zero_absorbs_ψ α δ.val x x₀ z]
        exact η
      let iz₀ := Subtype.mk (z * z) iz₀'
      exact all_equal iz₀ ix
    . intro η
      apply is_id.nonempty.elim
      intro e _
      have z₀ : z ∈ ideal := by
        rw [←(zero_absorbs_ψ α δ.val z hz) e]
        exact (is_id.absorbs e z).right
      apply η.elim
      intro r hr
      rw [←hr]
      exact (is_id.absorbs (Subtype.mk z z₀) r).left

def is_euclidean_norm (g : nonzero α δ → ℕ) : Prop :=
  (
    ∀ z : nonzero α δ, ∀ x y : nonzero α δ, z.val = x.val * y.val → g z ≥ g x
  )
  ∧
  (
    ∀ a: α, ∀ b : nonzero α δ,
    (∃ q : α, a = b.val * q)
    ∨
    (∃ q : α, ∃ r : nonzero α δ, a = (b.val * q) + r.val ∧ g r < g b)
  )

theorem invertibles_iff_least_degree (g : nonzero α δ → ℕ) :
is_euclidean_norm α δ g → ∀ x : nonzero α δ, (∀ y : nonzero α δ, g y ≥ g x) ↔ (has_inverse α δ.val.val.ψ.val x.val) := by
  intro h x
  apply δ.val.val.ψ.property.neu.elim
  intro one is_one
  apply δ.val.val.ϕ.property.neu.elim
  intro zero is_zero
  cases Classical.em (zero ≠ one) with
  | inl non_stupid =>
    apply Iff.intro
    . intro η
      apply Or.elim (h.right one x)
      . intro ex
        apply Exists.elim ex
        intro x' eq
        apply Exists.intro x'
        apply And.intro
        . rw [←eq]
          exact is_one
        . rw [δ.val.val.ψ.property.com]
          rw [←eq]
          exact is_one
      . intro ex
        apply Exists.elim ex
        intro q hq
        apply Exists.elim hq
        intro r hr
        have not_min := hr.right
        have min := Nat.not_lt_of_ge (η r)
        contradiction
    . intro η
      apply η.elim
      intro x' hx' y
      have inv_ex : x.val * (y.val * x') = y.val := calc
        x.val * (y.val * x') = (y.val * x') * x.val := by rw [δ.val.val.ψ.property.com]
        _ = y.val * (x' * x.val) := by rw [δ.val.val.ψ.property.ass]
        _ = y.val * (x.val * x') := by rw [δ.val.val.ψ.property.com x.val x']
        _ = y.val := (hx'.left y.val).right
      have inv_non_zero : ¬ is_neutral α δ.val.val.ϕ.val (y.val * x') := by
        by_contra abs
        rw [←zero_absorbs_ψ α δ.val (y.val * x') abs x.val] at abs
        rw [inv_ex] at abs
        exact y.property abs
      let comb : nonzero α δ := (Subtype.mk (y.val * x') inv_non_zero)
      apply h.left y x comb
      exact inv_ex.symm
  | inr stupid =>
    have stupid : zero = one := by
      by_contra abs
      rw [←Ne.eq_1 zero one] at abs
      contradiction
    have all_zero : ∀ x : α, x = zero := by
      intro x
      calc
        x = one * x := (is_one x).left.symm
        _ = zero * x := by rw [stupid]
        _ = x * zero := by rw [δ.val.val.ψ.property.com]
        _ = zero := zero_absorbs_ψ α δ.val zero is_zero x
    have l_is_true : ∀ (y : nonzero α δ), g y ≥ g x := by
      by_contra abs
      rw [not_forall] at abs
      apply abs.elim
      intro v _
      have v_is_not_neutral := v.property
      have v_is_neutral : is_neutral α δ.val.val.ϕ.val v.val := by
        rw [all_zero v.val]
        exact is_zero
      contradiction
    have r_is_true : has_inverse α δ.val.val.ψ.val x.val := by
      apply Exists.intro zero
      apply And.intro
      . rw [zero_absorbs_ψ]
        rw [stupid]
        repeat assumption
      . rw [δ.val.val.ψ.property.com]
        rw [zero_absorbs_ψ]
        rw [stupid]
        repeat assumption
    apply Iff.intro
    . intro
      exact r_is_true
    . intro
      exact l_is_true

structure is_universal_side_divisor (u : α) where
  not_zero : ¬ is_neutral α δ.val.val.ϕ.val u
  not_inv : ¬ has_inverse α δ.val.val.ψ.val u
  usd_prop : ∀ x : α, ∃ q r : α, x = (u * q) + r ∧ (is_neutral α δ.val.val.ϕ.val r ∨ has_inverse α δ.val.val.ψ.val r)

theorem ed_not_field_implies_having_usd (g : nonzero α δ → ℕ) :
is_euclidean_norm α δ g → (∃ x : α, ¬ is_neutral α δ.val.val.ϕ.val x ∧ ¬ has_inverse α δ.val.val.ψ.val x) → ∃ u : α, is_universal_side_divisor α δ u := by
  intro norm good
  let good_set : Set α := λ x => ¬ is_neutral α δ.val.val.ϕ.val x ∧ ¬ has_inverse α δ.val.val.ψ.val x
  let g_rest : good_set → ℕ := λ x => g (Subtype.mk x.val x.property.left)
  have has_min := function_to_the_naturals_has_min good_set g_rest (good.elim λ v => λ hv => Exists.intro (Subtype.mk v hv) trivial)
  apply has_min.elim
  intro u hu
  apply Exists.intro u.val
  apply is_universal_side_divisor.mk
  . exact u.property.left
  . exact u.property.right
  . intro x
    have euclidean_division := norm.right x (Subtype.mk u.val u.property.left)
    cases euclidean_division with
    | inl exa =>
      apply exa.elim
      intro q hq
      apply Exists.intro q
      apply δ.val.val.ϕ.property.neu.elim
      intro r hr
      apply Exists.intro r
      apply And.intro
      . rw [←hq]
        rw [(hr x).right]
      . apply Or.inl
        exact hr
    | inr rem =>
      apply rem.elim
      intro q hq
      apply Exists.intro q
      apply hq.elim
      intro r hr
      apply Exists.intro r.val
      apply And.intro
      . exact hr.left
      . apply Or.inr
        have r_not_good : ¬ good_set r.val := by
          by_contra abs
          have _ := hu (Subtype.mk r.val abs)
          have _ := Nat.not_le_of_gt hr.right
          contradiction
        rw [not_and_or] at r_not_good
        cases r_not_good with
        | inl is_neu =>
          rw [not_not] at is_neu
          have not_neu := r.property
          contradiction
        | inr is_inv =>
          rw [not_not] at is_inv
          exact is_inv

def is_in_R (c : ℂ) : Prop :=
  ∃ x y : ℤ, (c = Complex.mk ((Int.cast x) / 2) (√19 * (Int.cast y) / 2)) ∧ x ≡ y [ZMOD 2]

def R : Type :=
  { c : ℂ // is_in_R c }

theorem R_closed_under_complex_addition (z₁ z₂ : ℂ) : is_in_R z₁ → is_in_R z₂ → is_in_R (z₁ + z₂) := by
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

lemma div_and_mul_by_two_on_even (x : ℤ) : x ≡ 0 [ZMOD 2] → 2 * (x / 2) = x := by
  intro x_even
  have th := Int.ediv_add_emod x 2
  rw [x_even] at th
  simp at th
  exact th

lemma division_by_two_exact_on_even (x : ℤ) : x ≡ 0 [ZMOD 2] → (x : ℝ) / 2 = ↑(x / 2) := by
  intro x_even
  let x' := x / 2
  let xr := (x : ℝ) / 2
  have two_xr_eq_x : 2 * xr = x := calc
    2 * xr = 2 * (↑x / (2 : ℝ)) := by rfl
    _ = 2 * (↑x * (2 : ℝ)⁻¹) := by rw [div_eq_mul_inv ↑x (2 : ℝ)]
    _ = 2 * ((2 : ℝ)⁻¹ * ↑x) := by conv in ((2 : ℝ)⁻¹ * ↑x) => rw [mul_comm]
    _ = x := by rw [←mul_assoc]; simp
  have two_x'_eq_x : (2 * x' : ℝ) = (x : ℝ) := by
    have th := div_and_mul_by_two_on_even x x_even
    rify at th
    exact th

  calc
    xr = (2⁻¹ * 2) * xr := by simp
    _ = 2⁻¹ * (2 * xr) := by rw [mul_assoc]
    _ = 2⁻¹ * (x : ℝ) := by rw [two_xr_eq_x]
    _ = 2⁻¹ * (2 * x' : ℝ) := by rw [two_x'_eq_x]
    _ = (2⁻¹ * 2) * (x' : ℝ) := by rw [←mul_assoc]
    _ = x' := by simp

theorem R_closed_under_complex_multiplication (z₁ z₂ : ℂ) : is_in_R z₁ → is_in_R z₂ → is_in_R (z₁ * z₂) := by
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

  have eqx := division_by_two_exact_on_even x x_even
  have eqy := division_by_two_exact_on_even y y_even

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
      rw [div_and_mul_by_two_on_even x x_even]
      rw [div_and_mul_by_two_on_even y y_even]
      calc
        x₁ * x₂ - (y₁ * y₂) * 19 = (-(20 * (y₁ * y₂))) + ((x₁ * x₂) + (y₁ * y₂)) := by ring_nf
        _ ≡ 0 + ((x₁ * x₂) + (y₁ * y₂)) [ZMOD 4] := Int.ModEq.add sub rfl
        _ ≡ (x₁ * x₂) + (y₁ * y₂) [ZMOD 4] := by simp
        _ ≡ y [ZMOD 4] := (Int.modEq_of_dvd div4).symm

    apply Int.ModEq.cancel_left_div_gcd (Int.sign_eq_one_iff_pos.mp rfl) eq

def r_ϕ (x y : R) : R :=
  Subtype.mk (x.val + y.val) (R_closed_under_complex_addition x.val y.val x.property y.property)

def r_ψ (x y : R) : R :=
  Subtype.mk (x.val * y.val) (R_closed_under_complex_multiplication x.val y.val x.property y.property)

def R_additive_group : abelian R := by
  apply Subtype.mk r_ϕ
  apply abelian_structure.mk
  . intro x y z
    apply Subtype.ext
    calc
      _ = (x.val + y.val) + z.val := rfl
      _ = x.val + (y.val + z.val) := by ring
      _ = (r_ϕ x (r_ϕ y z)).val := rfl
  . let zero : R := by
      apply Subtype.mk (0 : ℂ)
      apply Exists.intro 0
      apply Exists.intro 0
      apply And.intro
      . apply Complex.ext
        . simp
        . simp
      . rfl
    apply Exists.intro zero
    intro v
    apply And.intro
    . apply Subtype.ext
      calc
        _ = zero.val + v.val := rfl
        _ = v.val := by ring
    . apply Subtype.ext
      calc
        _ = v.val + zero.val := rfl
        _ = v.val := by ring
  . intro x y
    apply Subtype.ext
    calc
      _ = x.val + y.val := rfl
      _ = y.val + x.val := by ring
      _ = (r_ϕ y x).val := rfl
  . intro x
    let x' : R := by
      apply Subtype.mk (-x.val)
      apply (x.property).elim
      intro n hn
      apply hn.elim
      intro m hm
      apply Exists.intro (-n)
      apply Exists.intro (-m)
      apply And.intro
      . apply Complex.ext
        . simp [Complex.add_re]
          rw [hm.left]
          simp
          ring
        . simp [Complex.add_im]
          rw [hm.left]
          simp
          ring
      . simp
        exact hm.right
    apply Exists.intro x'
    apply And.intro
    . intro v
      apply And.intro
      . apply Subtype.ext
        calc
          (r_ϕ (r_ϕ x x') v).val = (x.val + x'.val) + v.val := rfl
          _ = v.val := by ring
      . apply Subtype.ext
        calc
          (r_ϕ v (r_ϕ x x')).val = v.val + (x.val + x'.val) := rfl
          _ = v.val := by ring
    . intro v
      apply And.intro
      . apply Subtype.ext
        calc
          (r_ϕ (r_ϕ x' x) v).val = (x'.val + x.val) + v.val := rfl
          _ = v.val := by ring
      . apply Subtype.ext
        calc
          (r_ϕ v (r_ϕ x' x)).val = v.val + (x'.val + x.val) := rfl
          _ = v.val := by ring

def R_multiplicative_group : comm_monoid R := by
  apply Subtype.mk r_ψ
  apply comm_monoid_structure.mk
  . intro x y z
    apply Subtype.ext
    calc
      _ = (x.val * y.val) * z.val := rfl
      _ = x.val * (y.val * z.val) := by ring
      _ = (r_ψ x (r_ψ y z)).val := rfl
  . let one : R := by
      apply Subtype.mk (1 : ℂ)
      apply Exists.intro 2
      apply Exists.intro 0
      apply And.intro
      . apply Complex.ext
        . simp
        . simp
      . rfl
    apply Exists.intro one
    intro v
    apply And.intro
    . apply Subtype.ext
      calc
        _ = one.val * v.val := rfl
        _ = v.val := by ring
    . apply Subtype.ext
      calc
        _ = v.val * one.val := rfl
        _ = v.val := by ring
  . intro x y
    apply Subtype.ext
    calc
      _ = x.val * y.val := rfl
      _ = y.val * x.val := by ring
      _ = (r_ψ y x).val := rfl

def D₀ : prering R :=
  prering.mk R_additive_group R_multiplicative_group

theorem R_ϕ_distrib_R_ψ : distrib R D₀ := by
  apply And.intro
  . intro x y z
    apply Subtype.ext
    calc
      _ = x.val * (y.val + z.val) := rfl
      _ = (x.val * y.val) + (x.val * z.val) := by ring
  . intro x y z
    apply Subtype.ext
    calc
      _ = (y.val + z.val) * x.val := rfl
      _ = (y.val * x.val) + (z.val * x.val) := by ring

def D : ring R :=
  Subtype.mk D₀ R_ϕ_distrib_R_ψ
