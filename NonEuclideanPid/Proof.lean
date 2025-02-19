import Paperproof
set_option quotPrecheck false
open Classical

variable (α : Type)

theorem contrapositive (p q : Prop) : (¬q → ¬p) ↔ (p → q) := by
  apply Iff.intro
  . exact λ h₁ => λ h₂ => byContradiction (λ h₃ => (h₁ h₃) h₂)
  . exact λ h₁ => λ h₂ => byContradiction (λ h₃ => h₂ (h₁ (not_not.mp h₃)))

/- --------------- -/
/- Subset handling -/
/- --------------- -/

def Set : Type :=
  α -> Prop

instance : CoeOut (Set α) Type :=
  ⟨λ s => { x : α // s x }⟩

def In (x : α) (σ : Set α) : Prop :=
  σ x

def not_In (x : α) (σ : Set α) : Prop :=
  ¬ (In α x σ)

infix:100 " ∈ " => In α
infix:100 " ∉ " => not_In α
infix:100 " ∈ₙ " => In Nat
infix:100 " ∉ₙ " => not_In Nat

theorem naturals_are_well_ordered (s : Set Nat) : (∃ _ : ↑s, True) → (∃ x : ↑s, ∀ y : ↑s, x.val ≤ y.val) := by
  intro h
  apply byContradiction
  intro abs
  have no_less_no_me : ∀ y : Nat, (∀ x : ↑s, y ≤ x) → y ∉ₙ s := by
    intro y h₁
    apply byContradiction
    intro h₂
    apply abs
    exact (Exists.intro (Subtype.mk y (not_not.mp h₂)) (λ z => h₁ z))
  have nothing_in_s : ∀ x : Nat, x ∉ₙ s := by
    intro x
    exact Nat.strongRecOn x (by
    intro n i
    apply no_less_no_me n
    intro x
    apply byContradiction
    intro abs
    exact i x (Nat.lt_of_not_le abs) x.property)
  revert h
  apply Not.intro
  intro i
  apply i.elim
  intro v _
  exact nothing_in_s v v.property

theorem function_to_the_naturals_has_min (f : α → Nat) : (∃ _ : α, True) → (∃ x : α, ∀ y : α, f x ≤ f y) := by
  let im : Set Nat := λ n => ∃ a : α, f a = n -- SUS
  let image : α → ↑im := λ x => Subtype.mk (f x) (Exists.intro x rfl) -- $S N S^(-1)$
  intro h
  have im_has_min := by
    apply naturals_are_well_ordered im -- sus
    apply h.elim
    intro v _
    exact (Exists.intro (image v) trivial)
  have preimage_exists : ∀ y : ↑im, ∃ x : α, f x = y := by
    apply byContradiction
    intro abs
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

def invertible (f : magma α) : Prop :=
  ∀ x : α, ∃ y : α, is_neutral α f (f x y) ∧ is_neutral α f (f y x)

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
  ∀ x y : ↑s, (μ x y) ∈ s

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
  ∀ s : ↑σ, ∀ r : α, (r *ᵣ s) ∈ σ ∧ (s *ᵣ r) ∈ σ

structure is_ideal (α : Type) (ρ : ring α) (s : Set α) where
  subgroup : is_submagma α ρ.val.ϕ.val s
  absorbs : absorbs_ψ α ρ s
  nonempty : ∃ _ : ↑s, True

def is_generated_ideal (s : Set α) : Prop :=
  ∃ x: α, ∀ y : α, y ∈ s ↔ ∃ r : α, (r *ᵣ x) = y

theorem generated_ideal_is_additive_subgroup (i : Set α) : is_generated_ideal α ρ i → is_submagma α ρ.val.ϕ.val i := by
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

theorem generated_ideal_absorbs_ψ (i : Set α) : is_generated_ideal α ρ i → absorbs_ψ α ρ i := by
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

theorem generated_ideal_is_nonempty (i : Set α) : is_generated_ideal α ρ i → ∃ _ : ↑i, True := by
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

def is_dedekind_hasse_norm (h : α → Nat) : Prop :=
  (∀ x : α, h x = 0 ↔ is_neutral α δ.val.val.ϕ.val x)
  ∧
  (∀ u v : α, (¬ divides α δ u v) → (∃ s t : α,
    h ((s * u) + (t * v)) ≠ 0 ∧ h ((s * u) + (t * v)) < h u
  ))

def nonzero : Type :=
  { x : α // ¬ is_neutral α δ.val.val.ϕ.val x }

theorem has_dedekind_hasse_norm_implies_pid (h : α → Nat) : is_dedekind_hasse_norm α δ h → is_principal_ideal_domain α δ := by
  intro dh_norm ideal is_id
  let δ' : Type := { x : ↑ideal // ¬ is_neutral α δ.val.val.ϕ.val x }
  apply (em (∃ _ : ↑δ', True)).elim
  . intro ne
    have μ' : ∃ a : δ', ∀ b : δ', h b ≥ h a := function_to_the_naturals_has_min δ' (λ d => h d) ne
    have μ'' : ∃ a : δ', ∀ b : ↑ideal, h b < h a → is_neutral α δ.val.val.ϕ.val b := by
      apply μ'.elim
      intro m η₁
      apply Exists.intro m
      intro v η₂
      apply byContradiction
      intro abs
      have p := Nat.not_lt_of_ge (η₁ (Subtype.mk v abs))
      contradiction
    have μ : ∃ a : ↑ideal, ∀ b : ↑ideal, h b < h a → is_neutral α δ.val.val.ϕ.val b := by
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
      apply byContradiction
      intro abs
      apply ((dh_norm.right γ e) abs).elim
      intro s h₁
      apply h₁.elim
      intro t
      have comb_gives_abs : ∀ el : ↑ideal, ¬ (h el ≠ 0 ∧ h el < h γ) := by
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
  . intro em
    have all_neutral : ∀ x : ↑ideal, is_neutral α δ.val.val.ϕ.val x := byContradiction (
      λ abs => Exists.elim (not_forall.mp abs) (λ v => λ ha => (em (Exists.intro (Subtype.mk v ha) trivial))
    ))
    have all_equal : ∀ x y : ↑ideal, x.val = y.val := λ x => λ y => unique_neutral α δ.val.val.ϕ.val x y (And.intro (all_neutral x) (all_neutral y))
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

def is_euclidean_norm (g : nonzero α δ → Nat) : Prop :=
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

theorem invertibles_iff_least_degree (g : nonzero α δ → Nat) :
is_euclidean_norm α δ g → ∀ x : nonzero α δ, (∀ y : nonzero α δ, g y ≥ g x) ↔ (∃ x' : α, is_neutral α δ.val.val.ψ.val (x.val * x')) := by
  intro h x
  apply δ.val.val.ψ.property.neu.elim
  intro one is_one
  apply δ.val.val.ϕ.property.neu.elim
  intro zero is_zero
  cases em (zero ≠ one) with
  | inl non_stupid =>
    apply Iff.intro
    . intro η
      apply Or.elim (h.right one x)
      . intro ex
        apply Exists.elim ex
        intro x' eq
        apply Exists.intro x'
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
        _ = y.val := (hx' y.val).right
      have inv_non_zero : ¬ is_neutral α δ.val.val.ϕ.val (y.val * x') := by
        apply byContradiction
        intro abs
        rw [not_not] at abs
        rw [←zero_absorbs_ψ α δ.val (y.val * x') abs x.val] at abs
        rw [inv_ex] at abs
        exact y.property abs
      let comb : nonzero α δ := (Subtype.mk (y.val * x') inv_non_zero)
      apply h.left y x comb
      exact inv_ex.symm
  | inr stupid =>
    have stupid : zero = one := by
      apply byContradiction
      intro abs
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
      apply byContradiction
      intro abs
      rw [not_forall] at abs
      apply abs.elim
      intro v _
      have v_is_not_neutral := v.property
      have v_is_neutral : is_neutral α δ.val.val.ϕ.val v.val := by
        rw [all_zero v.val]
        exact is_zero
      contradiction
    have r_is_true : ∃ x' : α, is_neutral α δ.val.val.ψ.val (x.val * x') := by
      apply Exists.intro zero
      rw [zero_absorbs_ψ]
      rw [stupid]
      repeat assumption
    apply Iff.intro
    . intro
      exact r_is_true
    . intro
      exact l_is_true
