import NonEuclideanPid.RingConstruction

variable (α : Type)

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
