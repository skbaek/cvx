import algebra.ring

universes u v
variable {α : Type u}

section domain
  variable [domain α]

  lemma mul_ne_zero_iff {a b : α} : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := 
  by classical; rw [←not_iff_not, not_and_distrib, not_not, not_not, not_not, mul_eq_zero]

end domain