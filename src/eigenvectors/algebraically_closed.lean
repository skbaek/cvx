
import ring_theory.principal_ideal_domain
import linear_algebra.dimension
import analysis.complex.polynomial

/-
#check linear_map.to_fun

example {α : Type*} [discrete_field α] {β : Type*} [decidable_eq β] [add_comm_group β] [vector_space α β]  
(w : ℕ → β)
: false :=
begin
  let xx := (finsupp.total ℕ β α w).to_fun,
end
-/

open polynomial
open vector_space principal_ideal_domain submodule

/-- algebraically closed field -/
class algebraically_closed (K : Type*) extends discrete_field K :=
(exists_root {p : polynomial K} : 0 < degree p → ∃ a, is_root p a)


set_option class.instance_max_depth 41


universes u v w





namespace algebraically_closed

variables {α : Type u} [hα : algebraically_closed α]

variables {β : Type v} [decidable_eq β] [add_comm_group β] [vector_space α β] (f : β →ₗ[α] β)

set_option class.instance_max_depth 41

#check classical.iff_iff_not_or_and_or_not

--set_option pp.all true

#check degree_eq_one_of_irreducible_of_root
#check eq_X_add_C_of_degree_eq_one

lemma exists_eigenvector (h_dim : dim α β < cardinal.omega) : ∃ (x : β) (c : α), f x = c • x :=
begin
  let v : β := sorry,
  have hv : v ≠ 0, by sorry,
  let w := (λ n : ℕ, (f ^ n) v), 
  have h : ¬ linear_independent α w,
  { intro hw,
    apply not_lt_of_le _ h_dim,
    rw [← cardinal.lift_id (dim α β), cardinal.lift_umax.{v 0}],
    apply linear_independent_le_dim hw },
  have := λ x, h (linear_independent_iff.2 x),
  classical,
  apply exists.elim (not_forall.1 this),
  rcases not_forall.1 this with ⟨p, hp⟩,
  rcases not_imp.1 hp with ⟨h_total_p, h_p_ne_0⟩,
  let p : polynomial α := p, -- TODO: ask Zulip
  have := factors_spec p h_p_ne_0,
  let x := polynomial.eval₂ (λ a, a • linear_map.id) f p v,
end

end algebraically_closed


namespace algebraically_closed

variables {K : Type} [algebraically_closed K]




variables {V : Type} [add_comm_group V] [vector_space K V] [f : V →ₗ[K] V]
variables (h_dim : dim K V < omega)

variable {x : V}

set_option class.instance_max_depth 41

#check linear_independed_le_dim

#check linear_independed_le_dim 




set_option class.instance_max_depth 32

end algebraically_closed

noncomputable instance complex.algebraically_closed : algebraically_closed ℂ := {
  exists_root := (λ p hp, complex.exists_root hp)
}




#check complex.exists_root



end

set_option class.instance_max_depth 32


open principal_ideal_domain
#check factors (p : polynomial ℂ)
#check factors_spec (p : polynomial ℂ)
-- better euclidean_domain -> principle_ideal_domain -> factors

#check polynomial.eval₂ (λc, c • linear_map.id) _ p
#print irreducible.

example : polynomial.eval₂ (λc, c • linear_map.id) (linear_map.id : β →ₗ[α] β) (multiset.prod (factors (p : polynomial ℂ))) 
= multiset.prod (multiset.map polynomial.eval₂ (λc, c • linear_map.id) (linear_map.id : α →ₗ[ℂ] α) (factors (p : polynomial ℂ)))
:=
by library_search

#check polynomial.mul_div_eq_iff_is_root
