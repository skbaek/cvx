
import analysis.complex.polynomial
import ring_theory.principal_ideal_domain
import linear_algebra.dimension

open polynomial
open vector_space cardinal principal_ideal_domain submodule

-- TODO: move
lemma polynomial.not_is_unit_X_sub_C {α : Type} [integral_domain α] [decidable_eq α]:  ∀ a : α, ¬ is_unit (X - C a) :=
begin intros a ha, 
  let ha' := degree_eq_zero_of_is_unit ha,
  rw [degree_X_sub_C] at ha',
  apply nat.zero_ne_one (option.injective_some _ ha'.symm)
end

-- TODO: move to dimension.lean
lemma linear_independed_le_dim {α β : Type} [discrete_field α] [add_comm_group β] [vector_space α β]
{I : set β} (hI : linear_independent α I): cardinal.mk I ≤ dim α β :=
calc
  cardinal.mk I = dim α (span α I) : (dim_span hI).symm
  ... ≤ dim α β : dim_submodule_le (span α I)

/-- algebraically closed field -/
class algebraically_closed (K : Type) extends discrete_field K :=
(exists_root {p : polynomial K} : 0 < degree p → ∃ a, is_root p a)

namespace algebraically_closed

variables {K : Type} [algebraically_closed K]

lemma degree_le_one_of_irreducible (p : polynomial K) : irreducible p → p.degree ≤ 1 :=
begin
  by_cases h_cases : 0 < p.degree,
  { 
    assume hp : irreducible p,
    show degree p ≤ 1,
    { cases (algebraically_closed.exists_root h_cases) with a ha,
      have h_p_eq_mul : (X - C a) * (p / (X - C a)) = p,
        { apply mul_div_eq_iff_is_root.2 ha },
      have h_unit : is_unit (p / (X - C a)),
      from or.resolve_left 
            (hp.2 (X - C a) (p / (X - C a)) h_p_eq_mul.symm) 
            (polynomial.not_is_unit_X_sub_C _),
      show degree p ≤ 1,
        { rw h_p_eq_mul.symm, 
          apply trans (degree_mul_le (X - C a) (p / (X - C a))),
          rw [degree_X_sub_C, degree_eq_zero_of_is_unit h_unit], 
          simp [le_refl] } } },
  { exact λ_, le_trans (le_of_not_gt h_cases) (with_bot.some_le_some.2 (nat.le_succ 0)) }
end


variables {V : Type} [add_comm_group V] [vector_space K V] [f : V →ₗ[K] V]
variables (h_dim : dim K V < omega)

variable {x : V}

set_option class.instance_max_depth 41

#check linear_independed_le_dim

#check linear_independed_le_dim 



lemma exists_eigenvector : ∃ (x : V) (c : K), f.to_fun x = c • x :=
begin
  let s := λ x, set.range (λ n : ℕ, (f ^ n).to_fun x), --TODO: should be multiset ...
  have h : ∀ x, ¬ linear_independent K (s x),
  { intros x hs, 
    let H:= linear_independed_le_dim hs,

  }
end

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
