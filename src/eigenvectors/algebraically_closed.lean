
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


-- TODO: move to dimension.lean
lemma linear_independent_le_dim {α : Type u} {β : Type v} {ι : Type w}
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β] [decidable_eq ι]
  {v : ι → β} (hv : linear_independent α v): cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) : 
     (cardinal.mk_range_eq_of_inj (linear_independent.injective (field.zero_ne_one α) hv)).symm
  ... = cardinal.lift.{v w} (dim α (span α (set.range v))) : by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (dim α β) : cardinal.lift_le.2 (dim_submodule_le (span α _))




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


-- TODO: move
lemma polynomial.not_is_unit_X_sub_C {α : Type} [integral_domain α] [decidable_eq α]:  
  ∀ a : α, ¬ is_unit (X - C a) :=
begin intros a ha, 
  let ha' := degree_eq_zero_of_is_unit ha,
  rw [degree_X_sub_C] at ha',
  apply nat.zero_ne_one (option.injective_some _ ha'.symm)
end

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
