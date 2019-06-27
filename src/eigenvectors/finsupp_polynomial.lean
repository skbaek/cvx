import linear_algebra.dimension
import data.polynomial
import ring_theory.principal_ideal_domain

universes u v w



section eval₂
--TODO: move
variables {α : Type u} {β : Type v} [comm_ring α] [decidable_eq α] [semiring β]
variables (f : α → β) [is_semiring_hom f] (x : β) (p q : polynomial α)
open is_semiring_hom
open polynomial finsupp finset


set_option class.instance_max_depth 40

lemma eval₂_mul_noncomm (hf : ∀ a b, f a * b = b * f a) : 
  (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
begin
  dunfold eval₂,
  rw [mul_def, finsupp.sum_mul _ p], simp only [finsupp.mul_sum _ q], rw [sum_sum_index],
  { apply sum_congr rfl, assume i hi, dsimp only, rw [sum_sum_index],
    { apply sum_congr rfl, assume j hj, dsimp only,
      rw [sum_single_index, map_mul f, pow_add],
      { rw [mul_assoc, ←mul_assoc _ (x ^ i), hf _ (x ^ i)], 
        simp only [mul_assoc] },
      { rw [map_zero f, zero_mul] } },
    { intro, rw [map_zero f, zero_mul] },
    { intros, rw [map_add f, add_mul] } },
  { intro, rw [map_zero f, zero_mul] },
  { intros, rw [map_add f, add_mul] }
end

end eval₂


lemma finsupp_total_eq_eval₂ (α : Type v) (β : Type w)
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) (p : polynomial α) : 
  (finsupp.sum p (λ n b, b • (f ^ n) v))  
    = polynomial.eval₂ (λ a, a • linear_map.id) f p v :=
begin
  dunfold polynomial.eval₂ finsupp.sum,
  convert @finset.sum_hom _ _ _ p.support _ _ _ (λ h : β →ₗ[α] β, h v) _,
  simp
end

lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  {f : β →ₗ[α] β} {v : β} : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ (λ a, a • linear_map.id) f p v = 0 → p = 0 :=
by simp only [linear_independent_iff, finsupp.total_apply, finsupp_total_eq_eval₂]; refl



open vector_space principal_ideal_domain

-- TODO: move to dimension.lean
lemma linear_independent_le_dim {α : Type u} {β : Type v} {ι : Type w}
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β] [decidable_eq ι]
  {v : ι → β} (hv : linear_independent α v): cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) : 
     (cardinal.mk_range_eq_of_inj (linear_independent.injective (field.zero_ne_one α) hv)).symm
  ... = cardinal.lift.{v w} (dim α (submodule.span α (set.range v))) : by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (dim α β) : cardinal.lift_le.2 (dim_submodule_le (submodule.span α _))

set_option class.instance_max_depth 36

#check polynomial.degree_eq_zero_of_is_unit
#check polynomial.eval₂_mul

--set_option trace.class_instances true

/-
@[reducible] noncomputable def multiset.to_list {α : Type*} (s : multiset α) := classical.some (quotient.exists_rep s)

@[simp] lemma multiset.to_list_zero {α : Type*} : (multiset.to_list 0 : list α) = [] :=
  (multiset.coe_eq_zero _).1 (classical.some_spec (quotient.exists_rep multiset.zero))

@[simp] lemma multiset.to_list_cons {α : Type*} (a : α) (as : list α) : 
  (multiset.to_list (a :: as) : list α) = [] :=
-/

-- TODO: move
lemma eval₂_prod {α β : Type*} [comm_ring α] [decidable_eq α] [semiring β]
  (f : α → β) [is_semiring_hom f] (hf : ∀ a b, f a * b = b * f a) (x : β)
  (ps : list (polynomial α)) : 
  polynomial.eval₂ f x ps.prod = (ps.map (λ p, (polynomial.eval₂ f x p))).prod :=
begin 
  apply multiset.induction_on ps,
  simp,
  intros p ps ih,
simp [eval₂_mul_noncomm f _ _ _ hf, ih] {contextual := tt},
 end --by apply multiset.induction_on ps; simp {contextual := tt}
.
local attribute [instance, priority 0] polynomial.comm_semiring
local attribute [instance, priority 0] polynomial.nonzero_comm_semiring
local attribute [instance, priority 0] polynomial.nonzero_comm_ring

lemma exists_eigenvector (α : Type v) (β : Type w) 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (h_dim : dim α β < cardinal.omega) : 
  ∃ (x : β) (c : α), f x = c • x :=
begin
  let v : β := sorry,
  have hv : v ≠ 0, by sorry,
  let w := (λ n : ℕ, (f ^ n) v), 
  have h : ¬ linear_independent α w,
  { intro hw,
    apply not_lt_of_le _ h_dim,
    rw [← cardinal.lift_id (dim α β), cardinal.lift_umax.{w 0}],
    unfold cardinal.omega,
    apply linear_independent_le_dim hw },
  have := λ x, h (linear_independent_iff_eval₂.2 x),
  classical,
  rcases not_forall.1 this with ⟨p, hp⟩,
  rcases not_imp.1 hp with ⟨h_eval_p, h_p_ne_0⟩,
  rcases (factors_spec p h_p_ne_0).2 with ⟨c, hc⟩,
  --rw ← units.inv_mul_cancel_right (multiset.prod (factors p)) at hc,
  --have := hc,
--let :=  (λ (a : α), has_scalar.smul a (linear_map.id : β →ₗ[α] β)) ,
  let smul := @has_scalar.smul _ _ (@mul_action.to_has_scalar _ _ _ (@distrib_mul_action.to_mul_action _ _ _ _ (@semimodule.to_distrib_mul_action _ _ _ _ (@module.to_semimodule _ _ _ _ (vector_space.to_module _ _))))),
  have : polynomial.eval₂ (λ (a : α), smul a linear_map.id) f (factors p).prod v = 0,
  { rw ← hc, 
  have := polynomial.eval₂_mul (λ (a : α), smul a linear_map.id),
    --apply h_eval_p,
  }

  --let x := polynomial.eval₂ (λ a, a • linear_map.id) f p v,
end