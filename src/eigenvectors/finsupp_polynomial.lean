import ring_theory.principal_ideal_domain
import linear_algebra.dimension
import data.polynomial

universes u v w

#check @polynomial.euclidean_domain
#check @linear_map.endomorphism_ring
#check @linear_map.module


section smul_id
variables {α : Type v} {β : Type w}

def smul_id [comm_ring α] [add_comm_group β] [module α β] (a : α) : β →ₗ[α] β := a • linear_map.id


--local attribute [instance, priority 0] domain.to_ring
--local attribute [instance, priority 0] division_ring.to_ring

instance smul_id.is_semiring_hom [comm_ring α] [add_comm_group β] [module α β] : 
is_semiring_hom (smul_id : α → β →ₗ[α] β) := {
  map_zero := sorry,
  map_one := sorry,
  map_add := sorry,
  map_mul := sorry
}

lemma smul_id_comm [comm_ring α] [add_comm_group β] [module α β]
  (a : α) (b : β →ₗ[α] β) : 
  smul_id a * b = b * smul_id a :=
begin
  unfold smul_id,
end

end smul_id

section eval₂
--TODO: move
--local attribute [instance, priority 0] domain.to_ring
--local attribute [instance, priority 0] division_ring.to_ring
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

set_option pp.all true
#check eval₂_mul_noncomm

end eval₂

--set_option pp.all true
--#check @eval₂_mul_noncomm _ _ _ _ _ smul_id


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

--set_option pp.all true
--#check @finsupp_total_eq_eval₂

lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ smul_id f p v = 0 → p = 0 :=
by simp only [linear_independent_iff, finsupp.total_apply, finsupp_total_eq_eval₂]; refl


--set_option pp.all true
--#check @linear_independent_iff_eval₂


open vector_space principal_ideal_domain

--local attribute [instance, priority 10000000] field.to_division_ring
--local attribute [instance, priority 0] discrete_field.to_euclidean_domain

-- TODO: move to dimension.lean
-- TODO: how can we force @comm_ring.to_ring _ (field.to_comm_ring _) ???
lemma linear_independent_le_dim {α : Type u} {β : Type v} {ι : Type w}
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β] [decidable_eq ι]
  {v : ι → β} (hv : @linear_independent _ α _ v _ _ _ (@comm_ring.to_ring _ (field.to_comm_ring _)) _ _) : 
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) : 
     (cardinal.mk_range_eq_of_inj (linear_independent.injective (field.zero_ne_one α) hv)).symm
  ... = cardinal.lift.{v w} (dim α (submodule.span α (set.range v))) : by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (dim α β) : cardinal.lift_le.2 (dim_submodule_le (submodule.span α _))


--set_option pp.all true
#check @linear_independent_le_dim

#check polynomial.degree_eq_zero_of_is_unit
#check polynomial.eval₂_mul

--set_option trace.class_instances true

-- TODO: move
lemma eval₂_prod_noncomm {α β : Type*} [comm_ring α] [decidable_eq α] [semiring β]
  (f : α → β) [is_semiring_hom f] (hf : ∀ a b, f a * b = b * f a) (x : β)
  (ps : list (polynomial α)) : 
  polynomial.eval₂ f x ps.prod = (ps.map (λ p, (polynomial.eval₂ f x p))).prod :=
begin 
  induction ps,
  simp,
  simp [eval₂_mul_noncomm f _ _ _ hf, ps_ih] {contextual := tt}
end

--set_option pp.all true
#check @eval₂_prod_noncomm

local attribute [instance, priority 0] division_ring.to_ring
local attribute [instance, priority 0] domain.to_ring
local attribute [instance, priority 0] euclidean_domain.to_nonzero_comm_ring
local attribute [instance, priority 0] nonzero_comm_ring.to_comm_ring

lemma powers_linear_dependent_of_dim_finite (α : Type v) (β : Type w) 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (h_dim : dim α β < cardinal.omega) (v : β) : 
  ¬ linear_independent α (λ n : ℕ, (f ^ n) v) :=
begin
  intro hw,
  apply not_lt_of_le _ h_dim,
  rw [← cardinal.lift_id (dim α β), cardinal.lift_umax.{w 0}],
  unfold cardinal.omega,
  apply linear_independent_le_dim hw
end

--set_option pp.all true
#check @powers_linear_dependent_of_dim_finite

set_option class.instance_max_depth 35
local attribute [instance, priority 0] polynomial.comm_semiring
local attribute [instance, priority 0] polynomial.nonzero_comm_semiring
local attribute [instance, priority 0] polynomial.nonzero_comm_ring


local attribute [instance, priority 0] polynomial.has_mul
local attribute [instance, priority 0] polynomial.comm_ring
local attribute [instance, priority 0] nonzero_comm_semiring.to_comm_semiring

--set_option pp.all true

lemma mul_unit_eq_iff_mul_inv_eq {α : Type u} [monoid α] (a b : α) (c : units α) : 
a * c = b ↔ a = b * (@has_inv.inv (units α) _ c) :=
by rw [←units.inv_mul_cancel_right b c, units.mul_right_inj, mul_assoc, units.mul_inv, mul_one]


@[reducible] noncomputable def multiset.to_list {α : Type*} (s : multiset α) := classical.some (quotient.exists_rep s)

@[simp] lemma multiset.to_list_zero {α : Type*} : (multiset.to_list 0 : list α) = [] :=
  (multiset.coe_eq_zero _).1 (classical.some_spec (quotient.exists_rep multiset.zero))

lemma multiset.coe_to_list {α : Type*} (s : multiset α) : (s.to_list : multiset α) = s :=
classical.some_spec (quotient.exists_rep _)

lemma multiset.mem_to_list {α : Type*} (a : α) (s : multiset α) : a ∈ s.to_list ↔ a ∈ s :=
by rw [←multiset.mem_coe, multiset.coe_to_list]

/-
@[simp] lemma multiset.to_list_cons {α : Type*} (a : α) (as : list α) : 
  (multiset.to_list (a :: as) : list α) = [] := sorry
-/

theorem list.foldl_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) 
  (a : α) (l : list α) (h : ∀ x y, g (f x y) = f' (g x) (g y)) : 
  g (list.foldl f a l) = list.foldl f' (g a) (l.map g) :=
begin
  induction l generalizing a,
  { simp },
  { simp [list.foldl_cons, l_ih, h] }
end

lemma function.injective_foldl_comp {α : Type*} {l : list (α → α)} {f : α → α}
  (hl : ∀ f ∈ l, function.injective f) (hf : function.injective f): 
  function.injective (@list.foldl (α → α) (α → α) function.comp f l) :=
begin
  induction l generalizing f,
  { exact hf },
  { apply l_ih (λ _ h, hl _ (list.mem_cons_of_mem _ h)),
    apply function.injective_comp hf,
    apply hl _ (list.mem_cons_self _ _) }
end

#check 
 list.foldl_map' linear_map.to_fun linear_map.comp function.comp _ _ (λ _ _, rfl)

#check linear_map.ker_eq_bot'.symm.trans linear_map.ker_eq_bot

--set_option pp.implicit true

class algebraically_closed (α : Type*) extends discrete_field α :=
(exists_root {p : polynomial α} : 0 < polynomial.degree p → ∃ a, polynomial.is_root p a)

lemma field_to_ring_diamond (α : Type*) [h : field α] :
  @domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α h))
  = @comm_ring.to_ring α (@field.to_comm_ring α h) := 
rfl

lemma xxx (α : Type v) (β : Type w) 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) 
  (p : polynomial α) (h_p_ne_0 : p ≠ 0) (h_eval_p : (polynomial.eval₂ smul_id f p) v = 0) : 
  ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q : β →ₗ[α] β) : β → β) :=
begin
  rcases (factors_spec p h_p_ne_0).2 with ⟨c, hc⟩,
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  --have := hc,
--let :=  (λ (a : α), has_scalar.smul a (linear_map.id : β →ₗ[α] β)) ,
  --let smul := @has_scalar.smul _ _ (@mul_action.to_has_scalar _ _ _ (@distrib_mul_action.to_mul_action _ _ _ _ (@semimodule.to_distrib_mul_action _ _ _ _ (@module.to_semimodule _ _ _ _ (vector_space.to_module _ _))))),
  rw hc at h_eval_p,
  --rw eval₂_mul_noncomm at h_eval_p,
  have := @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ smul_id smul_id.is_semiring_hom f (factors p).prod (@has_inv.inv (units (polynomial α)) _ c) _,
  rw this at h_eval_p,
  rw polynomial.eq_C_of_degree_eq_zero (polynomial.degree_coe_units (c⁻¹)) at h_eval_p,
  rw polynomial.eval₂_C at h_eval_p,
  --dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul] at this,
  --rw linear_map.comp_apply at this_1,
  rw ← multiset.coe_to_list (factors p) at h_eval_p,
  rw multiset.coe_prod at h_eval_p,
  rw eval₂_prod_noncomm at h_eval_p,

  have h_noninj : ¬ function.injective ⇑(list.prod (list.map (λ p, polynomial.eval₂ smul_id f p) (multiset.to_list (factors p))) *
    smul_id (polynomial.coeff ↑c⁻¹ 0)),
  { rw ←linear_map.ker_eq_bot,
    rw linear_map.ker_eq_bot',
    rw classical.not_forall,
    use v, 
    rw not_imp,
    exact ⟨h_eval_p, hv⟩ },


  dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul] at h_noninj,

  dsimp only [list.prod, (*), mul_zero_class.mul, semiring.mul, ring.mul] at h_noninj,

  show ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q : β →ₗ[α] β) : β → β), --use .to_fun instead?
  { classical,
    by_contra h_contra,
    simp only [not_exists, not_not] at h_contra, 
    have h_factors_inj : ∀ g ∈ (factors p).to_list.map (λ q, (polynomial.eval₂ smul_id f q).to_fun),
        function.injective g,
    { intros g hg,
      rw list.mem_map at hg,
      rcases hg with ⟨q, hq₁, hq₂⟩,
      rw multiset.mem_to_list at hq₁,
      rw ←hq₂,
      exact h_contra q hq₁ },
    have := function.injective_foldl_comp (λ g, h_factors_inj g) function.injective_id,-- (begin intros f hf, convert h_contra _ _, sorry end),
    refine h_noninj (function.injective_comp _ _),
    { unfold_coes,
      rw list.foldl_map' linear_map.to_fun linear_map.comp function.comp _ _ (λ _ _, rfl),
      rw list.map_map,
      unfold function.comp,
      apply this },
    { intros x y hxy,
      simp at hxy,
      
      dunfold smul_id at hxy,
      rw [linear_map.smul_apply, linear_map.smul_apply] at hxy,
      have := congr_arg (has_scalar.smul (polynomial.coeff ↑c⁻¹ 0)⁻¹) hxy,
      rw [←mul_action.mul_smul, ←mul_action.mul_smul, 
          division_ring.inv_mul_cancel, one_smul, one_smul] at this,
      exact this,
      apply polynomial.coeff_coe_units_zero_ne_zero }
  },
end

lemma exists_eigenvector (α : Type v) (β : Type w) 
  [algebraically_closed α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) (h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v)) : 
  ∃ (x : β) (c : α), f x = c • x :=
begin
  have := λ h, h_lin_dep ((linear_independent_iff_eval₂ f v).2 h),
  haveI := classical.dec (∃ (x : polynomial α), ¬((polynomial.eval₂ smul_id f x) v = 0 → x = 0)),
  rcases not_forall.1 this with ⟨p, hp⟩,
  rcases not_imp.1 hp with ⟨h_eval_p, h_p_ne_0⟩,
  rcases (factors_spec p h_p_ne_0).2 with ⟨c, hc⟩,
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  --have := hc,
--let :=  (λ (a : α), has_scalar.smul a (linear_map.id : β →ₗ[α] β)) ,
  --let smul := @has_scalar.smul _ _ (@mul_action.to_has_scalar _ _ _ (@distrib_mul_action.to_mul_action _ _ _ _ (@semimodule.to_distrib_mul_action _ _ _ _ (@module.to_semimodule _ _ _ _ (vector_space.to_module _ _))))),
  rw hc at h_eval_p,
  --rw eval₂_mul_noncomm at h_eval_p,
  have := @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ smul_id smul_id.is_semiring_hom f (factors p).prod (@has_inv.inv (units (polynomial α)) _ c) _,
  rw this at h_eval_p,
  rw polynomial.eq_C_of_degree_eq_zero (polynomial.degree_coe_units (c⁻¹)) at h_eval_p,
  rw polynomial.eval₂_C at h_eval_p,
  --dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul] at this,
  --rw linear_map.comp_apply at this_1,
  rw ← multiset.coe_to_list (factors p) at h_eval_p,
  rw multiset.coe_prod at h_eval_p,
  rw eval₂_prod_noncomm at h_eval_p,

  have h_noninj : ¬ function.injective ⇑(list.prod (list.map (λ p, polynomial.eval₂ smul_id f p) (multiset.to_list (factors p))) *
    smul_id (polynomial.coeff ↑c⁻¹ 0)),
  { rw ←linear_map.ker_eq_bot,
    rw linear_map.ker_eq_bot',
    rw classical.not_forall,
    use v, 
    rw not_imp,
    exact ⟨h_eval_p, hv⟩ },


  dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul] at h_noninj,

  dsimp only [list.prod, (*), mul_zero_class.mul, semiring.mul, ring.mul] at h_noninj,

  have : ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q : β →ₗ[α] β) : β → β), --use .to_fun instead?
  { classical,
    by_contra h_contra,
    simp only [not_exists, not_not] at h_contra, 
    have h_factors_inj : ∀ g ∈ (factors p).to_list.map (λ q, (polynomial.eval₂ smul_id f q).to_fun),
        function.injective g,
    { intros g hg,
      rw list.mem_map at hg,
      rcases hg with ⟨q, hq₁, hq₂⟩,
      rw multiset.mem_to_list at hq₁,
      rw ←hq₂,
      exact h_contra q hq₁ },
    have := function.injective_foldl_comp (λ g, h_factors_inj g) function.injective_id,-- (begin intros f hf, convert h_contra _ _, sorry end),
    refine h_noninj (function.injective_comp _ _),
    { unfold_coes,
      rw list.foldl_map' linear_map.to_fun linear_map.comp function.comp _ _ (λ _ _, rfl),
      rw list.map_map,
      unfold function.comp,
      apply this },
    { intros x y hxy,
      simp at hxy,
      
      dunfold smul_id at hxy,
      rw [linear_map.smul_apply, linear_map.smul_apply] at hxy,
      have := congr_arg (has_scalar.smul (polynomial.coeff ↑c⁻¹ 0)⁻¹) hxy,
      rw [←mul_action.mul_smul, ←mul_action.mul_smul, 
          division_ring.inv_mul_cancel, one_smul, one_smul] at this,
      exact this,
      apply polynomial.coeff_coe_units_zero_ne_zero }
  }
end



lemma exists_eigenvector (α : Type v) (β : Type w) 
  [algebraically_closed α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) (h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v)) : 
  ∃ (x : β) (c : α), f x = c • x := sorry