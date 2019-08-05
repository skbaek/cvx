import ring_theory.principal_ideal_domain
import linear_algebra.dimension
import data.polynomial

universes u v w

class algebraically_closed (α : Type*) extends discrete_field α :=
(exists_root {p : polynomial α} : 0 < polynomial.degree p → ∃ a, polynomial.is_root p a)

namespace polynomial
variables {α : Type*} [algebraically_closed α]
open polynomial
-- TODO: move
lemma not_is_unit_X_sub_C {α : Type*} [integral_domain α] [decidable_eq α]:  
  ∀ a : α, ¬ is_unit (X - C a) :=
begin intros a ha, 
  let ha' := degree_eq_zero_of_is_unit ha,
  rw [degree_X_sub_C] at ha',
  apply nat.zero_ne_one (option.injective_some _ ha'.symm)
end

lemma degree_eq_one_of_irreducible {p : polynomial α} (h_nz : p ≠ 0) (hp : irreducible p) : 
  p.degree = 1 :=
begin
  have h_0_le_deg_p : 0 < degree p := degree_pos_of_ne_zero_of_nonunit h_nz hp.1,
  cases (algebraically_closed.exists_root h_0_le_deg_p) with a ha,
  have h_p_eq_mul : (X - C a) * (p / (X - C a)) = p,
  { apply mul_div_eq_iff_is_root.2 ha },
  have h_unit : is_unit (p / (X - C a)),
  from or.resolve_left 
        (hp.2 (X - C a) (p / (X - C a)) h_p_eq_mul.symm) 
        (polynomial.not_is_unit_X_sub_C a),
  show degree p = 1,
  { rw [←h_p_eq_mul, degree_mul_eq, degree_X_sub_C, degree_eq_zero_of_is_unit h_unit], 
    simp }
end
end polynomial

section smul_id
variables {α : Type v} {β : Type w}

def smul_id [comm_ring α] [add_comm_group β] [module α β] (a : α) : β →ₗ[α] β := a • linear_map.id

instance smul_id.is_semiring_hom [comm_ring α] [add_comm_group β] [module α β] : 
is_semiring_hom (smul_id : α → β →ₗ[α] β) := {
  map_zero := begin unfold smul_id, ext, simp end,
  map_one := begin unfold smul_id, ext, simp end,
  map_add := begin unfold smul_id, simp [add_smul] end,
  map_mul := begin unfold smul_id, intros, ext, simp [mul_smul] end
}

instance smul_id.is_ring_hom [comm_ring α] [add_comm_group β] [module α β] : 
is_ring_hom (smul_id : α → β →ₗ[α] β) := {
  map_one := smul_id.is_semiring_hom.map_one,
  map_add := smul_id.is_semiring_hom.map_add,
  map_mul := smul_id.is_semiring_hom.map_mul
}

instance [comm_ring α] [add_comm_group β] [module α β] : algebra α (β →ₗ[α] β) := 
{ to_fun := smul_id,
  commutes' := 
  begin 
    intros a f, 
    unfold smul_id, 
    ext, 
    simp, 
  end,
  smul_def' := 
  begin
    intros a f, 
    unfold smul_id, 
    ext, 
    simp, 
  end
}

end smul_id

section eval₂
--TODO: move
variables {α : Type u} {β : Type v} [comm_ring α] [decidable_eq α] [semiring β]
variables (f : α → β) [is_semiring_hom f] (x : β) (p q : polynomial α)
open is_semiring_hom
open polynomial finsupp finset

lemma eval₂_mul_noncomm (hf : ∀ b a, a * f b = f b * a) : 
  (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
begin
  dunfold eval₂,
  rw [mul_def, finsupp.sum_mul _ p], simp only [finsupp.mul_sum _ q], rw [sum_sum_index],
  { apply sum_congr rfl, assume i hi, dsimp only, rw [sum_sum_index],
    { apply sum_congr rfl, assume j hj, dsimp only,
      rw [sum_single_index, map_mul f, pow_add],
      { rw [mul_assoc, ←mul_assoc _ (x ^ i), ← hf _ (x ^ i)], 
        simp only [mul_assoc] },
      { rw [map_zero f, zero_mul] } },
    { intro, rw [map_zero f, zero_mul] },
    { intros, rw [map_add f, add_mul] } },
  { intro, rw [map_zero f, zero_mul] },
  { intros, rw [map_add f, add_mul] }
end

end eval₂

-- TODO: move ?
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

-- TODO: move ?
lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ smul_id f p v = 0 → p = 0 :=
by simp only [linear_independent_iff, finsupp.total_apply, finsupp_total_eq_eval₂]; refl


open vector_space principal_ideal_domain

-- TODO: move to dimension.lean
lemma linear_independent_le_dim {α : Type u} {β : Type v} {ι : Type w}
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β] [decidable_eq ι]
  {v : ι → β} (hv : @linear_independent _ α _ v _ _ _ (@comm_ring.to_ring _ (field.to_comm_ring _)) _ _) : 
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) : 
     (cardinal.mk_range_eq_of_inj (linear_independent.injective (field.zero_ne_one α) hv)).symm
  ... = cardinal.lift.{v w} (dim α (submodule.span α (set.range v))) : by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (dim α β) : cardinal.lift_le.2 (dim_submodule_le (submodule.span α _))

-- TODO: move
lemma eval₂_prod_noncomm {α β : Type*} [comm_ring α] [decidable_eq α] [semiring β]
  (f : α → β) [is_semiring_hom f] (hf : ∀ b a, a * f b = f b * a) (x : β)
  (ps : list (polynomial α)) : 
  polynomial.eval₂ f x ps.prod = (ps.map (λ p, (polynomial.eval₂ f x p))).prod :=
begin 
  induction ps,
  simp,
  simp [eval₂_mul_noncomm f _ _ _ hf, ps_ih] {contextual := tt}
end

lemma powers_linear_dependent_of_dim_finite (α : Type v) (β : Type w) 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (h_dim : dim α β < cardinal.omega) (v : β) : 
  ¬ linear_independent α (λ n : ℕ, (f ^ n) v) :=
begin
  intro hw,
  apply not_lt_of_le _ h_dim,
  rw [← cardinal.lift_id (dim α β), cardinal.lift_umax.{w 0}],
  apply linear_independent_le_dim hw
end


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

--set_option pp.implicit true

lemma exists_noninjective_factor_of_eval₂_0 {α : Type v} {β : Type w} 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) 
  (p : polynomial α) (h_p_ne_0 : p ≠ 0) (h_eval_p : (polynomial.eval₂ smul_id f p) v = 0) : 
  ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q : β →ₗ[α] β) : β → β) :=
begin
  rcases (factors_spec p h_p_ne_0).2 with ⟨c, hc⟩,
  have smul_id_comm : ∀ (a : α) (b : β →ₗ[α] β), b * smul_id a = smul_id a * b,
  { intros a b, 
    apply algebra.commutes' a b },
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  rw [hc,
    @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ smul_id smul_id.is_semiring_hom f (factors p).prod 
      (@has_inv.inv (units (polynomial α)) _ c) smul_id_comm,
    polynomial.eq_C_of_degree_eq_zero (polynomial.degree_coe_units (c⁻¹)),
    polynomial.eval₂_C, ← multiset.coe_to_list (factors p), multiset.coe_prod,
    eval₂_prod_noncomm _ smul_id_comm] at h_eval_p,
  have h_noninj : ¬ function.injective ⇑(list.prod 
    (list.map (λ p, polynomial.eval₂ (smul_id : α → β →ₗ[α] β) f p) (multiset.to_list (factors p))) *
    smul_id (polynomial.coeff ↑c⁻¹ 0)),
  { rw [←linear_map.ker_eq_bot, linear_map.ker_eq_bot', classical.not_forall],
    use v, 
    exact not_imp.2 (and.intro h_eval_p hv) },
  show ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q).to_fun),
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
    refine h_noninj (function.injective_comp _ _),
    { unfold_coes,
      dsimp only [list.prod, (*), mul_zero_class.mul, semiring.mul, ring.mul],
      rw list.foldl_map' linear_map.to_fun linear_map.comp function.comp _ _ (λ _ _, rfl),
      rw list.map_map,
      unfold function.comp,
      apply function.injective_foldl_comp (λ g, h_factors_inj g) function.injective_id },
    { rw [←linear_map.ker_eq_bot, smul_id, linear_map.ker_smul, linear_map.ker_id],
      apply polynomial.coeff_coe_units_zero_ne_zero }
  }
end


lemma multiset.prod_eq_zero {α : Type v} [comm_semiring α] {s : multiset α} (h : (0 : α) ∈ s) : 
  multiset.prod s = 0 :=
begin
  rcases multiset.exists_cons_of_mem h with ⟨s', hs'⟩,
  simp [hs', multiset.prod_cons]
end

lemma ne_0_of_mem_factors {α : Type v} [discrete_field α] {p q : polynomial α} 
  (hp : p ≠ 0) (hq : q ∈ factors p) : q ≠ 0 :=
begin
  intro h_q_eq_0,
  rw h_q_eq_0 at hq,
  apply hp ((associated_zero_iff_eq_zero p).1 _),
  rw ←multiset.prod_eq_zero hq,
  apply (factors_spec p hp).2
end

open polynomial

lemma leading_coeff_C_add_X {α : Type v} [integral_domain α] [decidable_eq α] (a b : α) (hb : b ≠ 0): 
  leading_coeff (C a + C b * X) = b :=
begin
  rw leading_coeff_add_of_degree_lt,
  { simp },
  { simp [degree_C hb],
    apply lt_of_le_of_lt degree_C_le (with_bot.coe_lt_coe.2 zero_lt_one)},
end

section
set_option class.instance_max_depth 50
lemma exists_eigenvector (α : Type v) (β : Type w) 
  [algebraically_closed α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) (h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v)) : 
  ∃ (x : β) (c : α), x ≠ 0 ∧ f x = c • x :=
begin
  have := λ h, h_lin_dep ((linear_independent_iff_eval₂ f v).2 h),
  haveI := classical.dec (∃ (x : polynomial α), ¬((polynomial.eval₂ smul_id f x) v = 0 → x = 0)),
  rcases not_forall.1 this with ⟨p, hp⟩,
  rcases not_imp.1 hp with ⟨h_eval_p, h_p_ne_0⟩,
  rcases exists_noninjective_factor_of_eval₂_0 f v hv p h_p_ne_0 h_eval_p with ⟨q, hq_mem, hq_noninj⟩,
  have h_q_ne_0 : q ≠ 0 := ne_0_of_mem_factors h_p_ne_0 hq_mem,
  have h_deg_q : q.degree = 1 := polynomial.degree_eq_one_of_irreducible h_q_ne_0 
    ((factors_spec p h_p_ne_0).1 q hq_mem),
  have h_q_eval₂ : polynomial.eval₂ smul_id f q = q.leading_coeff • f + smul_id (q.coeff 0),
  { rw [polynomial.eq_X_add_C_of_degree_eq_one h_deg_q],
    simp [eval₂_mul_noncomm smul_id f _ _ algebra.commutes',
        leading_coeff_C_add_X _ _ (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h))],
    refl },
  rw [←linear_map.ker_eq_bot, linear_map.ker_eq_bot', classical.not_forall] at hq_noninj,
  simp only [not_imp] at hq_noninj,
  rcases hq_noninj with ⟨x, hx₁, hx₂⟩,
  use x, 
  use -(coeff q 0 / q.leading_coeff),
  refine ⟨hx₂, _⟩,
  have h_fx_x_lin_dep: leading_coeff q • f x + coeff q 0 • x = 0,
  { rw h_q_eval₂ at hx₁,
    dsimp [smul_id] at hx₁,
    exact hx₁ },
  show f x = -(coeff q 0 / leading_coeff q) • x,
  { rw neg_smul,
    have : (leading_coeff q)⁻¹ • leading_coeff q • f x = (leading_coeff q)⁻¹ • -(coeff q 0 • x) := 
      congr_arg (λ x, (leading_coeff q)⁻¹ • x) (add_eq_zero_iff_eq_neg.1 h_fx_x_lin_dep),
    simpa [smul_smul, inv_mul_cancel (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h)), 
      mul_comm _ (coeff q 0), div_eq_mul_inv.symm] }
end
end