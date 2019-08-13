import ring_theory.principal_ideal_domain
import missing_mathlib.data.polynomial
import missing_mathlib.data.multiset
import missing_mathlib.data.finsupp
import missing_mathlib.linear_algebra.dimension
import missing_mathlib.linear_algebra.finsupp
import missing_mathlib.algebra.group.units
import missing_mathlib.algebra.ring
import missing_mathlib.data.list.basic
import analysis.complex.polynomial
import eigenvectors.smul_id

universes u v w

/-- algebraically closed field -/
class algebraically_closed (α : Type*) extends discrete_field α :=
(exists_root {p : polynomial α} : 0 < polynomial.degree p → ∃ a, polynomial.is_root p a)

noncomputable instance complex.algebraically_closed : algebraically_closed ℂ := {
  exists_root := (λ p hp, complex.exists_root hp)
}

section polynomial
variables {α : Type*} [algebraically_closed α]
open polynomial

lemma polynomial.degree_eq_one_of_irreducible {p : polynomial α} (h_nz : p ≠ 0) (hp : irreducible p) : 
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

-- TODO: move ?
lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ smul_id f p v = 0 → p = 0 :=
by simp only [linear_independent_iff, finsupp.total_apply, finsupp_sum_eq_eval₂]; refl

open vector_space principal_ideal_domain

lemma ne_0_of_mem_factors {α : Type v} [discrete_field α] {p q : polynomial α} 
  (hp : p ≠ 0) (hq : q ∈ factors p) : q ≠ 0 :=
begin
  intro h_q_eq_0,
  rw h_q_eq_0 at hq,
  apply hp ((associated_zero_iff_eq_zero p).1 _),
  rw ←multiset.prod_eq_zero hq,
  apply (factors_spec p hp).2
end

lemma exists_noninjective_factor_of_eval₂_0 {α : Type v} {β : Type w} 
  [discrete_field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) 
  (p : polynomial α) (h_p_ne_0 : p ≠ 0) (h_eval_p : (polynomial.eval₂ smul_id f p) v = 0) : 
  ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id f q : β →ₗ[α] β) : β → β) :=
begin
  rcases (factors_spec p h_p_ne_0).2 with ⟨c, hc⟩,
  have smul_id_comm : ∀ (a : α) (b : β →ₗ[α] β), b * smul_id a = smul_id a * b := algebra.commutes',
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  rw [hc,
    @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ smul_id smul_id.is_semiring_hom f (factors p).prod 
      (@has_inv.inv (units (polynomial α)) _ c) algebra.commutes',
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

section eigenvector

variables (α : Type v) (β : Type w) [decidable_eq β] [add_comm_group β]

-- section
-- set_option class.instance_max_depth 50
-- def eigenvector [discrete_field α] [vector_space α β] (f : β →ₗ[α] β) (μ : α) (x : β) : Prop := f x = μ • x
-- end

open polynomial

section
set_option class.instance_max_depth 50
lemma exists_eigenvector 
  [algebraically_closed α] [vector_space α β]
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

section
set_option class.instance_max_depth 50

lemma eigenvectors_linear_independent [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (μs : set α) (xs : μs → β) 
  (h_xs_nonzero : ∀ a, xs a ≠ 0) (h_eigenvec : ∀ μ : μs, f (xs μ) = (μ : α) • xs μ): 
  linear_independent α xs := 
begin
  rw linear_independent_iff,
  intros l hl,
  induction h_l_support : l.support using finset.induction with μ₀ l_support' hμ₀ ih generalizing l,
  { exact finsupp.support_eq_empty.1 h_l_support },
  { 
    let l'_f := (λ μ : μs, (↑μ - ↑μ₀) * l μ),
    --let l'_f := (λ μ : (↑(l_support') : set μs), (↑μ - ↑μ₀) * l μ),
    have h_l_support' : ∀ (μ : μs), l'_f μ ≠ 0 ↔ μ ∈ l_support',
    { intros μ,
      dsimp only [l'_f],
      rw [mul_ne_zero_iff, sub_ne_zero, ←not_iff_not, not_and_distrib, not_not, not_not, ←subtype.coe_ext],
      split,
      { intro h,
        cases h,
        { rwa h }, 
        { intro h_mem_l_support',
          apply finsupp.mem_support_iff.1 _ h,
          rw h_l_support,
          apply finset.subset_insert _ _ h_mem_l_support' } },
      { intro h, 
        apply (@or_iff_not_imp_right _ _ (classical.dec _)).2,
        intro hlμ,
        have := finsupp.mem_support_iff.2 hlμ,
        rw [h_l_support, finset.mem_insert] at this,
        cc } },
    let l' : μs →₀ α := finsupp.on_finset l_support' l'_f (λ μ, (h_l_support' μ).1),
    have l'_eq_0 : l' = 0,
    { apply ih l', 
      show l'.support = l_support',
      { dsimp only [l'],
        ext μ,
        rw finsupp.on_finset_mem_support l_support' l'_f _ μ,
        by_cases h_cases: μ ∈ l_support',
        { refine iff_of_true _ h_cases,
          exact (h_l_support' μ).2 h_cases },
        { refine iff_of_false _ h_cases,
          rwa not_iff_not.2 (h_l_support' μ) } },
      --show ⇑(finsupp.total ↥μs β α xs) l' = 0,
      { dsimp only [l'],
        rw finsupp.total_on_finset l_support' l'_f xs _,
        let g := f - smul_id μ₀, 
        have := congr_arg g hl,
        rw linear_map.map_zero at this,
        rw ←this,
        rw finsupp.total_apply,
        unfold finsupp.sum,
        rw linear_map.map_sum,
    }, },
      


    --let l' : μs →₀ α := finsupp.map l  sorry, 
    }, sorry
    --have h_finsupp: ∀ (a : μs), a ∈ l_support' ↔ l'.support,
    --{ sorry },
  -- have : ∀ μ₀ : μs, l μ₀ = 0,
  -- { intro μ₀,
  --   let μs' := (l.support.erase μ₀).val,
  --   let p_factors := μs'.map (λ μ : μs, X - C (↑μ : α)),
  --   let p := p_factors.prod,
  --   let g := eval₂ smul_id f p,
  --   have := eval₂_prod_noncomm _ algebra.commutes' f p_factors.to_list,
  -- },
end
end

end eigenvector