/-

Algebraically closed fields.

We follow Axler's paper "Down with determinants!"
(https://www.maa.org/sites/default/files/pdf/awards/Axler-Ford-1996.pdf).
-/

import ring_theory.principal_ideal_domain
import missing_mathlib.data.polynomial
import missing_mathlib.data.multiset
import missing_mathlib.data.finsupp
import missing_mathlib.linear_algebra.dimension
import missing_mathlib.linear_algebra.finsupp
import missing_mathlib.algebra.group.units
import missing_mathlib.algebra.ring
import missing_mathlib.algebra.module
import missing_mathlib.algebra.group_power
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
  obtain ⟨c, hc⟩ : ∃ c, p * ↑c = multiset.prod (factors p) := (factors_spec p h_p_ne_0).2,
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

variables {α : Type v} {β : Type w} [decidable_eq β] [add_comm_group β]

-- section
-- set_option class.instance_max_depth 50
-- def eigenvector [discrete_field α] [vector_space α β] (f : β →ₗ[α] β) (μ : α) (x : β) : Prop := f x = μ • x
-- end

open polynomial

section
set_option class.instance_max_depth 50

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. (Axler's Theorem 2.1.) -/
lemma exists_eigenvector 
  [algebraically_closed α] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) (n : ℕ) (h_dim : dim α β = n) : 
  ∃ (x : β) (c : α), x ≠ 0 ∧ f x = c • x :=
begin
  have h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v),
  { intro h_lin_indep, 
    have h_le : cardinal.lift (cardinal.mk ℕ) ≤ cardinal.lift ↑n,
    { rw ←h_dim,
      exact linear_independent_le_dim h_lin_indep },
    have h_lt : cardinal.lift ↑n < cardinal.lift (cardinal.mk ℕ),
    { have := cardinal.lift_lt.2 (cardinal.nat_lt_omega n),
      rwa [cardinal.omega, cardinal.lift_lift] at this, },
      exact lt_irrefl _ (lt_of_le_of_lt h_le h_lt) },
  haveI := classical.dec (∃ (x : polynomial α), ¬(polynomial.eval₂ smul_id f x v = 0 → x = 0)),
  obtain ⟨p, hp⟩ : ∃ p, ¬(eval₂ smul_id f p v = 0 → p = 0),
  { exact not_forall.1 (λ h, h_lin_dep ((linear_independent_iff_eval₂ f v).2 h)) },
  obtain ⟨h_eval_p, h_p_ne_0⟩ : eval₂ smul_id f p v = 0 ∧ p ≠ 0 := not_imp.1 hp,
  obtain ⟨q, hq_mem, hq_noninj⟩ : ∃ q ∈ factors p, ¬function.injective ⇑(eval₂ smul_id f q), 
  { exact exists_noninjective_factor_of_eval₂_0 f v hv p h_p_ne_0 h_eval_p },
  have h_q_ne_0 : q ≠ 0 := ne_0_of_mem_factors h_p_ne_0 hq_mem,
  have h_deg_q : q.degree = 1 := polynomial.degree_eq_one_of_irreducible h_q_ne_0 
    ((factors_spec p h_p_ne_0).1 q hq_mem),
  have h_q_eval₂ : polynomial.eval₂ smul_id f q = q.leading_coeff • f + smul_id (q.coeff 0),
  { rw [polynomial.eq_X_add_C_of_degree_eq_one h_deg_q],
    simp [eval₂_mul_noncomm smul_id f _ _ algebra.commutes',
        leading_coeff_C_add_X _ _ (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h))],
    refl },
  obtain ⟨x, hx₁, hx₂⟩ : ∃ (x : β), eval₂ smul_id f q x = 0 ∧ ¬x = 0,
  { rw [←linear_map.ker_eq_bot, linear_map.ker_eq_bot', classical.not_forall] at hq_noninj,
    simpa only [not_imp] using hq_noninj },
  have h_fx_x_lin_dep: leading_coeff q • f x + coeff q 0 • x = 0,
  { rw h_q_eval₂ at hx₁,
    dsimp [smul_id] at hx₁,
    exact hx₁ },
  show ∃ (x : β) (c : α), x ≠ 0 ∧ f x = c • x,
  { use x, 
    use -(coeff q 0 / q.leading_coeff),
    refine ⟨hx₂, _⟩,
    rw neg_smul,
    have : (leading_coeff q)⁻¹ • leading_coeff q • f x = (leading_coeff q)⁻¹ • -(coeff q 0 • x) := 
      congr_arg (λ x, (leading_coeff q)⁻¹ • x) (add_eq_zero_iff_eq_neg.1 h_fx_x_lin_dep),
    simpa [smul_smul, inv_mul_cancel (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h)), 
      mul_comm _ (coeff q 0), div_eq_mul_inv.symm] }
end
end

section
set_option class.instance_max_depth 50

/-- Non-zero eigenvectors corresponding to distinct eigenvalues of a linear operator are
linearly independent (Axler's Proposition 2.2) -/
lemma eigenvectors_linear_independent [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (μs : set α) (xs : μs → β) 
  (h_xs_nonzero : ∀ a, xs a ≠ 0) (h_eigenvec : ∀ μ : μs, f (xs μ) = (μ : α) • xs μ): 
  linear_independent α xs := 
begin
  rw linear_independent_iff,
  intros l hl,
  induction h_l_support : l.support using finset.induction with μ₀ l_support' hμ₀ ih generalizing l,
  { exact finsupp.support_eq_empty.1 h_l_support },
  { let l'_f := (λ μ : μs, (↑μ - ↑μ₀) * l μ),
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
    have total_l' : (@linear_map.to_fun α (finsupp μs α) β _ _ _ (finsupp.module μs α) _ (finsupp.total μs β α xs)) l' = 0,
    { let g := f - smul_id μ₀, 
      have h_gμ₀: g (l μ₀ • xs μ₀) = 0, 
        by rw [linear_map.map_smul, linear_map.sub_apply, h_eigenvec, smul_id_apply, sub_self, smul_zero],
      have h_useless_filter : finset.filter (λ (a : μs), l'_f a ≠ 0) l_support' = l_support',
      { convert @finset.filter_congr _ _ _ (classical.dec_pred _) (classical.dec_pred _) _ _,
        { apply finset.filter_true.symm },
        exact λ μ hμ, iff_of_true ((h_l_support' μ).2 hμ) true.intro },
      have bodies_eq : ∀ (μ : μs), l'_f μ • xs μ = g (l μ • xs μ), 
      { intro μ,
        dsimp only [g, l'_f],
        rw [linear_map.map_smul, linear_map.sub_apply, h_eigenvec, smul_id_apply, ←sub_smul, smul_smul],
        ac_refl },
      have := finsupp.total_on_finset l_support' l'_f xs _,
      unfold_coes at this,
      rw [this, ←linear_map.map_zero g,
          ←congr_arg g hl, finsupp.total_apply, finsupp.sum, linear_map.map_sum, h_l_support,
          finset.sum_insert hμ₀, h_gμ₀, zero_add, h_useless_filter],
      simp only [bodies_eq] },
    have h_l'_support_eq : l'.support = l_support',
    { dsimp only [l'],
      ext μ,
      rw finsupp.on_finset_mem_support l_support' l'_f _ μ,
      by_cases h_cases: μ ∈ l_support',
      { refine iff_of_true _ h_cases,
        exact (h_l_support' μ).2 h_cases },
      { refine iff_of_false _ h_cases,
        rwa not_iff_not.2 (h_l_support' μ) } },
    have l'_eq_0 : l' = 0 := ih l' total_l' h_l'_support_eq,
    
    have h_mul_eq_0 : ∀ μ : μs, (↑μ - ↑μ₀) * l μ = 0,
    { intro μ,
      calc (↑μ - ↑μ₀) * l μ = l' μ : rfl
      ... = 0 : by { rw [l'_eq_0], refl } },

    have h_lμ_eq_0 : ∀ μ : μs, μ ≠ μ₀ → l μ = 0,
    { intros μ hμ,
      apply classical.or_iff_not_imp_left.1 (mul_eq_zero.1 (h_mul_eq_0 μ)),
      rwa [sub_eq_zero, ←subtype.coe_ext] },

    have h_sum_l_support'_eq_0 : finset.sum l_support' (λ (μ : ↥μs), l μ • xs μ) = 0,
    { rw ←finset.sum_const_zero,
      apply finset.sum_congr rfl,
      intros μ hμ,
      rw h_lμ_eq_0,
      apply zero_smul,
      intro h,
      rw h at hμ,
      contradiction },

    have : l μ₀ = 0,
    { rw [finsupp.total_apply, finsupp.sum, h_l_support, 
          finset.sum_insert hμ₀, h_sum_l_support'_eq_0, add_zero] at hl,
      by_contra h,
      exact h_xs_nonzero μ₀ ((vector_space.smul_neq_zero (xs μ₀) h).1 hl) },

    show l = 0,
    { ext μ,
      by_cases h_cases : μ = μ₀,
      { rw h_cases, 
        assumption },
      exact h_lμ_eq_0 μ h_cases } }
end

def generalized_eigenvector [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (k : ℕ) (μ : α) (x : β) : Prop := ((f - smul_id μ) ^ k) x = 0

lemma generalized_eigenvector_zero_beyond [discrete_field α] [vector_space α β] 
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvector f k μ x) :
  ∀ m : ℕ, k ≤ m → ((f - smul_id μ) ^ m) x = 0 :=
begin
  intros m hm,
  rw ←pow_eq_pow_sub_mul _ hm,
  change ((f - smul_id μ) ^ (m - k)) (((f - smul_id μ) ^ k) x) = 0,
  unfold generalized_eigenvector at h,
  rw [h, linear_map.map_zero]
end

lemma exp_ne_zero_of_generalized_eigenvector_ne_zero [discrete_field α] [vector_space α β] 
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvector f k μ x) 
  (hx : x ≠ 0) : k ≠ 0 :=
begin
  contrapose hx,
  rw not_not at hx ⊢,
  rwa [hx, generalized_eigenvector, pow_zero] at h,
end

/-- The set of generalized eigenvectors of f corresponding to an eigenvalue μ
    equals the kernel of (f - smul_id μ) ^ n, where n is the dimension of 
    the vector space (Axler's Lemma 3.1). -/
lemma generalized_eigenvector_dim [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (μ : α) (x : β) (n : ℕ) (h_dim : dim α β = n) (hx : x ≠ 0): 
  (∃ k : ℕ, generalized_eigenvector f k μ x) ↔ ((f - smul_id μ) ^ n) x = 0 :=
begin
  split,
  { show (∃ (k : ℕ), generalized_eigenvector f k μ x) → ((f - smul_id μ) ^ n) x = 0,
    intro h_exists_eigenvec,
    let k := @nat.find (λ k : ℕ, generalized_eigenvector f k μ x) (classical.dec_pred _) h_exists_eigenvec,
    let z := (λ i : fin k, ((f - smul_id μ) ^ (i : ℕ)) x),

    have h_lin_indep : linear_independent α z,
    { rw linear_independent_iff,
      intros l hl,
      ext i,
      induction h_i_val : i.val using nat.strong_induction_on with i_val ih generalizing i,
      simp only [h_i_val.symm] at *,
      clear h_i_val i_val,

      have h_zero_of_lt : ∀ j, j < i → ((f - smul_id μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        simp [ih j hj j rfl] }, 

      have h_zero_beyond_k : ∀ m, k ≤ m → ((f - smul_id μ) ^ m) x = 0,
      { apply generalized_eigenvector_zero_beyond,
        apply (@nat.find_spec (λ k : ℕ, generalized_eigenvector f k μ x) (classical.dec_pred _) h_exists_eigenvec) },

      have h_zero_of_gt : ∀ j, j > i → ((f - smul_id μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        dsimp only [z],
        rw [linear_map.map_smul],
        change l j • ((f - smul_id μ) ^ (k - i.val - 1) * ((f - smul_id μ) ^ ↑j)) x = 0,
        rw [←pow_add, h_zero_beyond_k, smul_zero],
        rw [nat.sub_sub, ←nat.sub_add_comm (nat.succ_le_of_lt i.2)],
        apply nat.le_sub_right_of_add_le,
        apply nat.add_le_add_left,
        rw ←nat.lt_iff_add_one_le,
        rw gt_from_lt at hj,
        unfold_coes,
        change i.val < (j : ℕ),
        exact hj }, 

      have h_zero_of_ne : ∀ j, j ≠ i → ((f - smul_id μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        cases lt_or_gt_of_ne hj with h_lt h_gt,
        apply h_zero_of_lt j h_lt,
        apply h_zero_of_gt j h_gt }, 

      have h_zero_of_not_support : i ∉ l.support → ((f - smul_id μ) ^ (k - i.val - 1)) (l i • z i) = 0,
      { intros hi,
        rw [finsupp.mem_support_iff, not_not] at hi,
        rw [hi, zero_smul, linear_map.map_zero] },

      have h_l_smul_pow_k_sub_1 : l i • (((f - smul_id μ) ^ (k - 1)) x) = 0,
      { have h_k_sub_1 : k - i.val - 1 + i.val = k - 1,
        { rw ←nat.sub_add_comm,
          { rw nat.sub_add_cancel, 
            rw ge_from_le,
            apply le_of_lt i.2 },
          { apply nat.le_sub_left_of_add_le,
            apply nat.succ_le_of_lt i.2 } },
        rw [←h_k_sub_1, pow_add],
        let g := (f - smul_id μ) ^ (k - i.val - 1),
        rw [finsupp.total_apply, finsupp.sum] at hl,
        have := congr_arg g hl,
        rw [linear_map.map_sum, linear_map.map_zero g] at this,
        dsimp only [g] at this,
        rw finset.sum_eq_single i (λ j _, h_zero_of_ne j) h_zero_of_not_support at this,
        simp only [linear_map.map_smul, z] at this,
        apply this },

      have h_pow_k_sub_1 : ((f - smul_id μ) ^ (k - 1)) x ≠ 0 := 
        @nat.find_min (λ k : ℕ, generalized_eigenvector f k μ x) (classical.dec_pred _) h_exists_eigenvec _
            (nat.sub_lt (nat.lt_of_le_of_lt (nat.zero_le _) i.2) nat.zero_lt_one),
      
      show l i = 0,
      { contrapose h_pow_k_sub_1 with h_li_ne_0,
        rw not_not,
        rw ← vector_space.smul_neq_zero _ h_li_ne_0,
        exact h_l_smul_pow_k_sub_1 } },

    show ((f - smul_id μ) ^ n) x = 0,
    { apply generalized_eigenvector_zero_beyond 
        (@nat.find_spec (λ k : ℕ, generalized_eigenvector f k μ x) (classical.dec_pred _) h_exists_eigenvec),
      rw [←cardinal.nat_cast_le, ←cardinal.lift_mk_fin _, ←h_dim, ←cardinal.lift_le, cardinal.lift_lift],
      apply h_lin_indep.le_lift_dim} },

  { show ((f - smul_id μ) ^ n) x = 0 → (∃ (k : ℕ), generalized_eigenvector f k μ x),
    exact λh, ⟨_, h⟩, }
end



lemma generalized_eigenvector_span_aux [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (n : ℕ) (p : submodule α β) (h_dim : dim α p = n) : 
  p ≤ submodule.span α {x | ∃ k μ, generalized_eigenvector f k μ x} :=
begin
  induction n generalizing p,
  { rw submodule.bot_of_dim_zero p h_dim,
    exact lattice.bot_le },
  { obtain ⟨ x⟩ : _ := exists_eigenvector f sorry,
    let g := (f - smul_id μ₀) ^ n }
end

/-- The generalized eigenvectors of f span the vectorspace β. (Axler's Proposition 3.4). -/
lemma generalized_eigenvector_span [discrete_field α] [vector_space α β] 
  (f : β →ₗ[α] β) (n : ℕ) (h_dim : dim α β = n) : 
  submodule.span α {x | ∃ k μ, generalized_eigenvector f k μ x} = ⊤ :=
lattice.top_le_iff.1 (generalized_eigenvector_span_aux f n ⊤ (by rwa dim_top))

end

end eigenvector