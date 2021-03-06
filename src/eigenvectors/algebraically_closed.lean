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
import missing_mathlib.linear_algebra.finite_dimensional
import missing_mathlib.linear_algebra.finsupp
import missing_mathlib.algebra.group.units
import missing_mathlib.algebra.ring
import missing_mathlib.algebra.module
import missing_mathlib.algebra.group_power
import missing_mathlib.data.list.basic
import missing_mathlib.set_theory.cardinal
import missing_mathlib.ring_theory.algebra
import analysis.complex.polynomial
import eigenvectors.smul_id

universes u v w

/-- algebraically closed field -/
class algebraically_closed (α : Type*) extends field α :=
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
        polynomial.not_is_unit_X_sub_C,
  show degree p = 1,
  { rw [←h_p_eq_mul, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit h_unit], 
    simp }
end
end polynomial

-- TODO: move ?
lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ smul_id_ring_hom f p v = 0 → p = 0 :=
begin
  rw linear_independent_iff,
  simp only [finsupp.total_apply],
  simp only [finsupp_sum_eq_eval₂],
  simp only [smul_id_ring_hom, smul_id, linear_independent_iff, finsupp.total_apply, finsupp_sum_eq_eval₂],
  refl
end

open vector_space principal_ideal_ring

lemma ne_0_of_mem_factors {α : Type v} [field α] {p q : polynomial α} 
  (hp : p ≠ 0) (hq : q ∈ factors p) : q ≠ 0 :=
begin
  intro h_q_eq_0,
  rw h_q_eq_0 at hq,
  apply hp ((associated_zero_iff_eq_zero p).1 _),
  rw ←multiset.prod_eq_zero hq,
  apply (factors_spec p hp).2
end

lemma exists_noninjective_factor_of_eval₂_0 {α : Type v} {β : Type w} 
  [field α] [decidable_eq α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) 
  (p : polynomial α) (h_p_ne_0 : p ≠ 0) (h_eval_p : (polynomial.eval₂ smul_id_ring_hom f p) v = 0) : 
  ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id_ring_hom f q : β →ₗ[α] β) : β → β) :=
begin
  obtain ⟨c, hc⟩ := (factors_spec p h_p_ne_0).2,
  have smul_id_comm : ∀ (a : α) (b : β →ₗ[α] β), smul_id a * b = b * smul_id a := algebra.commutes',
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  rw [hc,
    @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ smul_id_ring_hom f (factors p).prod 
      (@has_inv.inv (units (polynomial α)) _ c) (λ x y, ( algebra.commutes' x y).symm),
    polynomial.eq_C_of_degree_eq_zero (polynomial.degree_coe_units (c⁻¹)),
    polynomial.eval₂_C, ← multiset.coe_to_list (factors p), multiset.coe_prod,
    eval₂_prod_noncomm smul_id_ring_hom (λ x y, (smul_id_comm x y).symm)] at h_eval_p,
  have h_noninj : ¬ function.injective ⇑(list.prod 
    (list.map (λ p, polynomial.eval₂ smul_id_ring_hom f p) (multiset.to_list (factors p))) *
    smul_id (polynomial.coeff ↑c⁻¹ 0)),
  { rw [←linear_map.ker_eq_bot, linear_map.ker_eq_bot', classical.not_forall],
    use v, 
    exact not_imp.2 (and.intro h_eval_p hv) },
  show ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ smul_id_ring_hom f q).to_fun),
  { classical,
    by_contra h_contra,
    simp only [not_exists, not_not] at h_contra, 
    have h_factors_inj : ∀ g ∈ (factors p).to_list.map (λ q, (polynomial.eval₂ smul_id_ring_hom f q).to_fun),
        function.injective g,
    { intros g hg,
      rw list.mem_map at hg,
      rcases hg with ⟨q, hq₁, hq₂⟩,
      rw multiset.mem_to_list at hq₁,
      rw ←hq₂,
      exact h_contra q hq₁ },
    refine h_noninj (function.injective.comp _ _),
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
open finite_dimensional

section
set_option class.instance_max_depth 50

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. (Axler's Theorem 2.1.) -/
lemma exists_eigenvector 
  [algebraically_closed α] [decidable_eq α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (hex : ∃ v : β, v ≠ 0) : 
  ∃ (x : β) (c : α), x ≠ 0 ∧ f x = c • x :=
begin
  obtain ⟨v, hv⟩ : ∃ v : β, v ≠ 0 := hex,
  have h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v),
  { intro h_lin_indep, 
    have : cardinal.mk ℕ < cardinal.omega, 
      by apply (lt_omega_of_linear_independent h_lin_indep),
    have := cardinal.lift_lt.2 this,
    rw [cardinal.omega, cardinal.lift_lift] at this,
    apply lt_irrefl _ this, },
  haveI := classical.dec (∃ (x : polynomial α), ¬(polynomial.eval₂ smul_id_ring_hom f x v = 0 → x = 0)),
  obtain ⟨p, hp⟩ : ∃ p, ¬(eval₂ smul_id_ring_hom f p v = 0 → p = 0),
  { exact not_forall.1 (λ h, h_lin_dep ((linear_independent_iff_eval₂ f v).2 h)) },
  obtain ⟨h_eval_p, h_p_ne_0⟩ : eval₂ smul_id_ring_hom f p v = 0 ∧ p ≠ 0 := not_imp.1 hp,
  obtain ⟨q, hq_mem, hq_noninj⟩ : ∃ q ∈ factors p, ¬function.injective ⇑(eval₂ smul_id_ring_hom f q), 
  { exact exists_noninjective_factor_of_eval₂_0 f v hv p h_p_ne_0 h_eval_p },
  have h_q_ne_0 : q ≠ 0 := ne_0_of_mem_factors h_p_ne_0 hq_mem,
  have h_deg_q : q.degree = 1 := polynomial.degree_eq_one_of_irreducible h_q_ne_0 
    ((factors_spec p h_p_ne_0).1 q hq_mem),
  have h_q_eval₂ : polynomial.eval₂ smul_id_ring_hom f q = q.leading_coeff • f + smul_id (q.coeff 0),
  { rw [polynomial.eq_X_add_C_of_degree_eq_one h_deg_q],
    simp [eval₂_mul_noncomm smul_id_ring_hom f _ _ (λ x y, ( algebra.commutes' x y).symm)],
    simp [leading_coeff_X_add_C _ _ (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h))],
    refl },
  obtain ⟨x, hx₁, hx₂⟩ : ∃ (x : β), eval₂ smul_id_ring_hom f q x = 0 ∧ ¬x = 0,
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
lemma eigenvectors_linear_independent [field α] [decidable_eq α] [vector_space α β] 
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
      rw [mul_ne_zero_iff, sub_ne_zero, ←not_iff_not, not_and_distrib, not_not, not_not, ←subtype.ext_iff],
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
    have total_l' : (@linear_map.to_fun α (finsupp μs α) β _ _ _ _ _ (finsupp.total μs β α xs)) l' = 0,
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
        rw [linear_map.map_smul, linear_map.sub_apply, h_eigenvec, smul_id_apply, ←sub_smul, smul_smul, mul_comm] },
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
      rwa [sub_eq_zero, ←subtype.ext_iff] },

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
      exact h_xs_nonzero μ₀ ((vector_space.smul_neq_zero (xs μ₀) h) hl) },

    show l = 0,
    { ext μ,
      by_cases h_cases : μ = μ₀,
      { rw h_cases, 
        assumption },
      exact h_lμ_eq_0 μ h_cases } }
end

def generalized_eigenvector [field α] [vector_space α β] 
  (f : β →ₗ[α] β) (k : ℕ) (μ : α) (x : β) : Prop := ((f - smul_id μ) ^ k) x = 0

lemma generalized_eigenvector_zero_beyond [field α] [vector_space α β] 
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvector f k μ x) :
  ∀ m : ℕ, k ≤ m → ((f - smul_id μ) ^ m) x = 0 :=
begin
  intros m hm,
  rw ←pow_eq_pow_sub_mul _ hm,
  change ((f - smul_id μ) ^ (m - k)) (((f - smul_id μ) ^ k) x) = 0,
  unfold generalized_eigenvector at h,
  rw [h, linear_map.map_zero]
end

lemma exp_ne_zero_of_generalized_eigenvector_ne_zero [field α] [vector_space α β] 
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvector f k μ x) 
  (hx : x ≠ 0) : k ≠ 0 :=
begin
  contrapose hx,
  rw not_not at hx ⊢,
  rwa [hx, generalized_eigenvector, pow_zero] at h,
end

lemma generalized_eigenvector_of_eigenvector [field α] [vector_space α β] 
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (hx : f x = μ • x) (hk : k > 0) :
  generalized_eigenvector f k μ x :=
begin
  rw [generalized_eigenvector, ←nat.succ_pred_eq_of_pos hk, pow_succ'],
  change ((f - smul_id μ) ^ nat.pred k) ((f - smul_id μ) x) = 0,
  have : (f - smul_id μ) x = 0 := by simp [hx, smul_id_apply],
  simp [this]
end

/-- The set of generalized eigenvectors of f corresponding to an eigenvalue μ
    equals the kernel of (f - smul_id μ) ^ n, where n is the dimension of 
    the vector space (Axler's Lemma 3.1). -/
lemma generalized_eigenvector_dim 
  [field α] [decidable_eq α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (μ : α) (x : β) : 
  (∃ k : ℕ, generalized_eigenvector f k μ x) 
    ↔ generalized_eigenvector f (findim α β) μ x :=
begin
  split,
  { show (∃ (k : ℕ), generalized_eigenvector f k μ x) → ((f - smul_id μ) ^ findim α β) x = 0,
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
        apply vector_space.smul_neq_zero _ h_li_ne_0 } },

    show ((f - smul_id μ) ^ findim α β) x = 0,
    { apply generalized_eigenvector_zero_beyond 
        (@nat.find_spec (λ k : ℕ, generalized_eigenvector f k μ x) (classical.dec_pred _) h_exists_eigenvec),
      rw [←cardinal.nat_cast_le, ←cardinal.lift_mk_fin _, ←cardinal.lift_le, cardinal.lift_lift],
      rw findim_eq_dim,
      apply h_lin_indep.le_lift_dim} }, -- TODO: shorten this?

  { show ((f - smul_id μ) ^ findim α β) x = 0 → (∃ (k : ℕ), generalized_eigenvector f k μ x),
    exact λh, ⟨_, h⟩, }
end

#check linear_independent.le_lift_dim

-- TODO: replace "change" by some other tactic?
section

section
set_option class.instance_max_depth 70
lemma generalized_eigenvector_restrict_aux [field α] [vector_space α β] 
  (f : β →ₗ[α] β) (p : submodule α β) (k : ℕ) (μ : α) (x : p) 
  (hfp : ∀ (x : β), x ∈ p → f x ∈ p) : 
  (((f.restrict p p hfp - smul_id μ) ^ k) x : β) 
  = ((f - smul_id μ) ^ k) x :=
begin
  induction k with k ih,
  { rw [pow_zero, pow_zero, linear_map.one_app, linear_map.one_app] },
  { rw [pow_succ, pow_succ], 
    change ((f.restrict p p hfp - smul_id μ) (((f.restrict p p hfp - smul_id μ) ^ k) x) : β) =
        (f - smul_id μ) (((f - smul_id μ) ^ k) x),
    rw [linear_map.sub_apply, linear_map.sub_apply, linear_map.restrict_apply, ←ih], 
    refl }
end
end

lemma generalized_eigenvector_restrict [field α] [vector_space α β] 
  (f : β →ₗ[α] β) (p : submodule α β) (k : ℕ) (μ : α) (x : p) (hfp : ∀ (x : β), x ∈ p → f x ∈ p) : 
  generalized_eigenvector (linear_map.restrict f p p hfp) k μ x 
    ↔ generalized_eigenvector f k μ x :=
by { rw [generalized_eigenvector, subtype.ext_iff, generalized_eigenvector_restrict_aux], refl }

#check set.image_preimage_subset 
-- begin
--   ext,
--   rw [set.mem_image, set.mem_set_of_eq],
--   split,
--   { intro h,
--     use f x,},
--   {}
-- end

lemma generalized_eigenvector_dim_of_any
  [field α] [decidable_eq α] [vector_space α β] [finite_dimensional α β]
  {f : β →ₗ[α] β} {μ : α}
  {m : ℕ} {x : β} (h : generalized_eigenvector f m μ x) :
  generalized_eigenvector f (findim α β) μ x :=
begin
  rw ←generalized_eigenvector_dim,
  { exact ⟨m, h⟩ }
end

lemma generalized_eigenvec_disjoint_range_ker
  [field α] [decidable_eq α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (μ : α) : 
  disjoint ((f - smul_id μ) ^ findim α β).range ((f - smul_id μ) ^ findim α β).ker :=
begin
  rintros v ⟨⟨u, _, hu⟩, hv⟩,
  have h2n : ((f - smul_id μ) ^ (findim α β + findim α β)) u = 0,
  { rw [pow_add, ←linear_map.mem_ker.1 hv, ←hu], refl },
  have hn : ((f - smul_id μ) ^ findim α β) u = 0, 
  { apply generalized_eigenvector_dim_of_any h2n },
  have hv0 : v = 0, by rw [←hn, hu],
  show v ∈ ↑⊥, by simp [hv0]
end

lemma pos_dim_eigenker_of_nonzero_eigenvec [algebraically_closed α] [vector_space α β] 
  {f : β →ₗ[α] β} {n : ℕ} {μ : α} {x : β} (hx : x ≠ 0) (hfx : f x = μ • x) : 
  0 < dim α ((f - smul_id μ) ^ n.succ).ker :=
begin
  have x_mem : x ∈ ((f - smul_id μ) ^ n.succ).ker,
  { simp [pow_succ', hfx, smul_id_apply] },
  apply dim_pos_of_mem_ne_zero (⟨x, x_mem⟩ : ((f - smul_id μ) ^ n.succ).ker),
  intros h,
  apply hx,
  exact congr_arg subtype.val h,
end

lemma pos_findim_eigenker_of_nonzero_eigenvec 
  [algebraically_closed α] [vector_space α β] [finite_dimensional α β]
  {f : β →ₗ[α] β} {n : ℕ} {μ : α} {x : β} (hx : x ≠ 0) (hfx : f x = μ • x) : 
  0 < findim α ((f - smul_id μ) ^ n.succ).ker :=
begin
  apply cardinal.nat_cast_lt.1,
  rw findim_eq_dim,
  apply pos_dim_eigenker_of_nonzero_eigenvec hx hfx,
end

lemma eigenker_le_span_gen_eigenvec [field α] [vector_space α β] 
  (f : β →ₗ[α] β) (μ₀ : α) (n : ℕ) :
((f - smul_id μ₀) ^ n).ker 
  ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}) :=
begin
  intros x hx,
  apply submodule.subset_span,
  exact ⟨n, μ₀, linear_map.mem_ker.1 hx⟩
end

lemma image_mem_eigenrange_of_mem_eigenrange [field α] [vector_space α β] 
  {f : β →ₗ[α] β} {μ : α} {x : β} {n : ℕ}
  (hx : x ∈ ((f - smul_id μ) ^ n).range) : 
  f x ∈ ((f - smul_id μ) ^ n).range :=
begin
  rw linear_map.mem_range at *,
  rcases hx with ⟨w, hw⟩,
  use f w,
  have hcommutes : f.comp ((f - smul_id μ) ^ n) = ((f - smul_id μ) ^ n).comp f := 
    algebra.mul_sub_algebra_map_pow_commutes f μ n,
    -- TODO: use algebra_map instead of smul_id
  rw [←linear_map.comp_apply, ←hcommutes, linear_map.comp_apply, hw],
end

/-- The generalized eigenvectors of f span the vectorspace β. (Axler's Proposition 3.4). -/
lemma generalized_eigenvector_span 
  [algebraically_closed α] [decidable_eq α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) : 
  submodule.span α {x | ∃ k μ, generalized_eigenvector f k μ x} = ⊤ :=
begin
  rw ←top_le_iff,
  tactic.unfreeze_local_instances,
  induction h_dim : findim α β using nat.strong_induction_on with n ih generalizing β,
  cases n,
  { have h_findim_top: findim α (⊤ : submodule α β) = 0 := eq.trans (@finite_dimensional.findim_top α β _ _ _ _) h_dim,
    have h_top_eq_bot : (⊤ : submodule α β) = ⊥ := bot_of_findim_zero _ h_findim_top,
    simp only [h_top_eq_bot, bot_le] },
  { have h_dim_pos : 0 < findim α β,
    { rw [h_dim],
      apply nat.zero_lt_succ },
    obtain ⟨x, μ₀, hx_ne_0, hμ₀⟩ : ∃ (x : β) (μ₀ : α), x ≠ 0 ∧ f x = μ₀ • x,
    { apply exists_eigenvector f 
        (exists_mem_ne_zero_of_findim_pos h_dim_pos) },
    let V₁ := ((f - smul_id μ₀) ^ n.succ).ker,
    let V₂ := ((f - smul_id μ₀) ^ n.succ).range,
    have h_disjoint : disjoint V₂ V₁,
    { simp only [V₁, V₂, h_dim.symm],
      exact generalized_eigenvec_disjoint_range_ker f μ₀ },
    have h_dim_add : findim α V₂ + findim α V₁ = findim α β,
    { apply linear_map.findim_range_add_findim_ker },
    have h_dim_V₁_pos : 0 < findim α V₁,
    { apply pos_findim_eigenker_of_nonzero_eigenvec hx_ne_0 hμ₀ },
    have h_findim_V₂ : findim α V₂ < n.succ := by linarith,
    have h_f_V₂ : ∀ (x : β), x ∈ V₂ → f x ∈ V₂, 
    { intros x hx, 
      apply image_mem_eigenrange_of_mem_eigenrange hx, },
    have hV₂ : V₂ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}),
    { have : V₂ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x} ∩ V₂),
      { rw ←subtype.image_preimage_val,
        rw ←submodule.subtype_eq_val V₂,
        rw submodule.span_image (submodule.subtype V₂),
        rw set.preimage_set_of_eq,
        rw submodule.subtype_eq_val,
        have h₀ : ∀ p, submodule.map (submodule.subtype V₂) ⊤ 
              ≤ submodule.map (submodule.subtype V₂) p 
              ↔ ⊤ ≤ p
            := λ _, (linear_map.map_le_map_iff' (submodule.ker_subtype V₂)),
        have := submodule.range_subtype V₂,
        unfold linear_map.range at this,
        rw this at h₀,
        rw h₀,
        have := ih (findim α V₂) h_findim_V₂ (f.restrict V₂ V₂ h_f_V₂) rfl,
        simp only [generalized_eigenvector_restrict] at this,
        apply this },
      refine le_trans this _,
      apply submodule.span_mono,
      apply set.inter_subset_left },
    have hV₁ : V₁ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}),
    { apply eigenker_le_span_gen_eigenvec },
    show ⊤ ≤ submodule.span α {x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x},
    { rw ←finite_dimensional.eq_top_of_disjoint V₂ V₁ h_dim_add h_disjoint,
      apply lattice.sup_le hV₂ hV₁ } }
end

end

end

end