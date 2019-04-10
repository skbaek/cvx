import analysis.complex.polynomial
import ring_theory.noetherian

open polynomial


#check is_noetherian_ring.exists_factors (p : polynomial ℂ)
-- better euclidean_domain -> principle_ideal_domain -> factors

#check complex.exists_root
#print irreducible

#check polynomial.mul_div_eq_iff_is_root



--set_option pp.all true


lemma polynomial.not_is_unit_X_sub_C {α : Type} [integral_domain α] [decidable_eq α]:  ∀ a : α, ¬ is_unit (X - C a) :=
begin intros a ha, 
  let ha' := degree_eq_zero_of_is_unit ha,
  rw [degree_X_sub_C] at ha',
  apply nat.zero_ne_one (option.injective_some _ ha'.symm)
end

lemma complex.degree_le_one_of_irreducible (p : polynomial ℂ) : irreducible p → p.degree ≤ 1 :=
begin
  by_cases h_cases : 0 < p.degree,
  { 
    assume hp : irreducible p,
    show degree p ≤ 1,
    { cases (complex.exists_root h_cases) with a ha,
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