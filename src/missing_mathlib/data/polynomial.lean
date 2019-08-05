import data.polynomial

universe variables u v w

namespace polynomial

variables {α : Type u} {β : Type v}
open polynomial
-- TODO: move
lemma not_is_unit_X_sub_C {α : Type*} [integral_domain α] [decidable_eq α]:  
  ∀ a : α, ¬ is_unit (X - C a) :=
begin intros a ha, 
  let ha' := degree_eq_zero_of_is_unit ha,
  rw [degree_X_sub_C] at ha',
  apply nat.zero_ne_one (option.injective_some _ ha'.symm)
end

lemma leading_coeff_C_add_X {α : Type v} [integral_domain α] [decidable_eq α] (a b : α) (hb : b ≠ 0): 
  leading_coeff (C a + C b * X) = b :=
begin
  rw leading_coeff_add_of_degree_lt,
  { simp },
  { simp [degree_C hb],
    apply lt_of_le_of_lt degree_C_le (with_bot.coe_lt_coe.2 zero_lt_one)},
end

end polynomial

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

lemma finsupp_sum_eq_eval₂ (α : Type v) (β : Type w)
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) (p : polynomial α) : 
  (finsupp.sum p (λ n b, b • (f ^ n) v))  
    = polynomial.eval₂ (λ a, a • linear_map.id) f p v :=
begin
  dunfold polynomial.eval₂ finsupp.sum,
  convert @finset.sum_hom _ _ _ p.support _ _ _ (λ h : β →ₗ[α] β, h v) _,
  simp
end

lemma eval₂_prod_noncomm {α β : Type*} [comm_ring α] [decidable_eq α] [semiring β]
  (f : α → β) [is_semiring_hom f] (hf : ∀ b a, a * f b = f b * a) (x : β)
  (ps : list (polynomial α)) : 
  polynomial.eval₂ f x ps.prod = (ps.map (λ p, (polynomial.eval₂ f x p))).prod :=
begin 
  induction ps,
  simp,
  simp [eval₂_mul_noncomm f _ _ _ hf, ps_ih] {contextual := tt}
end
