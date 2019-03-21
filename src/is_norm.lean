
-- TODO: move
class is_norm (α : Type*) {β : Type*} (N : β → ℝ) [normed_field α] [add_comm_group β] [vector_space α β] :=
  (norm_eq_zero_iff: ∀ x : β, N x = 0 ↔ x = 0)
  (norm_smul : ∀ c : α, ∀ x : β, N (c • x) = @has_norm.norm α (normed_field.to_has_norm α) c * N x)
  (triangle : ∀ x y : β, N (x + y) ≤ N x + N y)

-- TODO: move
namespace is_norm

variables (α : Type*) {β : Type*} (N : β → ℝ) [normed_field α] [add_comm_group β] [vector_space α β]

--local notation `∥` x `∥` := N x

lemma norm_zero [is_norm α N] : N 0 = 0 := 
by rw norm_eq_zero_iff α N 0

lemma norm_neg [is_norm α N] (x : β) :N (-x) = N x := 
begin 
  rw [←one_smul α x, ←neg_smul, @norm_smul α β N, @norm_neg α normed_ring.to_normed_group],
  rw [@norm_one α (by apply_instance),one_mul,one_smul]
end

lemma norm_nonneg [is_norm α N] (x : β) : 0 ≤ N x :=
begin
  apply (@mul_le_mul_left _ _ _ _ (2 : ℝ) (lt_trans zero_lt_one one_lt_two)).1,
  convert is_norm.triangle α N x (-x),
  { rw [add_neg_self, norm_zero α N, mul_zero] },
  { rw [two_mul,norm_neg α N] }
end

/-
/-- Equivalent norms with explicit coefficients -/
def equiv_by (b₁ : ℝ) (b₂ : ℝ) (N₁ : β → ℝ) (N₂ : β → ℝ)  := 
  ∀ x, N₁ x ≤ b₂ * N₂ x ∧ N₂ x ≤ b₁ * N₁ x

/-- Equivalent norms -/
def equiv (N₁ : β → ℝ) (N₂ : β → ℝ) := 
  ∃ b₁ b₂, equiv_by b₁ b₂ N₁ N₂ 

lemma equiv_by_abs {N₁ : β → ℝ} {N₂ : β → ℝ} [is_norm α N₁] [is_norm α N₂] 
  {b₁ : ℝ} {b₂ : ℝ} (h : equiv_by b₁ b₂ N₁ N₂) :
  equiv_by (abs b₁) (abs b₂) N₁ N₂ :=
begin
  unfold equiv_by at *,
  intros x,
  apply and.intro,
  { apply le_trans (h x).1,
    apply mul_le_mul _ (le_refl _) (norm_nonneg α N₂ _) (abs_nonneg _),
    apply le_abs_self },
  { apply le_trans (h x).2,
    apply mul_le_mul _ (le_refl _) (norm_nonneg α N₁ _) (abs_nonneg _),
    apply le_abs_self }
end

--set_option pp.all true

instance normed_space_is_norm [normed_space α β] : 
  is_norm α (norm : β → ℝ) :=
{
  norm_eq_zero_iff := begin 
  intros x,
  apply iff.intro,
  intros hx,
  apply eq_of_dist_eq_zero,
  rw [normed_group.dist_eq x], 
  simp [hx], end,
  norm_smul := sorry,
  triangle := sorry,
}

-/
end is_norm

section norm

variables {α : Type*} (N : α → ℝ) [hα : add_comm_group α] [hℝα : vector_space ℝ α] [hN : is_norm ℝ N]

def norm_cone : set (α × ℝ) :=
  { x : α × ℝ | N x.1 ≤ x.2 }

set_option trace.class_instances true
-- TODO: why does ` variables ` not work?
lemma cone_norm_cone  {α : Type*} (N : α → ℝ) [hα : add_comm_group α] [hℝα : vector_space ℝ α] [hN : is_norm ℝ N] : 
@cone (α × ℝ) (@prod.add_comm_group α ℝ hα (ring.to_add_comm_group ℝ) ) 
(@prod.vector_space ℝ α ℝ _ _ (/-ring.to_add_comm_group ℝ-/_) hℝα discrete_field.to_vector_space) (@norm_cone α N) :=
begin
  intros x ha c hc,
  unfold norm_cone at *,
  simp [is_norm.norm_smul N c x.fst, real.norm_eq_abs, abs_of_nonneg hc],
  apply mul_le_mul (le_refl _),
  { simp at ha, assumption },
  { apply is_norm.norm_nonneg ℝ N },
  { exact hc }
end

open lattice

-- TODO: why does ` variables ` not work?
--
def dual_norm {α : Type*} (N : α → ℝ) [hα : add_comm_group α] [hℝα : vector_space ℝ α] [hN : is_norm ℝ N] [real_inner_product_space α] : 
α → ℝ := lattice.Sup { c : ℝ | ∃ x, c = ⟪ y, x ⟫ ∧ N x ≤ 1 }

/-- The dual norm is well defined if  the norm induced by the inner product
 (norm) can be bounded by the primal norm. In finite dimensional real vector
 spaces all norms are equivalent and the condition is always true. -/
lemma dual_norm_bounded [real_inner_product_space α] (y : α) (b : ℝ) (hb : 0 ≤ b ∧ ∀x, norm x ≤ b * N x): 
  bdd_above { c | ∃ x, c = ⟪ y, x ⟫ ∧ N x ≤ 1 } :=
begin
  unfold bdd_above,
  use norm y * b,
  intros c hc,
  apply exists.elim hc,
  intros x hx,
  rw hx.1,
  have h_norm_x : norm x ≤ b,
  begin
    apply le_trans (hb.2 x) _,
    apply mul_le_of_le_one_right hb.1 hx.2,
  end,
  apply le_trans (real_inner_product_space.cauchy_schwartz' y x),
  apply mul_le_mul (le_refl _) h_norm_x (norm_nonneg _) (norm_nonneg _)
end


--set_option pp.all true

instance dual_norm_is_norm 
{α : Type*} (N : α → ℝ) [hα : real_inner_product_space α] [vector_space ℝ α] [is_norm ℝ N]
 (b : ℝ) (hb : 0 ≤ b ∧ ∀x, norm x ≤ b * N x): 
  is_norm ℝ (dual_norm N) :=
{ 
  norm_eq_zero_iff := 
  begin
    intros y,
    apply iff.intro,
    { unfold dual_norm,
      intro h,
      have h_nonempty : { c | ∃ x, c = ⟪ y, x ⟫ ∧ N x ≤ 1 } ≠ ∅,
      begin
        apply @set.ne_empty_of_mem ℝ _ 0,
        use 0,
        apply and.intro,
        apply (real_inner_product_space.inner_zero_right y).symm,
        rw is_norm.norm_zero ℝ N,
        linarith
      end,
      have hy : ⟪y, (N y)⁻¹ • y⟫ ≤ 0,
      begin
        apply (lattice.cSup_le_iff (dual_norm_bounded _ y b hb) h_nonempty).1 (le_of_eq h) ⟪y, (N y)⁻¹ • y⟫,
        use (N y)⁻¹ • y,
        apply and.intro rfl,
        rw @is_norm.norm_smul ℝ α N _,
        rw real.norm_eq_abs,
        rw abs_of_nonneg (inv_nonneg.2 (is_norm.norm_nonneg ℝ N y)),
        by_cases h_cases: N y = 0,
        { simp [h_cases], linarith },
        { rw inv_mul_cancel h_cases },
      end,
      have hy : (N y)⁻¹ * ⟪y, y⟫ ≤ 0,
      begin
        rw [←real_inner_product_space.inner_smul_right],
        exact hy,
      end
      show y = 0,
      begin
        apply real_inner_product_space.eq_zero_of_inner_self_eq_zero,
        
      end
    },
    { sorry }
  end,
  norm_smul := sorry,
  triangle := sorry
}

lemma inner_product_cone [real_inner_product_space α] : 
  dual_cone (norm_cone norm) = norm_cone (dual_norm norm) := --TODO use dual norm
begin
  apply set.subset.antisymm,
  { intros x hx, unfold norm_cone, },
  {sorry}
end

end norm 
.


