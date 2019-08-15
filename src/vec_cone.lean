import .cone .colvec

section dual_cone

variables {k m n : nat} (a : ℝ) (x y z : colvec (fin n) ℝ) (A : set (colvec (fin n) ℝ))

def second_order_cone (n : nat): set (colvec (fin (n + 1)) ℝ ) :=
{ x | ∥ x.tail ∥ ≤ x.head }

lemma cone_second_order_cone : 
cone (second_order_cone n) :=
begin
  intros x ha c hc,
  unfold second_order_cone at *,
  rw [set.mem_set_of_eq, colvec.tail_smul, colvec.head_smul, 
    norm_smul, real.norm_eq_abs, abs_of_nonneg hc],
  exact mul_le_mul (le_refl c) ha (norm_nonneg _) hc
end

postfix `ᵀ` : 1500 := set.image matrix.transpose

lemma second_order_cone_self_dual : 
  dual_cone (second_order_cone n) = second_order_cone n :=
begin
  have h_ltr: dual_cone (second_order_cone n) ⊆ second_order_cone n,
  { assume (y : colvec (fin (n + 1)) ℝ) (hy : y ∈ dual_cone (second_order_cone n)),
    by_cases h_cases : y.tail = 0,
    { have h : (0:ℝ) ≤ ⟪ colvec.cons 1 0, y ⟫,
      { apply hy (colvec.cons 1 0),
        simp [second_order_cone,zero_le_one] },
      have h : 0 ≤ y.head,
      { rw [←@colvec.mul_head_add_mul_tail n ℝ _ (colvec.cons 1 0) y] at h,
        simpa [matrix.mul_zero'] using h },
      show y ∈ second_order_cone n,
      { unfold second_order_cone,
        rwa [set.mem_set_of_eq, h_cases, norm_zero] }
    },
    { let y1 := y.head,
      let y2 := y.tail,
      have h : (0 : ℝ) ≤ real.sqrt ⟪ y2, y2 ⟫ * y1 + ⟪ - y2, y2 ⟫,
      { convert hy (colvec.cons (real.sqrt ⟪ y2, y2 ⟫) (- y2)) _,
        unfold has_inner.inner,
        convert @colvec.mul_head_add_mul_tail n ℝ _ _ _,
        { simp },
        { simp },
        simp [second_order_cone],
        refl
      },
      have h : ⟪ y2, y2 ⟫ ≤ real.sqrt ⟪ y2, y2 ⟫ * y1,
      { 
        apply le_of_sub_nonneg,
        rw real_inner_product_space.inner_neg_left at h,
        rwa sub_eq_add_neg,
      },
      have h : real.sqrt ⟪ y2, y2 ⟫ * ⟪ y2, y2 ⟫ ≤ real.sqrt ⟪ y2, y2 ⟫ * (real.sqrt ⟪ y2, y2 ⟫ * y1),
        from mul_le_mul (le_refl _) h (real_inner_product_space.inner_self_nonneg _) (real.sqrt_nonneg _),
      have h : ⟪ y2, y2 ⟫ * real.sqrt ⟪ y2, y2 ⟫ ≤ ⟪ y2, y2 ⟫ * y1,
      {
        rw [←mul_assoc, mul_comm] at h,
        convert h,
        convert (@real.sqrt_mul ⟪ y2, y2 ⟫ (real_inner_product_space.inner_self_nonneg _) ⟪ y2, y2 ⟫),
        apply (real.sqrt_mul_self (real_inner_product_space.inner_self_nonneg _)).symm
      },
      show y ∈ second_order_cone n,
        from le_of_mul_le_mul_left h (real_inner_product_space.inner_self_pos h_cases),
    }
  },
  have h_rtl: second_order_cone n ⊆ dual_cone (second_order_cone n),
  begin
    assume (y : colvec (fin (n + 1)) ℝ),
    assume (hy : y ∈ second_order_cone n),
    assume (x : colvec (fin (n + 1)) ℝ) (hx : real.sqrt ⟪ x.tail, x.tail ⟫ ≤ x.head),
    have hx' : real.sqrt ⟪ - x.tail, - x.tail ⟫ ≤ x.head,
      by simpa,
    have h : ⟪ -x.tail, y.tail ⟫ ≤ x.head * y.head,
      calc ⟪ -x.tail, y.tail ⟫
            ≤ real.sqrt ⟪ -x.tail, -x.tail ⟫ * real.sqrt ⟪ y.tail, y.tail ⟫ 
              : real_inner_product_space.cauchy_schwartz' _ _
        ... ≤ x.head * y.head
              : mul_le_mul hx' hy (real.sqrt_nonneg _) (le_trans (real.sqrt_nonneg _) hx'),
    show 0 ≤ ⟪ x, y ⟫,
    {
      rw [←@colvec.mul_head_add_mul_tail n ℝ _ x y],
      rw [real_inner_product_space.inner_neg_left] at h,
      convert sub_nonneg_of_le h,
      simp
    }
  end,
  show dual_cone (second_order_cone n) = second_order_cone n,
    from set.subset.antisymm h_ltr h_rtl
end

end dual_cone