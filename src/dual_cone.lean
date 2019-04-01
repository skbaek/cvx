import .cone .rowvec

section dual_cone

variables {k m n : nat} (a : ℝ) (x y z : colvec ℝ n) (A : set (colvec ℝ n))

-- TODO: move?
local infix ` ⬝ ` : 70 := matrix.mul

def dual_cone (A : set (colvec ℝ n)) : set (rowvec ℝ n) := 
{ y | ∀ x ∈ A, (0 : ℝ) ≤ y ⬝ x }

lemma cone_dual_cone : cone (dual_cone A) :=
begin
  intros x ha c hc z hz,
  rw matrix.smul_mul,
  apply zero_le_mul hc,
  exact ha _ hz
end

def second_order_cone (n : nat): set (colvec ℝ (n + 1)) :=
{ x : colvec ℝ (n + 1) | ∥ x.butlast ∥ ≤ x.last }

lemma cone_second_order_cone : 
cone (second_order_cone n) :=
begin
  intros x ha c hc,
  unfold second_order_cone at *,
  rw [set.mem_set_of_eq, colvec.butlast_smul, colvec.last_smul, norm_smul, real.norm_eq_abs, abs_of_nonneg hc],
  exact mul_le_mul (le_refl c) ha (norm_nonneg _) hc
end

postfix `ᵀ` : 1500 := set.image matrix.transpose

lemma second_order_cone_self_dual : 
  dual_cone (second_order_cone n) = (second_order_cone n)ᵀ :=
begin
  have h_ltr: dual_cone (second_order_cone n) ⊆ (second_order_cone n)ᵀ,
  { assume (y : rowvec ℝ (n + 1)) (hy : y ∈ dual_cone (second_order_cone n)),
    by_cases h_cases : y.butlast = 0,
    { have h : (0:ℝ) ≤ y ⬝ (colvec.snoc 0 1),
      { apply hy (colvec.snoc 0 1),
        simp [second_order_cone,zero_le_one] },
      have h : 0 ≤ y.last,
      { rw [←rowvec.mul_last_add_mul_butlast] at h,
        simp [matrix.mul_zero'] at h,
        dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe] at h, --TODO WTF?
        rwa add_zero y.last at h },
      show y ∈ (second_order_cone n)ᵀ,
      { unfold second_order_cone,
        use yᵀ,
        split,
        { rw [set.mem_set_of_eq, rowvec.butlast_transpose, h_cases],
          rwa [matrix.transpose_zero, norm_zero, rowvec.last_transpose] },
        { exact matrix.transpose_transpose _ } }
    },
    { let y1 := y.butlast,
      let y2 := y.last,
      have h : (0 : ℝ) ≤ real.sqrt (y1 ⬝ y1ᵀ) * y2 + (- y1) ⬝ y1ᵀ,
      { convert hy (colvec.snoc (- y1ᵀ) (real.sqrt (y1 ⬝ y1ᵀ))) _,
        rw mul_comm,
        rw [← matrix.transpose_transpose (-y1)],
        rw [← matrix.transpose_mul y1 (-y1)ᵀ, one_by_one_matrix.transpose],
        convert rowvec.mul_last_add_mul_butlast _ _,
        { simp },
        { simp },
        simp [second_order_cone],
        refl
      },
      have h : (y1 ⬝ y1ᵀ : ℝ) ≤ real.sqrt (y1 ⬝ y1ᵀ) * y2,
      { 
        apply le_of_sub_nonneg,
        rw matrix.neg_mul at h,
        rwa sub_eq_add_neg,
      },
      have h : real.sqrt (y1 ⬝ y1ᵀ) * (y1 ⬝ y1ᵀ) ≤ real.sqrt (y1 ⬝ y1ᵀ) * (real.sqrt (y1 ⬝ y1ᵀ) * y2),
        from mul_le_mul (le_refl _) h (colvec.inner_self_nonneg _) (real.sqrt_nonneg _),
      have h : (y1 ⬝ y1ᵀ : ℝ) * real.sqrt (y1 ⬝ y1ᵀ) ≤ (y1 ⬝ y1ᵀ) * y2,
      {
        rw [←mul_assoc, mul_comm] at h,
        convert h,
        convert (@real.sqrt_mul (y1 ⬝ y1ᵀ) (rowvec.inner_self_nonneg _) (y1 ⬝ y1ᵀ)),
        apply (real.sqrt_mul_self (rowvec.inner_self_nonneg _)).symm
      },
      show y ∈ (second_order_cone n)ᵀ,
      {
        use yᵀ,
        split,
        { apply le_of_mul_le_mul_left h (rowvec.inner_self_pos h_cases) },
        { rw matrix.transpose_transpose }
      } 
    }
  },
  have h_rtl: (second_order_cone n)ᵀ ⊆ dual_cone (second_order_cone n),
  begin
    assume (y : rowvec ℝ (n + 1)),
    assume (hy : y ∈ (second_order_cone n)ᵀ),
    assume (x : colvec ℝ (n + 1)) (hx : real.sqrt ⟪ x.butlast, x.butlast ⟫ ≤ x.last),
    have hy' : real.sqrt ⟪ colvec.butlast yᵀ, colvec.butlast yᵀ ⟫ ≤ colvec.last yᵀ,
    begin
      apply exists.elim hy,
      intros yt hyt,
      rw [hyt.2.symm, matrix.transpose_transpose],
      apply hyt.1
    end,
    have hx' : real.sqrt ⟪ - x.butlast, - x.butlast ⟫ ≤ x.last,
      by simpa,
    have h : ⟪ -x.butlast, colvec.butlast yᵀ ⟫ ≤ x.last * colvec.last yᵀ,
      calc ⟪ -x.butlast, colvec.butlast yᵀ ⟫ 
            ≤ real.sqrt ⟪ -x.butlast, -x.butlast ⟫ * real.sqrt ⟪ colvec.butlast yᵀ, colvec.butlast yᵀ ⟫ 
              : real_inner_product_space.cauchy_schwartz' _ _
        ... ≤ x.last * colvec.last yᵀ                                        
              : mul_le_mul hx' hy' (real.sqrt_nonneg _) (le_trans (real.sqrt_nonneg _) hx'),
    show (0 : ℝ) ≤ y ⬝ x,
    {
      rw [← rowvec.mul_last_add_mul_butlast],
      rw [real_inner_product_space.inner_neg_left] at h,
      rw mul_comm,
      convert sub_nonneg_of_le h,
      simp [has_inner.inner, inner, matrix.transpose_transpose],
    }
  end,
  show dual_cone (second_order_cone n) = (second_order_cone n)ᵀ,
    from set.subset.antisymm h_ltr h_rtl
end

end dual_cone