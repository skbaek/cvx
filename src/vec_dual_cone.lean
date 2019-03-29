import .cone .rowvec

section vec_dual_cone

variables {k m n : nat} (a : ℝ) (x y z : colvec ℝ n) (A : set (colvec ℝ n))

-- TODO: move?
local infix ` ⬝ ` : 70 := matrix.mul

def vec_dual_cone (A : set (colvec ℝ n)) : set (rowvec ℝ n) := 
{ y | ∀ x ∈ A, (0 : ℝ) ≤ y ⬝ x }

lemma cone_vec_dual_cone : cone (vec_dual_cone A) :=
begin
  intros x ha c hc z hz,
  rw matrix.smul_mul,
  apply zero_le_mul hc,
  exact ha _ hz
end

def second_order_cone (n : nat): set (colvec ℝ (n + 1)) :=
{ x : colvec ℝ (n + 1) | ∥ x.butlast ∥  ≤ x.last }

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
  vec_dual_cone (second_order_cone n) = (second_order_cone n)ᵀ :=
begin
  have h_ltr: vec_dual_cone (second_order_cone n) ⊆ (second_order_cone n)ᵀ,
  { assume (y : rowvec ℝ (n + 1)) (hy : y ∈ vec_dual_cone (second_order_cone n)),
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
    { --TODO ...
    
    have h : 0 ≤ ⟪ - y.fst, y.fst ⟫ + real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd,
      { 
        apply hy (- y.fst, real.sqrt ⟪ y.fst, y.fst ⟫),
        unfold norm_cone,
        simp,
        refl,
      },
      have h : ⟪ y.fst, y.fst ⟫ ≤ real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd,
      { 
        apply le_of_sub_nonneg, 
        rw [←@neg_add_eq_sub ℝ (ring.to_add_comm_group _)],
        rwa [ ←inner_neg_left]
      },
      have h : real.sqrt ⟪ y.fst, y.fst ⟫ * ⟪ y.fst, y.fst ⟫ ≤ real.sqrt ⟪ y.fst, y.fst ⟫ * (real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd),
        from mul_le_mul (le_refl _) h (inner_self_nonneg _) (real.sqrt_nonneg _),
      have h : ⟪ y.fst, y.fst ⟫ * real.sqrt ⟪ y.fst, y.fst ⟫ ≤ ⟪ y.fst, y.fst ⟫ * y.snd,
      {
        rw [←mul_assoc, ←real.sqrt_mul (inner_self_nonneg _), real.sqrt_mul_self (inner_self_nonneg _)] at h,
        rwa mul_comm
      },
      show y ∈ norm_cone α,
        from le_of_mul_le_mul_left h (inner_self_pos h_cases)
    }
  },
  have h_rtl: norm_cone α ⊆ dual_cone (norm_cone α),
  begin
    assume (y : α × ℝ) (hy : real.sqrt ⟪ y.1, y.1 ⟫ ≤ y.2),
    assume (x : α × ℝ) (hx :  real.sqrt ⟪ x.1, x.1 ⟫ ≤ x.2),
    have hx' : real.sqrt ⟪ - x.1, - x.1 ⟫ ≤ x.2,
      by simpa,
    have h : ⟪ -x.1, y.1 ⟫ ≤ x.2 * y.2,
      calc ⟪ -x.1, y.1 ⟫ ≤ real.sqrt ⟪ -x.1, -x.1 ⟫ * real.sqrt ⟪ y.1, y.1 ⟫ : cauchy_schwartz' _ _
                    ... ≤ x.2 * y.2                                         : mul_le_mul hx' hy (real.sqrt_nonneg _) (le_trans (real.sqrt_nonneg _) hx'),
    show 0 ≤ ⟪ x.fst, y.fst ⟫ + x.snd * y.snd,
    {
      rw [inner_neg_left] at h,
      rw add_comm,
      convert sub_nonneg_of_le h,
      simp
    }
  end,
  show dual_cone (norm_cone α) = norm_cone α,
    from set.subset.antisymm h_ltr h_rtl
end

end vec_dual_cone