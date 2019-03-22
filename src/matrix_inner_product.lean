import .matrix
import .inner_product_space
import .cone

namespace matrix

noncomputable instance inner_product (n : ℕ) : real_inner_product_space (matrix ℝ n n) := {
  inner := λ A B, trace (A * B),
  inner_add_left := sorry,
  inner_smul_left := sorry,
  inner_comm := sorry,
  inner_self_nonneg := sorry,
  eq_zero_of_inner_self_eq_zero := sorry,
}

end matrix

#check λ n, inner_product_cone (matrix ℝ n n)