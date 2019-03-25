import .inner_product_space
import .cone
import .mat

namespace mat

noncomputable instance inner_product (n : ℕ) : 
  real_inner_product_space (mat ℝ n n) := {
  inner := λ A B, trace (A * B),
  inner_add_left := sorry,
  inner_smul_left := sorry,
  inner_comm := sorry,
  inner_self_nonneg := sorry,
  eq_zero_of_inner_self_eq_zero := sorry,
}

end mat

#check λ n : nat, inner_product_cone (mat ℝ n n) 