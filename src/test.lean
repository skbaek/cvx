import algebra.module analysis.normed_space.basic data.real.basic

class real_inner_product_space (V : Type*) [add_comm_group V] extends vector_space ℝ V :=
(inner : V → V → ℝ)
(inner_axioms : false /- (axioms omitted here) -/)

instance is_normed_space (V : Type*) [add_comm_group V] [real_inner_product_space V] :
  normed_space ℝ V := sorry

local attribute [-instance] is_normed_space

set_option trace.class_instances true
noncomputable example : add_comm_group ℝ := by apply_instance