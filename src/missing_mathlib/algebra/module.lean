import algebra.module


lemma linear_map.to_fun_eq_coe_fn {α β γ : Type*} [ring α] [add_comm_group β] [add_comm_group γ] [module α β] [module α γ] 
  (f : β →ₗ[α] γ): linear_map.to_fun f = ⇑f := rfl