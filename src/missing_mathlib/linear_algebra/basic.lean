import linear_algebra.basic

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}


variables {R:discrete_field α} [add_comm_group β] [add_comm_group γ]
variables [vector_space α β] [vector_space α γ]
variables (p p' : submodule α β)
variables {r : α} {x y : β}
include R

set_option class.instance_max_depth 36

lemma vector_space.smul_neq_zero (x : β) (hr : r ≠ 0) : r • x = 0 ↔ x = 0 :=
begin
  have := submodule.smul_mem_iff ⊥ hr,
  rwa [submodule.mem_bot, submodule.mem_bot] at this,
end
