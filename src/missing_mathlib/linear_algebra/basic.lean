import linear_algebra.basic

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}  {ι : Type x}

namespace linear_map
section
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ] 
variables [module α β] [module α γ] [module α δ] 
variables (f g : β →ₗ[α] γ)
include α

def restrict
  (f : β →ₗ[α] γ) (p : submodule α β) (q : submodule α γ) (hf : ∀ x ∈ p, f x ∈ q) : 
  p →ₗ[α] q :=
{ to_fun := λ x, ⟨f x, hf x.1 x.2⟩,
  add := begin intros, apply set_coe.ext, simp end,
  smul := begin intros, apply set_coe.ext, simp end }

lemma restrict_apply (f : β →ₗ[α] γ) (p : submodule α β) (q : submodule α γ) (hf : ∀ x ∈ p, f x ∈ q) (x : p) :
  f.restrict p q hf x = ⟨f x, hf x.1 x.2⟩ := rfl

-- TODO: replace sum_apply (wrong type classes on δ)
lemma sum_apply' [decidable_eq ι] (t : finset ι) (f : ι → β →ₗ[α] γ) (b : β) :
  t.sum f b = t.sum (λd, f d b) :=
(@finset.sum_hom _ _ _ t f _ _ (λ g : β →ₗ[α] γ, g b) _).symm
end
end linear_map

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
