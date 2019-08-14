import linear_algebra.basic
import ring_theory.algebra

universes v w

section smul_id
variables {α : Type v} {β : Type w}
variables [comm_ring α] [add_comm_group β] [module α β] (a : α)

def smul_id : β →ₗ[α] β := a • linear_map.id

lemma smul_id_apply (x : β) : ((smul_id a : β →ₗ[α] β) : β → β) x = a • x := rfl

instance smul_id.is_semiring_hom : 
is_semiring_hom (smul_id : α → β →ₗ[α] β) := {
  map_zero := begin unfold smul_id, ext, simp end,
  map_one := begin unfold smul_id, ext, simp end,
  map_add := begin unfold smul_id, simp [add_smul] end,
  map_mul := begin unfold smul_id, intros, ext, simp [mul_smul] end
}

instance smul_id.is_ring_hom : 
is_ring_hom (smul_id : α → β →ₗ[α] β) := {
  map_one := smul_id.is_semiring_hom.map_one,
  map_add := smul_id.is_semiring_hom.map_add,
  map_mul := smul_id.is_semiring_hom.map_mul
}

instance : algebra α (β →ₗ[α] β) := 
{ to_fun := smul_id,
  commutes' := 
  begin 
    intros a f, 
    unfold smul_id, 
    ext, 
    simp, 
  end,
  smul_def' := 
  begin
    intros a f, 
    unfold smul_id, 
    ext, 
    simp, 
  end
}

end smul_id