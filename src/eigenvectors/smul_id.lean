import linear_algebra.basic
import ring_theory.algebra
import deprecated.ring

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

def smul_id_ring_hom : α →+* (β →ₗ[α] β) := ring_hom.of (smul_id : α → β →ₗ[α] β)


-- TODO: merge with this?
#check module.endomorphism_algebra 
#check algebra_map

instance : algebra α (β →ₗ[α] β) := 
  (smul_id_ring_hom : α →+* (β →ₗ[α] β)).to_algebra'
  begin 
    intros a f, 
    simp only [smul_id_ring_hom, ring_hom.coe_of], 
    dunfold smul_id, 
    ext, 
    simp, 
  end

end smul_id