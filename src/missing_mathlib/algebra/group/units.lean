import algebra.group.units

universe variables u

lemma mul_unit_eq_iff_mul_inv_eq {α : Type u} [monoid α] (a b : α) (c : units α) : 
a * c = b ↔ a = b * (@has_inv.inv (units α) _ c) :=
by rw [←units.inv_mul_cancel_right b c, units.mul_right_inj, mul_assoc, units.mul_inv, mul_one]
