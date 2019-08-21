import set_theory.cardinal

open function lattice set
local attribute [instance] classical.prop_decidable

universes u v w x
variables {α β : Type u}

namespace cardinal

lemma mk_zero_iff_empty_set (s : set α) : cardinal.mk s = 0 ↔ s = ∅ :=
not_iff_not.1 (ne_zero_iff_nonempty.trans coe_nonempty_iff_ne_empty)

lemma nat_add (m n : ℕ) : ((m + n : ℕ) : cardinal) = (m + n : cardinal) := nat.cast_add _ _

end cardinal
