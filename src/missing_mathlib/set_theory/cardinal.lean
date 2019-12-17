import set_theory.cardinal

open function lattice set
local attribute [instance] classical.prop_decidable

universes u v w x
variables {α β : Type u}

namespace cardinal

lemma mk_zero_iff_empty_set (s : set α) : cardinal.mk s = 0 ↔ s = ∅ :=
not_iff_not.1 (ne_zero_iff_nonempty.trans coe_nonempty_iff_ne_empty)

lemma nat_add (m n : ℕ) : ((m + n : ℕ) : cardinal) = (m + n : cardinal) := nat.cast_add _ _

lemma exists_nat_of_add_eq_nat {a b : cardinal} {n : ℕ} (h : a + b = n) :
  ∃ k l : ℕ, a = k ∧ b = l :=
begin
  rcases (@cardinal.lt_omega a).1 _ with ⟨k, hk⟩,
  rcases (@cardinal.lt_omega b).1 _ with ⟨l, hl⟩,
  { use k,
    use l,
    cc },
  { refine ((@cardinal.add_lt_omega_iff a b).1 _).2,
    rw h,
    apply cardinal.nat_lt_omega },
  { refine ((@cardinal.add_lt_omega_iff a b).1 _).1,
    rw h,
    apply cardinal.nat_lt_omega },
end

end cardinal
