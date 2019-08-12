import algebra.big_operators

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

section comm_monoid
variables [comm_monoid β]

@[to_additive finset.sum_filter']
lemma prod_filter' [decidable_eq β] (s : finset α) (f : α → β) :
  finset.prod (finset.filter (λ (x : α), f x ≠ 1) s) f = finset.prod s f :=
finset.prod_subset (finset.filter_subset s) 
    (λ x hx₁ hx₂, not_not.1 (λ h, hx₂ (finset.mem_filter.2 ⟨hx₁, h⟩)))

end comm_monoid
end finset