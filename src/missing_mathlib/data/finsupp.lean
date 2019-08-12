import data.finsupp 

definition finsupp.on_finset' {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : (↑s : set α) → β) : α →₀ β :=
finsupp.on_finset s (λ a, dite (a ∈ s) (λ h, f ⟨a, h⟩) (λ _, 0)) 
  (λ a ha, not_not.1 (λ x, ha (dif_neg x)))

lemma finsupp.on_finset'_support {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : (↑s : set α) → β) : 
  ∀ a : α, a ∈ (finsupp.on_finset' s f).support ↔ dite (a ∈ s) (λ h, f ⟨a,h⟩ ≠ 0) (λ _, false) :=
begin
  sorry
end