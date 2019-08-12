import data.finsupp 

lemma finsupp.on_finset_mem_support {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : α → β) (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) : 
  ∀ a : α, a ∈ (finsupp.on_finset s f hf).support ↔ f a ≠ 0 :=
by { intro, rw [finsupp.mem_support_iff, finsupp.on_finset_apply] }


lemma finsupp.on_finset_support {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : α → β) (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) : 
  (finsupp.on_finset s f hf).support = s.filter (λ a, f a ≠ 0) :=
begin
  ext a,
  rw [finsupp.on_finset_mem_support, finset.mem_filter], 
  specialize hf a,
  finish
end

definition finsupp.on_finset' {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : (↑s : set α) → β) : α →₀ β :=
finsupp.on_finset s (λ a, dite (a ∈ s) (λ h, f ⟨a, h⟩) (λ _, 0)) 
  (λ a ha, not_not.1 (λ x, ha (dif_neg x)))

lemma finsupp.on_finset'_mem_support {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : (↑s : set α) → β) : 
  ∀ a : α, a ∈ (finsupp.on_finset' s f).support ↔ dite (a ∈ s) (λ h, f ⟨a,h⟩ ≠ 0) (λ _, false) :=
begin
  intros a,
  rw [finsupp.mem_support_iff, finsupp.on_finset', finsupp.on_finset_apply],
  by_cases h_cases : a ∈ s;
  simp [dif_pos, dif_neg, h_cases]
end

lemma finsupp.on_finset'_apply {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β] 
  (s : finset α) (f : (↑s : set α) → β) : 
  ∀ a : α, (finsupp.on_finset' s f : α → β) a = dite (a ∈ s) (λ h, f ⟨a,h⟩) (λ _, 0) :=
by { intro, rw [finsupp.on_finset', finsupp.on_finset_apply] }
