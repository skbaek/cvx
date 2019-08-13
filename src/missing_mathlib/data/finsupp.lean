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
