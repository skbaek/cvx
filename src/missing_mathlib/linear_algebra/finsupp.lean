import linear_algebra.finsupp
import missing_mathlib.data.finsupp
import missing_mathlib.algebra.big_operators
import missing_mathlib.linear_algebra.basic

import analysis.complex.polynomial

lemma finsupp.total_on_finset {α β γ : Type*} 
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [ring β] [add_comm_group γ] [module β γ]
  (s : finset α) (f : α → β) (g : α → γ) (hf : ∀ a, f a ≠ 0 → a ∈ s): 
  finsupp.total α γ β g (finsupp.on_finset s f hf) = 
    finset.sum (finset.filter (λ (a : α), f a ≠ 0) s) (λ (x : α), f x • g x) :=
begin
  rw finsupp.total_apply,
  dunfold finsupp.sum,
  simp [finsupp.on_finset_apply],
  rw finsupp.on_finset_support
end
