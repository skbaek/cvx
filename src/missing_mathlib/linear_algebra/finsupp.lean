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

set_option class.instance_max_depth 50

lemma finsupp.total_on_finset' {α β γ : Type*} 
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [discrete_field β] [add_comm_group γ] [vector_space β γ]
  (s : finset α) (f : {x // x ∈ s} → β) (g : α → γ) (hg : ∀ a, g a ≠ 0): 
  finsupp.total α γ β g (finsupp.on_finset' s f) = 
    finset.sum s.attach (λ x : {x // x ∈ s}, f x • g x.1) :=
begin
  unfold finsupp.on_finset',
  rw finsupp.total_on_finset,
  have h_dite : ∀ x : {x // x ∈ s}, 
      dite (x.1 ∈ s) (λ (h₀ : x.1 ∈ s), f ⟨x.1, h₀⟩) (λ (_x : x.1 ∉ s), 0) = f x := 
  begin
    rintros ⟨_, _⟩,
    exact dif_pos _, 
  end,
  conv {to_rhs, congr, skip, funext, rw ←h_dite},
  rw @finset.sum_attach _ _ _ _ 
      (λ (x : α), dite (x ∈ s) (λ (h₀ : x ∈ s), f ⟨x, h₀⟩) (λ _, 0) • g x),
  rw ←@finset.sum_filter' α γ _ _ s,
  congr,
  ext x,
  by_cases h_cases : dite (x ∈ s) (λ (h : x ∈ s), f ⟨x, h⟩) (λ (_x : x ∉ s), 0) = 0,
  { simp [h_cases] },
  { have := vector_space.smul_neq_zero (g x) h_cases,
    specialize hg x, 
    finish }
end