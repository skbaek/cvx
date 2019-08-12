import linear_algebra.finsupp
import missing_mathlib.data.finsupp
import missing_mathlib.algebra.big_operators

lemma finsupp.total_on_finset {α β γ : Type*} 
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [ring β] [add_comm_group γ] [module β γ]
  (s : finset α) (f : α → β) (g : α → γ) (hf : ∀ a, f a ≠ 0 → a ∈ s): 
  finsupp.total α γ β g (finsupp.on_finset s f hf) = 
    finset.sum (set.finite.to_finset (finite_set_of s hf : set.finite {a | f a ≠ 0})) (λ (x : α), f x • g x) :=
begin
  rw finsupp.total_apply,
  dunfold finsupp.sum,
  simp [finsupp.on_finset_apply],
  rw finsupp.on_finset_support,
end

#check finset.sum_filter'
#check @finset.sum_attach
#check finset.mem_filter


set_option pp.proofs true
lemma finsupp.total_on_finset' {α β γ : Type*} 
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [ring β] [add_comm_group γ] [module β γ]
  (s : finset α) (f : {x // x ∈ s} → β) (g : α → γ) (hg : ∀ a, g a ≠ 0): 
  finsupp.total α γ β g (finsupp.on_finset' s f) = 

finset.sum s.attach
      (λ x : {x // x ∈ s}, f x • g x.1)

   :=
begin
  unfold finsupp.on_finset',
  rw finsupp.total_on_finset,
  have := finset.sum_attach,
  have h_dite : ∀ x : {x // x ∈ s}, 
      dite (x.1 ∈ s) (λ (h₀ : x.1 ∈ s), f ⟨x.1, h₀⟩) (λ (_x : x.1 ∉ s), 0) = f x := 
  begin
    rintros ⟨_, _⟩,
    exact dif_pos _, 
  end,
  conv {to_rhs, congr, skip, funext, rw ←h_dite},
  rw @finset.sum_attach _ _ _ _ 
      (λ (x : α), dite (x ∈ s) (λ (h₀ : x ∈ s), f ⟨x, h₀⟩) (λ _, 0) • g x),
  rw ←finset.sum_filter' s,
  congr,
  have := finite_set_of s (finsupp.on_finset'._proof_1 s f),
end