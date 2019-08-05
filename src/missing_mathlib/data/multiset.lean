import data.multiset

@[reducible] noncomputable def multiset.to_list {α : Type*} (s : multiset α) := classical.some (quotient.exists_rep s)

@[simp] lemma multiset.to_list_zero {α : Type*} : (multiset.to_list 0 : list α) = [] :=
  (multiset.coe_eq_zero _).1 (classical.some_spec (quotient.exists_rep multiset.zero))

lemma multiset.coe_to_list {α : Type*} (s : multiset α) : (s.to_list : multiset α) = s :=
classical.some_spec (quotient.exists_rep _)

lemma multiset.mem_to_list {α : Type*} (a : α) (s : multiset α) : a ∈ s.to_list ↔ a ∈ s :=
by rw [←multiset.mem_coe, multiset.coe_to_list]

/-
@[simp] lemma multiset.to_list_cons {α : Type*} (a : α) (as : list α) : 
  (multiset.to_list (a :: as) : list α) = [] := sorry
-/


lemma multiset.prod_eq_zero {α : Type*} [comm_semiring α] {s : multiset α} (h : (0 : α) ∈ s) : 
  multiset.prod s = 0 :=
begin
  rcases multiset.exists_cons_of_mem h with ⟨s', hs'⟩,
  simp [hs', multiset.prod_cons]
end