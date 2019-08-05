import data.list.basic

universe u

theorem list.foldl_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) 
  (a : α) (l : list α) (h : ∀ x y, g (f x y) = f' (g x) (g y)) : 
  g (list.foldl f a l) = list.foldl f' (g a) (l.map g) :=
begin
  induction l generalizing a,
  { simp },
  { simp [list.foldl_cons, l_ih, h] }
end

lemma function.injective_foldl_comp {α : Type*} {l : list (α → α)} {f : α → α}
  (hl : ∀ f ∈ l, function.injective f) (hf : function.injective f): 
  function.injective (@list.foldl (α → α) (α → α) function.comp f l) :=
begin
  induction l generalizing f,
  { exact hf },
  { apply l_ih (λ _ h, hl _ (list.mem_cons_of_mem _ h)),
    apply function.injective_comp hf,
    apply hl _ (list.mem_cons_self _ _) }
end