import data.list.basic
.nat .logic

variables {α : Type} {k m n : nat} 
  {as bs cs : list α}

namespace list 
 
@[simp] def get [has_zero α] : nat → list α → α  
| _ []      := (0 : α)
| 0 (i::is) := i 
| (n+1) (i::is) := get n is 

@[simp] lemma get_nil [has_zero α] {k} : get k [] = (0 : α) := 
begin cases k; refl end

lemma get_eq_zero_of_ge [has_zero α] : 
  ∀ {k} {as : list α}, k ≥ as.length → get k as = (0 : α) 
| 0 [] h1 := rfl
| 0 (a::as) h1 := by cases h1
| (k+1) [] h1 := rfl
| (k+1) (a::as) h1 := 
  begin
    apply @get_eq_zero_of_ge k,
    apply nat.succ_le_succ_iff.elim_left h1,
  end

lemma mem_get_of_lt [has_zero α] : 
  ∀ {k} {as : list α}, 
  k < as.length → as.get k ∈ as 
| _ [] h1 := by cases h1
| 0 (a::as) _ := or.inl rfl
| (k+1) (a::as) h1 := 
  begin
    simp only [get], apply or.inr,
    apply mem_get_of_lt,
    apply nat.lt_of_succ_lt_succ h1,
  end

lemma mem_get_or_get_eq_zero [has_zero α] (k : nat) (as : list α) :
  as.get k ∈ as ∨ as.get k = 0 :=
begin
  by_cases h1 : k < as.length; [left, right],
  apply mem_get_of_lt h1, rw not_lt at h1,
  apply get_eq_zero_of_ge h1
end

def equiv [has_zero α] (as1 as2 : list α) : Prop :=
∀ m, as1.get m = as2.get m

infix `≃`: 100 := equiv 

lemma equiv_refl [has_zero α] : as ≃ as := λ k, rfl

lemma equiv_symm [has_zero α] {as bs : list α} :
  as ≃ bs → bs ≃ as :=
λ h1 k, (h1 k).symm

lemma equiv_trans [has_zero α] {as bs cs : list α} :
  as ≃ bs → bs ≃ cs → as ≃ cs :=
λ h1 h2 k, eq.trans (h1 k) (h2 k)

lemma equiv_of_eq [has_zero α] : as = bs → as ≃ bs := 
begin intro h1, rw h1, apply equiv_refl end

lemma eq_of_equiv [has_zero α] :
  ∀ {as1 as2 : list α}, as1.length = as2.length → 
  as1 ≃ as2 → as1 = as2 
| []     [] h1 h2 := rfl
| (_::_) [] h1 h2 := by cases h1
| [] (_::_) h1 h2 := by cases h1
| (a1::as1) (a2::as2) h1 h2 := 
  begin
    apply fun_mono_2 (h2 0) (eq_of_equiv _ _),
    simp only [add_left_inj, add_comm, length] at h1,
    exact h1, intro m, apply h2 (m+1) 
  end

@[simp] def neg [has_neg α] : list α → list α 
| []      := [] 
| (a::as) := -a::(neg as)

@[simp] lemma get_neg [add_group α] : 
  ∀ {k} {as : list α}, as.neg.get k = -(as.get k) 
| _ []          := by simp only [get_nil, neg, neg_zero]
| 0 (a::as)     := by simp only [get, neg, neg_zero]
| (k+1) (a::as) := by simp only [get, neg, @get_neg k as]

@[simp] lemma length_neg [has_neg α] : 
  ∀ as : list α, (as).neg.length = as.length 
| []      := rfl 
| (a::as) := 
  by simp only [list.length, length_neg as, neg]

@[simp] def add [has_add α] : list α → list α → list α 
| as1 [] := as1
| [] as2 := as2
| (a1::as1) (a2::as2) := ((a1+a2)::(add as1 as2))

@[simp] lemma nil_add [has_add α] {as : list α} :
add [] as = as := by cases as; refl

@[simp] lemma add_nil [has_add α] {as : list α} :
add as [] = as := by cases as; refl

lemma get_add [add_monoid α] :
  ∀ {k : nat} {is js : list α}, 
  (add is js).get k = (is.get k + js.get k) :=
begin
  intros k, induction k; intros is js;
  cases is with i is; cases js with j js;
  simp only [add, add_nil, get, get_nil, add_zero, zero_add],
  apply k_ih
end

lemma length_add [has_add α] : 
  ∀ {is js : list α}, (add is js).length = max is.length js.length 
| [] js := 
  begin 
    simp only [nil_add, length, add],
    rw max_eq_right, apply nat.zero_le 
  end 
| is [] :=
  begin 
    simp only [add_nil, length, add],
    rw max_eq_left, apply nat.zero_le 
  end 
| (i::is) (j::js) := 
  by simp only [length, add, nat.max_succ_succ, @length_add is js]

lemma length_add_eq_length_left [has_add α] {as bs : list α} {m : nat} :
  as.length = m → bs.length = m → (add as bs).length = as.length :=
begin
  intros h1 h2, rw length_add, 
  apply max_eq_left (le_of_eq _),
  apply eq.trans h2 h1.symm
end

lemma length_add_eq_length_right [has_add α] {as bs : list α} {m : nat} :
  as.length = m → bs.length = m → (add as bs).length = bs.length :=
begin
  intros h1 h2, rw length_add, 
  apply max_eq_right (le_of_eq _),
  apply eq.trans h1 h2.symm
end

lemma add_assoc [add_group α] (a b c : list α) :
  list.add (list.add a b) c = list.add a (list.add b c) := 
begin
  apply eq_of_equiv, simp only [length_add, max_assoc],
  intro m, simp only [get_add, add_assoc]
end

lemma add_equiv_add [add_monoid α] {a b c d : list α} : 
  a ≃ b → c ≃ d → (add a c) ≃ (add b d) := 
begin
  intros h1 h2 m, simp only [get_add],
  apply fun_mono_2 (h1 m) (h2 m)
end

lemma add_left_neg [add_group α]: add (neg as) as ≃ [] :=
begin intro k, rw [get_nil, get_add, get_neg, add_left_neg] end

def dot_prod [has_zero α] [has_add α] [has_mul α] : list α → list α → α 
| [] []     := 0 
| [] (_::_) := 0 
| (_::_) [] := 0 
| (a1::as1) (a2::as2) :=
  (a1 * a2) + dot_prod as1 as2

end list