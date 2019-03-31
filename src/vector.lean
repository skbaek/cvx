import data.vector .list 

variables {α : Type} {k m n : nat}

open tactic

namespace vector

def zero [has_zero α] (m) : vector α m := 
vector.repeat 0 m

instance has_zero [has_zero α] : has_zero (vector α m) := ⟨zero m⟩ 

lemma zero_succ [has_zero α] {m} : 
  (0 : vector α (m+1)) = (0 : α)::(0 : vector α m) := rfl

def neg [has_neg α] (v : vector α m) : vector α m := 
⟨v.val.neg, eq.trans (list.length_neg _) v.property⟩ 

instance has_neg [has_neg α]: has_neg (vector α m) := ⟨neg⟩  

lemma val_neg [has_neg α] (v : vector α k) :
  (-v).val = list.neg v.val := rfl

def add [has_add α] (v w : vector α k) : vector α k :=
⟨ list.add v.val w.val, 
  calc (list.add (v.val) (w.val)).length 
      = max (list.length (v.val)) (list.length (w.val)) : list.length_add
  ... = v.val.length : 
        begin
          apply max_eq_left (le_of_eq _),
          apply eq.trans w.property v.property.symm
        end
  ... = k : v.property ⟩ 

instance has_add [has_add α] : has_add (vector α k) := ⟨add⟩ 

lemma val_add [has_add α] (v w : vector α k) :
  (v + w).val = list.add v.val w.val := rfl

lemma add_assoc [add_group α] (a b c : vector α m) :
  a + b + c = a + (b + c) :=
begin apply subtype.eq, simp only [val_add], apply list.add_assoc end

lemma val_zero_equiv_nil [has_zero α] {m} :
  (@zero α _ m).val ≃ [] := 
begin
  intro k, simp only [zero, repeat, list.get_nil],
  cases list.mem_get_or_get_eq_zero k (list.repeat (0 : α) m),
  apply list.eq_of_mem_repeat h, exact h
end

lemma zero_add [add_group α] (a : vector α m) : 0 + a = a :=
begin
  apply subtype.eq, simp only [val_add], apply list.eq_of_equiv,
  { apply list.length_add_eq_length_right 
    (zero m).property a.property },
  { apply list.equiv_trans 
    (list.add_equiv_add val_zero_equiv_nil list.equiv_refl) 
    (list.equiv_of_eq list.nil_add) }
end

lemma add_zero [add_group α] (a : vector α m) : a + 0 = a :=
begin
  apply subtype.eq, simp only [val_add], apply list.eq_of_equiv,
  { apply list.length_add_eq_length_left 
    a.property (zero m).property },
  { apply list.equiv_trans 
    (list.add_equiv_add list.equiv_refl val_zero_equiv_nil) 
    (list.equiv_of_eq list.add_nil) }
end

lemma add_left_neg [add_group α] (a : vector α m) : -a + a = 0 := 
begin
  apply subtype.eq, simp only [val_neg, val_add],
  apply list.eq_of_equiv,
  { rw list.length_add_eq_length_left _ a.property,
    rw list.length_neg,
    apply eq.trans a.property (zero m).property.symm,
    rw list.length_neg, apply a.property },
  { apply list.equiv_trans list.add_left_neg 
    (list.equiv_symm val_zero_equiv_nil) }
end

instance add_group [add_group α] : add_group (vector α m) :=
{ add := add,
  add_assoc := add_assoc,
  zero := zero m,
  zero_add := zero_add,
  add_zero := add_zero,
  neg := neg,
  add_left_neg := add_left_neg }

def dot_prod [ring α] (v w : vector α k) : α :=
list.dot_prod v.val w.val 

infix `⬝` := dot_prod

--def zero_dot_prod [ring α] (v : vector α k) : 0 ⬝ v = 0 := sorry
--def dot_prod_zero [ring α] (v : vector α k) : v ⬝ 0 = 0 := sorry

def sum [add_monoid α] : ∀ {k}, vector α k → α 
| 0     _ := 0
| (k+1) v := v.head + @sum k v.tail

end vector

/- (mk_meta_vector k) returns the expr of a vector of length k,
   where the expr of each entry is a metavariable. -/ 
meta def mk_meta_vector (αx : expr) : nat → tactic expr 
| 0     := to_expr ``(@vector.nil %%αx)
| (k+1) := 
  do x ← mk_meta_var αx,
     vx ← mk_meta_vector k,
     to_expr ``(@vector.cons %%αx %%`(k) %%x %%vx)

/- (vector₂.mk_meta m n) returns the expr of an m × n vector₂,
   where the expr of each entry is a metavariable. -/ 
meta def mk_meta_vector₂ (αx : expr) : nat → nat → tactic expr 
| 0     n := to_expr ``(@vector.nil (vector %%αx %%`(n)))
| (m+1) n :=  
  do v₁x ← mk_meta_vector αx n,
     v₂x ← mk_meta_vector₂ m n,
     to_expr ``(@vector.cons (vector %%αx %%`(n)) %%`(m) %%v₁x %%v₂x)

def vector₂ (α : Type) (m n : nat) : Type := vector (vector α n) m