import data.rat .string .array .vector

variables {α β : Type}
variables {k m n : nat}

open nat tactic

def array₂ (m n : nat) (α : Type) : Type := array m (array n α)

namespace array₂ 

def mk (m n : nat) (a : α) : array₂ m n α :=
mk_array m (mk_array n a)

def read : array₂ m n α → fin m → fin n → α 
| A i j := array.read (array.read A i) j 

def write (A : array₂ m n α) 
  (i : fin m) (j : fin n) (a : α) : array₂ m n α := 
array.write A i ((array.read A i).write j a) 

def cell_size [has_repr α] (a₂ : array₂ m n α) : nat := 
a₂.foldl 0 (λ a₁ n, max n a₁.cell_size)

def repr_aux [has_repr α] (k : nat) (a₁ : array m α) : string := 
a₁.foldl "|" (λ a s, s ++ " " ++ (repr a).resize k ++ " |")

def repr [has_repr α] (a₂ : array₂ m n α) : string := 
let k := a₂.cell_size in
a₂.foldl "" (λ a₁ s, s ++ "\n" ++ repr_aux k a₁)

instance has_repr [has_repr α] : has_repr (array₂ m n α) := ⟨repr⟩ 
meta instance has_to_format [has_repr α] : has_to_format (array₂ m n α) := ⟨λ x, repr x⟩ 

end array₂ 

def vector₂.to_array₂ {m n : nat} (v₂ : vector₂ α m n) : array₂ m n α := 
(v₂.map (vector.to_array)).to_array

/- (mk_meta_array₂ ⌜α⌝ m n) returns the expr of an m × n vector₂,
   where the expr of each entry is a metavariable. -/ 
meta def mk_meta_array₂ (αx : expr) (m n : nat) : tactic expr :=
do v₂x ← mk_meta_vector₂ αx m n,
   return `(@vector₂.to_array₂ %%αx %%`(m) %%`(n) %%v₂x)




