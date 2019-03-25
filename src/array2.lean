import data.rat .string  .array

variables {α β : Type}
variables {k m n : nat}

open nat

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

end array₂ 
