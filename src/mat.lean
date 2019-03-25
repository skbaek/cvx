import data.matrix data.real.basic

variables {k m n : nat}
variables {α : Type} [ring α]

@[reducible] def mat (α : Type) [ring α] (m n : nat) : Type := 
matrix (fin m) (fin n) α 

@[reducible] def vec (α : Type) [ring α] (n : nat) : Type := (fin n) → α 

local notation v `⬝` w := matrix.vec_mul_vec v w --TODO: matrix.vec_mul_vec is not the dot product but the outer vector product

namespace mat

def mem (a : α) (A : mat α m n) : Prop :=
∃ i : fin m, ∃ j : fin n, a = A i j

instance has_mem : has_mem α (mat α m n) := ⟨mem⟩  

def trace_aux (A : mat α n n) : ∀ m, m ≤ n → α 
| 0 h     := 0
| (m+1) h :=
  have h' : m < n := nat.lt_of_succ_le h,
  A ⟨m,h'⟩ ⟨m,h'⟩ + trace_aux m (le_trans (nat.le_succ _) h)

def trace (A : mat α n n) : α := trace_aux A n (le_refl _)

def pos_semidef {α : Type} [ordered_ring α] (A : mat α n n) : Prop := 
∀ x : vec α n, ∀ a ∈ (x ⬝ (matrix.mul_vec A x)), (0 : α) ≤ a 

def pos_def {α : Type} [ordered_ring α] (A : mat α n n) : Prop := 
∀ x : vec α n, x ≠ 0 → ∀ a ∈ (x ⬝ (matrix.mul_vec A x)), (0 : α) < a

def loewner {α : Type} [ordered_ring α] (A B : mat α n n) : Prop := 
pos_semidef (A - B)

infix `≼` : 1200 := loewner
infix `≽` : 1200 := λ A B, loewner B A

def strict_loewner [ordered_ring α] (A B : mat α n n) : Prop := 
A ≼ B ∧ A ≠ B

infix `≺` : 1200 := loewner
infix `≻` : 1200 := λ A B, strict_loewner B A

def transpose (A : mat α m n) : mat α n m := 
matrix.transpose A

postfix `ᵀ` : 1500 := transpose

def get_diagonal (A : mat α m m) : mat α m m | i j := 
if i = j 
then A i j
else 0

def lower_triangle (A : mat α m m) : mat α m m | i j := 
if i = j 
then 1 
else if i > j 
     then A i j 
     else 0

end mat

def lists_to_mat_core {m n : nat} (ls : list (list α)) 
  (i : fin m) (j : fin n) : option α :=
do l ← ls.nth i.val, l.nth j.val

def lists_to_mat (m n : nat) 
  (ls : list (list α)) : mat α m n | i j := 
match lists_to_mat_core ls i j with 
| none     := 0
| (some a) := a
end
