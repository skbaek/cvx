 import .colvec
 
variables {α : Type} [ring α] {k m n : nat}

namespace rowvec

def last (x : rowvec α (n+1)) : α := x 0 ⟨n, nat.lt_succ_self n⟩
def butlast (x : rowvec α (n+1)) : rowvec α n := λ i j, x i ⟨j.1, nat.le_succ_of_le j.2⟩

lemma last_transpose (x : rowvec α (n+1)) : colvec.last xᵀ = rowvec.last x
:= sorry

lemma last_transpose' (x : colvec α (n+1)) : rowvec.last xᵀ = colvec.last x
:= sorry

@[simp] lemma butlast_transpose (x : rowvec α (n+1)): 
  colvec.butlast (xᵀ) = (rowvec.butlast x)ᵀ := 
by ext i j; simp [matrix.transpose, colvec.butlast, rowvec.butlast]

@[simp] lemma butlast_transpose' (x : colvec α (n+1)): 
  rowvec.butlast (xᵀ) = (colvec.butlast x)ᵀ := 
sorry

variables 

-- TODO: move?
local infix ` ⬝ ` : 70 := matrix.mul

def inner (v w : rowvec α n) : α := w ⬝ vᵀ

lemma inner_self_nonneg {α : Type} [linear_ordered_comm_ring α] (x : rowvec α n) : 0 ≤ inner x x :=
sorry

lemma inner_self_pos {α : Type} [linear_ordered_comm_ring α] {x : rowvec α n} (h : x ≠ 0) : 0 < inner x x :=
sorry


lemma mul_last_add_mul_butlast (x : rowvec α (n+1)) (y : colvec α (n+1)) :
  x.last * y.last + x.butlast ⬝ y.butlast = x ⬝ y := 
sorry


end rowvec