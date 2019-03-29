 import .colvec
 
variables {α : Type} [ring α] {k m n : nat}

namespace rowvec

def last (x : rowvec α (n+1)) : α := x 0 ⟨n, nat.lt_succ_self n⟩
def butlast (x : rowvec α (n+1)) : rowvec α n := λ i j, x i ⟨j.1, nat.le_succ_of_le j.2⟩

@[simp] lemma butlast_transpose (x : rowvec α (n+1)): 
  colvec.butlast (xᵀ) = (rowvec.butlast x)ᵀ := 
by ext i j; simp [mat.transpose, matrix.transpose, colvec.butlast, rowvec.butlast]


-- TODO: move?
local infix ` ⬝ ` : 70 := matrix.mul

lemma mul_last_add_mul_butlast (x : rowvec α (n+1)) (y : colvec α (n+1)) :
  x.last * y.last + x.butlast ⬝ y.butlast = x ⬝ y := 
sorry

lemma last_transpose (x : rowvec α (n+1)) : colvec.last (matrix.transpose x) = rowvec.last x :=
sorry

end rowvec