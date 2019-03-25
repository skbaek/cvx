import .mat data.real.basic

variables {α : Type} [ordered_ring α]
{k m n : nat}

structure lp (α : Type) [ordered_ring α] (m n : nat) := 
(obf : vec α n)
(lhs : mat α m n)
(rhs : vec α m)

open mat


-- To do : update using mat

#exit
def feasible : lp α m n → vec α n → Prop | P x := 
let A := P.lhs in
let b := P.rhs in
matrix.mul_vec A x ≤* b

lemma farkas (A : mat real m n) (b : vector real m) : 
  (∃ x : vector real n, matrix.mul_vec A x = b ∧ x.nonneg) ∨ 
  (∃ y : vector real m, (vec_mul y A).nonneg ∧ 0 < y ⬝ b) := sorry

