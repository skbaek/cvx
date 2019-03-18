import .matrix data.real.basic

variables {α : Type} [ordered_ring α]
{k m n : nat}

structure lp (α : Type) [ordered_ring α] (m n : nat) := 
(obf : vector α n)
(lhs : matrix α m n)
(rhs : vector α m)

open matrix

def feasible : lp α m n → vector α n → Prop | P x := 
let A := P.lhs in
let b := P.rhs in
mul_vec A x ≤* b

lemma farkas (A : matrix real m n) (b : vector real m) : 
  (∃ x : vector real n, mul_vec A x = b ∧ x.nonneg) ∨ 
  (∃ y : vector real m, (vec_mul y A).nonneg ∧ 0 < y ⬝ b) := sorry

