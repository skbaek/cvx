import .mat data.real.basic

-- To do : update using mat

#exit

open matrix

variables {k m n : nat}

namespace sdp

def S (n : nat) : Type := matrix real n n 

structure primal (m n : nat) := 
(obf : S n)
(lhs : vector (S n) m)
(rhs : vector real m)

def primal.feasible (P : primal m n) (X : S n) : Prop := 
let ⟨C,A,b⟩ := P in
(∀ i : fin m, ⟪A.nth i, X⟫ = b.nth i) ∧ (0 ≼ X)

def primal.optimal (P : primal m n) (X : S n) : Prop := 
let C := P.obf in
primal.feasible P X ∧ (∀ Y : S n, primal.feasible P Y → ⟪C, X⟫ ≤ ⟪C, Y⟫)

structure dual (m n : nat) := 
(obf : vector real m)
(lhs : vector (S n) m)
(rhs : S n)

def dual.feasible (D : dual m n) (y : vector real m) : Prop := 
let ⟨b,A,C⟩ := D in
(vector.map₂ const_mul y A).sum ≼ C

def dual.optimal (D : dual m n) (y : vector real m) : Prop := 
let b := D.obf in
dual.feasible D y ∧ (∀ x : vector real m, dual.feasible D x → (b ⬝ x) ≤ (b ⬝ y))

def primal.to_dual : primal m n → dual m n 
| ⟨C,A,b⟩ := ⟨b,A,C⟩ 

/- Lemma 2.12 -/
lemma optimality_condition (C A b) (X : S n) (y : vector real m) : 
  primal.feasible ⟨C,A,b⟩ X → dual.feasible ⟨b,A,C⟩ y → 
  mul (C - (vector.map₂ const_mul y A).sum) X = 0 → 
  (primal.optimal ⟨C,A,b⟩ X ∧ dual.optimal ⟨b,A,C⟩ y) := sorry

def primal.strictly_feasible (P : primal m n) (X : S n) : Prop := 
let ⟨C,A,b⟩ := P in
(∀ i : fin m, ⟪A.nth i, X⟫ = b.nth i) ∧ (0 ≺ X)

def dual.strictly_feasible (D : dual m n) (y : vector real m) : Prop := 
let ⟨b,A,C⟩ := D in
(vector.map₂ const_mul y A).sum ≺ C

/- Lemma 2.15 -/
lemma no_duality_gap (C : S n) (A : vector (S n) m) (b : vector real m) :
  (∃ X : S n, primal.strictly_feasible ⟨C,A,b⟩ X) → 
  (∃ y : vector real m, dual.strictly_feasible ⟨b,A,C⟩ y) → 
  (∃ X : S n, ∃ y : vector real m, 
    ( primal.optimal ⟨C,A,b⟩ X ∧  
      dual.optimal ⟨b,A,C⟩ y ∧ ⟪C, X⟫ = b ⬝ y ) ) := sorry

end sdp