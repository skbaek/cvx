import .rowvec .cone data.real.basic 

variables {k m n : nat}

namespace cone_program

structure primal (m n : nat) := 
(obf : rowvec ℝ n)
(lhs : mat ℝ m n)
(rhs : colvec ℝ m)

open matrix

variables (K : set (colvec ℝ n)) (K' : set (rowvec ℝ n))

local infix ` ⬝ ` : 70 := matrix.mul
local notation x , `ᵀ` := transpose x



def primal.feasible (P : primal m n) (x : colvec ℝ n) : Prop := 
let ⟨c,A,b⟩ := P in
  A ⬝ x = b ∧ x ∈ K

def primal.optimal (P : primal m n) (x : colvec ℝ n) : Prop := 
let c := P.obf in
P.feasible K x ∧ ∀ y, P.feasible K y → (c ⬝ x : ℝ) ≤ c ⬝ y

structure dual (m n : nat) := 
(obf : colvec ℝ m)
(lhs : mat ℝ m n)
(rhs : rowvec ℝ n)

def dual.feasible (D : dual m n) (y : rowvec ℝ m) : Prop := 
let ⟨b,A,c⟩ := D in
  c - y ⬝ A ∈ K'

def dual.optimal (D : dual m n) (y : rowvec ℝ m) : Prop := 
let b := D.obf in
D.feasible K' y ∧ ∀ x, D.feasible K' x → (x ⬝ b : ℝ) ≤ y ⬝ b

def primal.to_dual : primal m n → dual m n
| ⟨c,A,b⟩ := ⟨b,A,c⟩ 

lemma cone_duality 
--TODO (hK : cone K)
(P : primal m n) (x : colvec ℝ n) (y : rowvec ℝ m)
(hx : P.feasible K x) (hy : P.to_dual.feasible (sorry /-dual_cone K-/) y) : 
(y ⬝ P.to_dual.obf : ℝ) ≤ P.obf ⬝ x :=
begin
  let c := P.obf,
  let A := P.lhs,
  let b := P.rhs,

  have h : - y ⬝ b = c ⬝ x - (y ⬝ A + c) ⬝ x + y ⬝ (A ⬝ x - b),
  begin
    simp only [real_inner_product_space.inner_add_left],
  end,

end

end cone_program