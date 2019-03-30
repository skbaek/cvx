import .colvec .vec_dual_cone data.real.basic 

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
P.lhs ⬝ x = P.rhs ∧ x ∈ K

def primal.optimal (P : primal m n) (x : colvec ℝ n) : Prop := 
let c := P.obf in
P.feasible K x ∧ ∀ y, P.feasible K y → (c ⬝ x : ℝ) ≤ c ⬝ y

structure dual (m n : nat) := 
(obf : colvec ℝ m)
(lhs : mat ℝ m n)
(rhs : rowvec ℝ n)

def dual.feasible (D : dual m n) (y : rowvec ℝ m) : Prop := 
D.rhs - y ⬝ D.lhs ∈ K'

def dual.optimal (D : dual m n) (y : rowvec ℝ m) : Prop := 
let b := D.obf in
D.feasible K' y ∧ ∀ x, D.feasible K' x → (x ⬝ b : ℝ) ≤ y ⬝ b

def primal.to_dual (P : primal m n) : dual m n :=
⟨P.rhs, P.lhs, P.obf⟩ 

lemma cone_duality
(P : primal m n) (x : colvec ℝ n) (y : rowvec ℝ m)
(hx : P.feasible K x) (hy : P.to_dual.feasible (vec_dual_cone K) y) : 
(y ⬝ P.to_dual.obf : ℝ) ≤ P.obf ⬝ x :=
begin
  let c := P.obf,
  let A := P.lhs,
  let b := P.rhs,

  have h : y ⬝ b = c ⬝ x - (c - y ⬝ A) ⬝ x - y ⬝ (A ⬝ x - b),
  {
    rw [matrix.sub_mul', matrix.mul_sub', matrix.mul_assoc],
    simp
  },
  have h_ge_0: (0:ℝ) ≤ (c - y ⬝ A) ⬝ x,
  { let H := hy x hx.2,
    unfold primal.to_dual at H,
    simp at H,
    exact H },
  have h_eq_0: A ⬝ x - b = 0,
    by simp [hx.1],
  show (y ⬝ b : ℝ) ≤ c ⬝ x,
  calc (y ⬝ b : ℝ) = c ⬝ x - (c - y ⬝ A) ⬝ x - y ⬝ (A ⬝ x - b) : begin rw [h], refl end
    ... = c ⬝ x - (c - y ⬝ A) ⬝ x                            : 
      begin 
        rw [h_eq_0],
        dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe], --TODO WTF? 
        simp [mul_zero']
      end
    ... ≤ c ⬝ x : (sub_le_self_iff _).2 h_ge_0
end

end cone_program