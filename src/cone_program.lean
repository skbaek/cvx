import .vec_cone data.real.basic

variables {k m n : nat}

namespace cone_program

structure primal (m n : nat) := 
(obf : colvec (fin n) ℝ)
(lhs : matrix (fin m) (fin n) ℝ)
(rhs : colvec (fin m) ℝ)

open matrix

variables (K : set (colvec (fin n) ℝ)) (K' : set (colvec (fin n) ℝ))

local infix ` ⬝ ` : 70 := matrix.mul
local notation x , `ᵀ` := transpose x

def primal.feasible (P : primal m n) (x : colvec (fin n) ℝ) : Prop := 
P.lhs ⬝ x = P.rhs ∧ x ∈ K

def primal.optimal (P : primal m n) (x : colvec (fin n) ℝ) : Prop := 
let c := P.obf in
P.feasible K x ∧ ∀ y, P.feasible K y → ⟪ c, x ⟫ ≤ ⟪ c, y ⟫

structure dual (m n : nat) := 
(obf : colvec (fin m) ℝ)
(lhs : matrix (fin m) (fin n) ℝ)
(rhs : colvec (fin n) ℝ)

def dual.feasible (D : dual m n) (y : colvec (fin m) ℝ) : Prop := 
D.rhs - D.lhsᵀ ⬝ y ∈ K'

def dual.optimal (D : dual m n) (y : colvec (fin m) ℝ) : Prop := 
let b := D.obf in
D.feasible K' y ∧ ∀ x, D.feasible K' x → ⟪ x, b ⟫ ≤ ⟪ y, b ⟫

def primal.to_dual (P : primal m n) : dual m n :=
⟨P.rhs, P.lhs, P.obf⟩ 

lemma cone_duality
(P : primal m n) (x : colvec (fin n) ℝ) (y : colvec (fin m) ℝ)
(hx : P.feasible K x) (hy : P.to_dual.feasible (dual_cone K) y) : 
⟪ P.to_dual.obf, y ⟫ ≤ ⟪ P.obf, x ⟫ :=
begin
  let c := P.obf,
  let A := P.lhs,
  let b := P.rhs,

  have h : ⟪ b, y ⟫ = ⟪ c, x ⟫ - ⟪ x, c - Aᵀ ⬝ y ⟫  - ⟪ y, A ⬝ x - b ⟫ ,
  {
    rw [real_inner_product_space.inner_sub_right, 
        real_inner_product_space.inner_sub_right, colvec.inner_mul],
    simp [real_inner_product_space.inner_comm x c, real_inner_product_space.inner_comm y b],
  },
  have h_ge_0: 0 ≤ ⟪ x, c - Aᵀ ⬝ y ⟫,
  { let H := hy x hx.2,
    unfold primal.to_dual at H,
    dsimp at H,
    exact H },
  have h_eq_0 : ⟪ y, A ⬝ x - b ⟫ = 0,
    by simp [hx.1],
  show ⟪ b, y ⟫ ≤ ⟪ c, x ⟫,
  calc ⟪ b, y ⟫ = ⟪ c, x ⟫ - ⟪ x, c - Aᵀ ⬝ y ⟫  - ⟪ y, A ⬝ x - b ⟫ : h
    ... = ⟪ c, x ⟫ - ⟪ x, c - Aᵀ ⬝ y ⟫                            : by rw [h_eq_0]; simp
    ... ≤ ⟪ c, x ⟫                                               : (sub_le_self_iff _).2 h_ge_0
end

end cone_program