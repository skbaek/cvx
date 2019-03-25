import .inner_product_space .cone data.real.basic .matrix

open matrix

noncomputable theory

variables {k m n : nat}

namespace cone_program

variables {α : Type} [add_comm_group α] [real_inner_product_space α] (K : set α) (K' : set α)

structure primal (α : Type) (m : nat) := 
(obf : α)
(lhs : vector α m)
(rhs : vector ℝ m)

def mat_mul_vec (A : vector α m) (x : α) : (vector ℝ m) := A.map (λ (a : α), ⟪ a, x ⟫)

local infix `⊚` : 70 := mat_mul_vec

def vec_mul_mat (A : vector α m) (y : vector ℝ m) : α := (vector.map₂ (•) y A).sum

local infix `⊙` : 70 := vec_mul_mat

def primal.feasible (P : primal α m) (x : α) : Prop := 
let ⟨c,A,b⟩ := P in
A ⊚ x = b ∧ x ∈ K

def primal.optimal (P : primal α n) (x : α) : Prop := 
let c := P.obf in
P.feasible K x ∧ ∀ y, P.feasible K y → ⟪c, x⟫ ≤ ⟪c, y⟫

structure dual (α : Type) (m : nat) := 
(obf : vector real m)
(lhs : vector α m)
(rhs : α)


def dual.feasible (D : dual α m) (y : vector real m) : Prop := 
let ⟨b,A,c⟩ := D in
c - A ⊙ y ∈ K'.

def dual.optimal (D : dual α m) (y : vector real m) : Prop := 
let b := D.obf in
D.feasible K' y ∧ ∀ x, D.feasible K' x → b ⬝ x ≤ b ⬝ y

def primal.to_dual : primal α m → dual α m
| ⟨c,A,b⟩ := ⟨b,A,c⟩ 

lemma lower_bound {α : Type} [hα : add_comm_group α] [hα' : real_inner_product_space α] 
(K : set α) (hK : cone K)
(P : primal α m) (x : α) (h_x_opt : P.optimal K x) 
(y : vector ℝ m) (hy : P.to_dual.feasible (dual_cone K) y) : 
P.to_dual.obf ⬝ y ≤ ⟪ P.obf, x ⟫ :=
begin
  let c := P.obf,
  let A := P.lhs,
  let b := P.rhs,

  have h : - b ⬝ y = ⟪ c, x ⟫ - ⟪ A ⊙ y + c, x ⟫ + y ⬝ (A ⊚ x - b),
  begin
    simp [real_inner_product_space.inner_add_left],
  end,

end

end cone_program