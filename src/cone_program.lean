import .inner_product_space .cone data.real.basic .matrix

open matrix

variables {k m n : nat}

namespace cone_program

variables {α : Type} [add_comm_group α] [real_inner_product_space α] (K : set α) (K' : set α)

structure primal (α : Type) (m : nat) := 
(obf : α)
(lhs : vector α m)
(rhs : vector real m)

def primal.feasible (P : primal α m) (x : α) : Prop := 
let ⟨c,A,b⟩ := P in
(∀ i : fin m, ⟪A.nth i, x⟫ = b.nth i) ∧ x ∈ K

def primal.optimal (P : primal α n) (x : α) : Prop := 
let c := P.obf in
primal.feasible K P x ∧ (∀ y : α, primal.feasible K P y → ⟪c, x⟫ ≤ ⟪c, y⟫)

structure dual (α : Type) (m : nat) := 
(obf : vector real m)
(lhs : vector α m)
(rhs : α)

def dual.feasible (D : dual α m) (y : vector real m) : Prop := 
let ⟨b,A,c⟩ := D in
c - (vector.map₂ (•) y A).sum ∈ K'.

def dual.optimal (D : dual α m) (y : vector real m) : Prop := 
let b := D.obf in
dual.feasible K' D y ∧ (∀ x : vector real m, dual.feasible K' D x → (b ⬝ x) ≤ (b ⬝ y))

def primal.to_dual : primal α m → dual α m
| ⟨C,A,b⟩ := ⟨b,A,C⟩ 

lemma lower_bound {α : Type} [hα : add_comm_group α] [hα' : real_inner_product_space α] 
(K : set α) (hK : cone K)
(P : primal α m) (x_opt : α) (h_x_opt : primal.optimal K P x_opt) :
  let D := primal.to_dual P in 
  let K' := dual_cone K in 
  ∀ (y : vector ℝ m) (hy : dual.feasible K' D y), (D.obf ⬝ y) ≤ ⟪ P.obf, x_opt ⟫ :=
sorry

end cone_program