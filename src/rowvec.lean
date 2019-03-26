
import tactic.interactive
import .mat
import .inner_product_space

-- TODO: move
@[reducible] def rowvec (α : Type) [ring α] (n : nat) : Type := mat α 1 n
@[reducible] def colvec (α : Type) [ring α] (n : nat) : Type := mat α n 1
instance one_by_one_matrix (α : Type*) [ring α]: has_coe (mat α 1 1) α := 
  ⟨λ A, A 0 0⟩

variables {α : Type} [ring α] {n : nat}

-- TODO: move
local infix ` ⬝ ` : 70 := matrix.mul
local notation x , `ᵀ` := matrix.transpose x
def inner (v w : colvec α n) : α := wᵀ ⬝ v
notation `⟪` v `, ` w `⟫` := inner v w

-- TODO: move
def colvec.last (x : colvec α (n+1)) : α := x 0 n
def colvec.butlast (x : colvec α (n+1)) : colvec α n := λ ⟨i,hi⟩ ⟨j,hj⟩, x i j

-- TODO: norm
set_option trace.class_instances true

instance colvec.add_comm_group (α : Type*) [ring α] : add_comm_group (colvec α n) :=
begin
  letI := @ring.to_add_comm_group α _,
  have h : add_comm_group (fin 1 → α), from @pi.add_comm_group (fin 1) (λ_, α) _,
  have h : add_comm_group (fin n → fin 1 → α), from @pi.add_comm_group (fin n) (λ_, fin 1 → α) _,
  exact h,
end

noncomputable instance colvec.real_inner_product_space : real_inner_product_space (colvec ℝ n) :=
{
  inner := inner,
  inner_add_left := begin dsimp [inner, colvec, mat], intros u v w, rw @matrix.mul_add n 1 _ _ ℝ (@ring.to_semiring ℝ (real.ring ℝ)) u v w, end,
  inner_smul_left := sorry,
  inner_comm := sorry,
  inner_self_nonneg := sorry,
  eq_zero_of_inner_self_eq_zero := sorry
}