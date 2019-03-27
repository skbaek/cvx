
import tactic.interactive
import .mat
import .inner_product_space

-- TODO: move
@[reducible] def rowvec (α : Type) [ring α] (n : nat) : Type := mat α 1 n
@[reducible] def colvec (α : Type) [ring α] (n : nat) : Type := mat α n 1

namespace one_by_one_matrix

def coe {α : Type*} [ring α] : (mat α 1 1) → α := λ A, A 0 0

instance coe_instance (α : Type*) [ring α]: has_coe (mat α 1 1) α := 
  ⟨coe⟩

@[simp] lemma coe_add (α : Type*) [ring α] (A B : mat α 1 1) : 
  coe (A + B) = coe A + coe B :=
by simp [coe]

@[simp] lemma coe_smul (α : Type*) [ring α] (a : α) (A : mat α 1 1) : 
  coe (a • A) = a • coe A :=
by simp [coe, has_scalar.smul]

end one_by_one_matrix

variables {α : Type} [ring α] {k m n : nat}

-- TODO: move
local infix ` ⬝ ` : 70 := matrix.mul
def inner (v w : colvec α n) : α := wᵀ ⬝ v
notation `⟪` v `, ` w `⟫` := inner v w

-- TODO: move
def colvec.last (x : colvec α (n+1)) : α := x 0 n
def colvec.butlast (x : colvec α (n+1)) : colvec α n := λ ⟨i,hi⟩ ⟨j,hj⟩, x i j

-- TODO: norm
--set_option trace.class_instances true

/-
instance colvec.add_comm_group (α : Type*) [ring α] : add_comm_group (colvec α n) :=
begin
  letI := @ring.to_add_comm_group α _,
  have h : add_comm_group (fin 1 → α), from @pi.add_comm_group (fin 1) (λ_, α) _,
  have h : add_comm_group (fin n → fin 1 → α), from @pi.add_comm_group (fin n) (λ_, fin 1 → α) _,
  exact h,
end-/

--TODO: move
lemma fin1_eq_zero (i : fin 1): i = 0 :=
begin
  apply fin.eq_of_veq,
  apply (nat.eq_zero_of_le_zero (nat.le_of_lt_succ j.2))
end

noncomputable instance colvec.real_inner_product_space : real_inner_product_space (colvec ℝ n) :=
{
  inner := inner,
  inner_add_left := 
  begin 
    dsimp [inner, colvec, mat], 
    intros u v w, 
    rw matrix.mul_add', 
    dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe], --TODO WTF?
    rw one_by_one_matrix.coe_add, 
  end,
  inner_smul_left := 
  begin
    dsimp [inner, colvec, mat], 
    intros,
    rw matrix.mul_smul, 
    dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe], --TODO WTF?
    rw one_by_one_matrix.coe_smul, 
    simp
  end,
  inner_comm := 
  begin
    dsimp [inner, colvec, mat], 
    intros,
    unfold mat.transpose,
    rw [←matrix.transpose_transpose (matrix.transpose w ⬝ v), matrix.transpose_mul, matrix.transpose_transpose w],
    refl
  end,
  inner_self_nonneg := 
  begin
    dsimp [inner, colvec, mat, matrix.mul], 
    dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
    intros,
    apply finset.zero_le_sum,
    intros i _,
    apply mul_self_nonneg
  end,
  eq_zero_of_inner_self_eq_zero := 
  begin
    dsimp [inner, colvec, mat, matrix.mul],
    dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
    intros v h,
    rw finset.sum_eq_zero_iff_of_nonneg at h,
    { ext i j,
      rw fin1_eq_zero j,
      apply eq_zero_of_mul_self_eq_zero,
      convert h _ _,
      simp },
    { intros i hi,
      apply mul_self_nonneg }
  end
}