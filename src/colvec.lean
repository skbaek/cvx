
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

section move
variables {α : Type} [ring α] {k m n : nat}

-- TODO: move
local infix ` ⬝ ` : 70 := matrix.mul
def inner (v w : colvec α n) : α := wᵀ ⬝ v
notation `⟪` v `, ` w `⟫` := inner v w


--TODO: move
lemma fin1_eq_zero (i : fin 1): i = 0 :=
begin
  apply fin.eq_of_veq,
  apply (nat.eq_zero_of_le_zero (nat.le_of_lt_succ i.2))
end
end move

namespace colvec

variables {α : Type} [ring α] {k m n : nat} (a : α) (x y z : colvec α n)

def last (x : colvec α (n+1)) : α := x ⟨n, nat.lt_succ_self n⟩ 0
def butlast (x : colvec α (n+1)) : colvec α n := λ i j, x ⟨i.1, nat.le_succ_of_le i.2⟩ j

@[simp] lemma last_smul (c : α) (x : colvec α (n+1)) : last (c • x) = c * last x :=
by refl

@[simp] lemma butlast_smul (c : α) (x : colvec α (n+1)) : butlast (c • x) = c • butlast x :=
by ext i j; simp[butlast, (•)]

def snoc (x : colvec α n) (c : α) : colvec α (n+1) := 
λ i j, dite (i.val < n) (λhi, x ⟨i.val,hi⟩ j) (λ_, c)

@[simp] lemma last_snoc (x : colvec α n) (c : α) : last (snoc x c) = c :=
by simp [snoc, last]

@[simp] lemma butlast_snoc (x : colvec α n) (c : α) : butlast (snoc x c) = x :=
by ext i j; simp [snoc, butlast, i.2]

@[simp] lemma snoc_butlast_last (x : colvec α (n+1)) : snoc x.butlast x.last = x :=
begin
  ext i j,
  unfold snoc butlast last,
  by_cases h_cases : i.val < n, 
  { simp [h_cases] },
  { have hi : i = ⟨n, nat.lt_succ_self n⟩, 
      from (fin.eq_iff_veq _ _).2 (nat.eq_of_lt_succ_of_not_lt i.2 h_cases),
    have hj : j = 0,
      by rw fin.eq_iff_veq; exact nat.eq_zero_of_le_zero (nat.le_of_lt_succ j.2),
    simp [hi, hj] }
end

lemma inner_add_left : ⟪ x + y, z ⟫ = ⟪ x, z ⟫ + ⟪ y, z ⟫  := 
begin 
  dsimp [inner, colvec, mat],
  rw matrix.mul_add', 
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe], --TODO WTF?
  rw one_by_one_matrix.coe_add, 
end

end colvec

namespace colvec

variables {α : Type} [comm_ring α] {k m n : nat} (a : α) (x y z : colvec α n)

lemma inner_smul_left : inner (a • x) y = a * inner x y := 
begin
  dsimp [inner, colvec, mat], 
  intros,
  rw matrix.mul_smul, 
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe], --TODO WTF?
  rw one_by_one_matrix.coe_smul, 
  simp
end

lemma inner_comm : inner x y = inner y x :=
begin
  dsimp [inner, colvec, mat], 
  intros,
  rw [←matrix.transpose_transpose ((matrix.transpose y).mul x), matrix.transpose_mul, matrix.transpose_transpose y],
  refl
end

end colvec

namespace colvec

variables {α : Type} [linear_ordered_comm_ring α] {k m n : nat} (a : α) (x y z : colvec α n)

lemma inner_self_nonneg : 0 ≤ inner x x :=
begin
  dsimp [inner, colvec, mat, matrix.mul], 
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
  intros,
  apply finset.zero_le_sum,
  intros i _,
  apply mul_self_nonneg
end

lemma eq_zero_of_inner_self_eq_zero : inner x x = 0 → x = 0 :=
begin
  dsimp [inner, colvec, mat, matrix.mul],
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
  intros h,
  rw finset.sum_eq_zero_iff_of_nonneg at h,
  { ext i j,
    rw fin1_eq_zero j,
    apply eq_zero_of_mul_self_eq_zero,
    convert h _ _,
    simp },
  { intros i hi,
    apply mul_self_nonneg }
end

end colvec

noncomputable instance colvec.real_inner_product_space (n : ℕ) : real_inner_product_space (colvec ℝ n) :=
{
  inner := inner,
  inner_add_left := colvec.inner_add_left,
  inner_smul_left := colvec.inner_smul_left,
  inner_comm := colvec.inner_comm,
  inner_self_nonneg := colvec.inner_self_nonneg,
  eq_zero_of_inner_self_eq_zero := colvec.eq_zero_of_inner_self_eq_zero
}