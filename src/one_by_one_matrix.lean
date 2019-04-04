import .mat

-- TODO: move
lemma fin.eq_zero_fin1 (i : fin 1) : i = 0 :=
begin
  rw fin.eq_iff_veq,
  apply nat.eq_zero_of_le_zero (nat.le_of_lt_succ i.2)
end

namespace one_by_one_matrix
/-
def coe {α : Type*} : (matrix (fin 1) (fin 1) α) → α := λ A, A 0 0

instance coe_instance (α : Type*) : has_coe (matrix (fin 1) (fin 1) α) α := 
  ⟨coe⟩

@[simp] lemma coe_add (α : Type*) [has_add α] (A B : matrix (fin 1) (fin 1) α) : 
  coe (A + B) = coe A + coe B :=
by simp [coe]

@[simp] lemma coe_smul (α : Type*) [has_mul α] (a : α) (A : matrix (fin 1) (fin 1) α) : 
  coe (a • A) = a * coe A :=
by simp [coe, has_scalar.smul]

@[simp] lemma coe_smul' (α : Type*) [has_mul α] (a : α) (A : matrix (fin 1) (fin 1) α) : 
  coe (a • A) = a * coe A :=
by simp [coe, has_scalar.smul]

@[simp] lemma coe_neg (α : Type*) [has_neg α] (A : matrix (fin 1) (fin 1) α) : 
  coe (- A) = - coe A :=
by simp [coe]

@[simp] lemma coe_zero (α : Type*) [has_zero α] : 
  coe (0 : matrix (fin 1) (fin 1) α) = 0 :=
by simp [coe]
-/

@[simp] lemma transpose (α : Type*) [ring α] (A : matrix (fin 1) (fin 1) α) : Aᵀ = A :=
begin
  ext i j,
  unfold matrix.transpose,
  rw [fin.eq_zero_fin1 i, fin.eq_zero_fin1 j]
end


end one_by_one_matrix