import data.matrix data.real.basic


universes u v

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

-- TODO: move / generalize in matrix.lean
lemma mul_zero' [ring α] (M : matrix m n α) : M.mul (0 : matrix n l α) = 0 :=
begin 
  ext i j, 
  unfold matrix.mul, 
  simp
end

lemma mul_add' [ring α] (L : matrix m n α) (M N : matrix n l α) : L.mul (M + N) = L.mul M + L.mul N :=
begin 
  ext i j, 
  unfold matrix.mul, 
  simp [left_distrib, finset.sum_add_distrib] 
end

lemma add_mul' [ring α] (M N : matrix m n α) (L : matrix n l α) : (M + N).mul L = M.mul L + N.mul L :=
begin 
  ext i j, 
  unfold matrix.mul, 
  simp [right_distrib, finset.sum_add_distrib] 
end

@[simp] lemma mul_neg [ring α] (M : matrix m n α) (N : matrix n l α) : M.mul (-N) = - M.mul N :=
begin 
  ext i j,
  unfold matrix.mul,
  simp,
end

@[simp] lemma neg_mul [ring α] (M : matrix m n α) (N : matrix n l α) : (-M).mul N = - M.mul N :=
begin 
  ext i j,
  unfold matrix.mul,
  simp,
end

lemma mul_sub' [ring α] (L : matrix m n α) (M N : matrix n l α) : L.mul (M - N) = L.mul M - L.mul N :=
by simp [mul_add']

lemma sub_mul' [ring α] (M N : matrix m n α) (L : matrix n l α) : (M - N).mul L = M.mul L - N.mul L :=
by simp [add_mul']

@[simp] lemma mul_smul [comm_ring α] (M : matrix m n α) (a : α) (N : matrix n l α) : M.mul (a • N) = a • M.mul N :=
begin
  ext i j,
  unfold matrix.mul,
  unfold has_scalar.smul,
  rw finset.mul_sum,
  congr,
  ext,
  ring
end

@[simp] lemma smul_mul [comm_ring α] (M : matrix m n α) (a : α) (N : matrix n l α) : (a • M).mul N = a • M.mul N :=
begin
  ext i j,
  unfold matrix.mul,
  unfold has_scalar.smul,
  rw finset.mul_sum,
  congr,
  ext,
  ring
end

local postfix `ᵀ` : 1500 := transpose

lemma transpose_transpose (M : matrix m n α) : 
  Mᵀᵀ = M :=
by ext; unfold transpose

lemma transpose_mul [comm_ring α] (M : matrix m n α) (N : matrix n l α) : 
  (M.mul N)ᵀ = Nᵀ.mul Mᵀ  := 
begin
  ext i j, 
  unfold matrix.mul,
  unfold transpose,
  congr,
  ext,
  ring
end

lemma transpose_add [has_add α] (M : matrix m n α) (N : matrix m n α) : 
  (M + N)ᵀ = Mᵀ + Nᵀ  := 
begin
  ext i j, 
  dsimp [transpose], 
  refl
end

lemma transpose_smul [has_mul α] (a : α) (M : matrix m n α) : 
  (a • M)ᵀ = a • Mᵀ  := 
by ext i j; refl

@[simp] lemma transpose_neg [comm_ring α] (M : matrix m n α) : 
  (- M)ᵀ = - Mᵀ  := 
by ext i j; refl

@[simp] lemma transpose_zero [has_zero α] : (0 : matrix m n α)ᵀ = 0 := 
by ext i j; refl

lemma eq_iff_transpose_eq (M : matrix m n α) (N : matrix m n α) : M = N ↔ Mᵀ = Nᵀ := 
begin 
  split,
  { intro h, ext i j, rw h },
  { intro h, ext i j, rw [←transpose_transpose M,h,transpose_transpose] },
end

end matrix


variables {k m n : nat}
variables {α : Type} [ring α]

@[reducible] def mat (α : Type) [ring α] (m n : nat) : Type := 
matrix (fin m) (fin n) α 

@[reducible] def vec (α : Type) [ring α] (n : nat) : Type := (fin n) → α 

local notation v `⬝` w := matrix.vec_mul_vec v w --TODO: matrix.vec_mul_vec is not the dot product but the outer vector product

namespace mat

def mem (a : α) (A : mat α m n) : Prop :=
∃ i : fin m, ∃ j : fin n, a = A i j

instance has_mem : has_mem α (mat α m n) := ⟨mem⟩  

def trace_aux (A : mat α n n) : ∀ m, m ≤ n → α 
| 0 h     := 0
| (m+1) h :=
  have h' : m < n := nat.lt_of_succ_le h,
  A ⟨m,h'⟩ ⟨m,h'⟩ + trace_aux m (le_trans (nat.le_succ _) h)

def trace (A : mat α n n) : α := trace_aux A n (le_refl _)

def pos_semidef {α : Type} [ordered_ring α] (A : mat α n n) : Prop := 
∀ x : vec α n, ∀ a ∈ (x ⬝ (matrix.mul_vec A x)), (0 : α) ≤ a 

def pos_def {α : Type} [ordered_ring α] (A : mat α n n) : Prop := 
∀ x : vec α n, x ≠ 0 → ∀ a ∈ (x ⬝ (matrix.mul_vec A x)), (0 : α) < a

def loewner {α : Type} [ordered_ring α] (A B : mat α n n) : Prop := 
pos_semidef (A - B)

infix `≼` : 1200 := loewner
infix `≽` : 1200 := λ A B, loewner B A

def strict_loewner [ordered_ring α] (A B : mat α n n) : Prop := 
A ≼ B ∧ A ≠ B

infix `≺` : 1200 := loewner
infix `≻` : 1200 := λ A B, strict_loewner B A

postfix `ᵀ` : 1500 := matrix.transpose

def get_diagonal (A : mat α m m) : mat α m m | i j := 
if i = j 
then A i j
else 0

def lower_triangle (A : mat α m m) : mat α m m | i j := 
if i = j 
then 1 
else if i > j 
     then A i j 
     else 0

end mat

def lists_to_mat_core {m n : nat} (ls : list (list α)) 
  (i : fin m) (j : fin n) : option α :=
do l ← ls.nth i.val, l.nth j.val

def lists_to_mat (m n : nat) 
  (ls : list (list α)) : mat α m n | i j := 
match lists_to_mat_core ls i j with 
| none     := 0
| (some a) := a
end
