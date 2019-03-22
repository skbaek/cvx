import .vector 
import linear_algebra.basic

variables {k m n : nat} {α β : Type} [ring α] [ring β]

open tactic vector

def matrix (α : Type) [ring α] (m n : nat) : Type := vector (vector α n) m

namespace matrix

instance add_group [add_group α] : add_group (matrix α m n) := 
vector.add_group

lemma tail_zero : tail (0 : matrix α (m+1) n) = (0 : matrix α m n) := rfl
lemma head_zero : head (0 : matrix α (m+1) n) = (0 : vector α n) := rfl

def mul_vec : ∀ {k m}, matrix α k m → vector α m → vector α k 
| 0 _ _ _     := nil   
| (k+1) m A x := vector.cons (A.head ⬝ x) (mul_vec A.tail x)

lemma zero_mul_vec {v : vector α n} :
 ∀ {m}, mul_vec (0 : matrix α m n) v = (0 : vector α m) 
| 0 := begin simp only [mul_vec], refl end 
| (m+1) := 
  begin
    simp only [mul_vec], 
    rw [tail_zero, @zero_mul_vec m, 
      head_zero, vector.zero_dot_prod],
    apply (vector.zero_succ).symm,
  end

def split_col : ∀ {m n}, matrix α m (n+1) → vector α m × matrix α m n 
| 0 n A := (nil,nil)
| (m+1) n A := 
  let (c,A') := split_col A.tail in
  (c.cons A.head.head, A'.cons A.head.tail)

def vec_mul {m} : ∀ {n}, vector α m → matrix α m n → vector α n 
| 0     x A := nil   
| (n+1) x A := 
  let (y,A') := split_col A in 
  vector.cons (x ⬝ y) (vec_mul x A')

def pos_semidef [ordered_ring α] (A : matrix α n n) : Prop := 
∀ x : vector α n, 0 ≤ (x ⬝ (mul_vec A x)) 

def pos_def [ordered_ring α] (A : matrix α n n) : Prop := 
∀ x : vector α n, x ≠ 0 → 0 < (x ⬝ (mul_vec A x)) 

def loewner [ordered_ring α] (A B : matrix α n n) : Prop := 
pos_semidef (A - B)

infix `≼` : 1200 := loewner
infix `≽` : 1200 := λ A B, loewner B A

def strict_loewner [ordered_ring α] (A B : matrix α n n) : Prop := 
A ≼ B ∧ A ≠ B

infix `≺` : 1200 := loewner
infix `≻` : 1200 := λ A B, strict_loewner B A


def tail_tail (A : matrix α (m+1) (n+1)) : matrix α m n := 
  (split_col A.tail).snd

def trace : ∀ {n}, matrix α n n → α  
| 0     _ := 0 
| (n+1) A := A.head.head + trace (tail_tail A)

def cons_col : ∀ {m n}, vector α m → matrix α m n → matrix α m (n+1) 
| 0 n x A     := nil
| (m+1) n x A := vector.cons (A.head.cons x.head) (cons_col x.tail A.tail)

def mul : ∀ {k m n : nat}, matrix α k m → matrix α m n → matrix α k n 
| k m 0 A B     := vector.repeat vector.nil k
| k m (n+1) A B := 
  let (x,B') := split_col B in 
  cons_col (mul_vec A x) (mul A B')

def transpose : ∀ {n}, matrix α m n → matrix α n m 
| 0 _     := vector.nil 
| (n+1) A := 
  let (x,A') := split_col A in 
  vector.cons x (transpose A')

postfix `ᵀ` : 1200 := transpose

def inner_prod (X Y : matrix α n n) : α := 
trace (mul Xᵀ Y)

notation `⟪` X `,` Y `⟫` := inner_prod X Y 

def map (f : α → β) : ∀ {m n}, matrix α m n → matrix β m n 
| 0 n A     := nil 
| (m+1) n A := (A.head.map f)::(map A.tail)

def const_mul (a : α) (A : matrix α m n) : matrix α m n :=
map (λ x, a * x) A


instance has_mul (α : Type*) [comm_ring α] (n : ℕ) : has_mul (matrix α n n) := {
  mul := mul
}

instance monoid (α : Type*) [comm_ring α] (n : ℕ) : monoid (matrix α n n) := sorry

instance add_comm_group (α : Type*) [comm_ring α] (m n : ℕ) : add_comm_group (matrix α m n) := sorry

instance module (α : Type*) [comm_ring α] (m n : ℕ) : module α (matrix α m n) := sorry

instance vector_space (α : Type*) [discrete_field α] (m n : ℕ) : vector_space α (matrix α m n) := sorry

end matrix