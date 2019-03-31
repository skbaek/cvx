import tactic.squeeze data.rat .misc tactic.norm_num .string tactic.ring

universes u v 

variables {α : Type} [ring α]

def NN (α : Type) : Type := nat → nat → α 

open tactic expr

def update (α : Type u) (k : nat) (a : α) (f : nat → α) : nat → α := 
λ x : nat, if x = k then a else f x

/- (mk_meta_N n) returns ⌜g : nat → α⌝, where ⌜f j⌝ is 
   a unique metavariable for any j < n, and ⌜g j⌝ = x 
   otherwise. -/
meta def mk_meta_N (τx tx : expr) : nat → tactic expr 
| 0     := to_expr ``(λ x : nat, (%%tx : %%τx))
| (n+1) := 
  do gx ← mk_meta_N n,
     sx ← mk_meta_var τx, 
     to_expr ``(update %%τx %%`(n) %%sx %%gx)

/- (mk_meta m n) returns ⌜f : NN α⌝, where each 
   ⌜f i j⌝ is a unique metavariable for any 
   i < m and j < n, and ⌜f i j⌝ = x otherwise. -/
meta def mk_meta_NN (τx tx : expr) : nat → nat → tactic expr 
| 0     _ := to_expr ``(λ i j : nat, (%%tx : %%τx))
| (m+1) n := 
  do fx ← mk_meta_NN m n,
     gx ← mk_meta_N τx tx n,
     to_expr ``(update (nat → %%τx) %%`(m) %%gx %%fx)
  
def mul_aux (A B : NN α) (i j : nat) : nat → α 
| 0       := 0
| (m + 1) := mul_aux m + (A i m * B m j)

def mul (A B : NN α) (k m n : nat) : NN α | i j := 
mul_aux A B i j m 

meta def mul_simp_lemmas : list name := 
[`mul, `mul_aux, `list_to_N, `lists_to_NN] 

meta def get_simp_lemmas : list name → tactic simp_lemmas 
| []      := return simp_lemmas.mk
| (n::ns) := 
  do s ← get_simp_lemmas ns,
     s.add_simp n

meta def simp_mul (x : expr) : tactic (expr × expr) := 
do s ← get_simp_lemmas mul_simp_lemmas,
   simplify s [] x

/- Return ⌜mul A B k m n i j = C i j⌝ -/
meta def prove_entry_eq (τx ρx Ax Bx Cx : expr) (k m n i j : nat) : tactic expr := 
do tx ← return `(@mul %%τx %%ρx %%Ax %%Bx %%`(k) %%`(m) %%`(n) %%`(i) %%`(j)),
   (sx,px) ← simp_mul tx,
   rx ← return `((%%Cx : NN %%τx) %%`(i) %%`(j)),
   unify sx rx,
   return px

lemma forall_lt_zero_row_eq (A B C : NN α) (k m n i : nat) : 
  ∀ j < 0, (mul A B k m n i j) = C i j := forall_lt_zero _

lemma forall_lt_succ_row_eq {A B C : NN α} {k m n i c : nat} : 
 (mul A B k m n i c) = C i c → 
 (∀ j < c,      (mul A B k m n i j) = C i j) → 
 (∀ j < c.succ, (mul A B k m n i j) = C i j) := forall_lt_succ _ c

/- Return ⌜h : ∀ j < c, mul A B k m n i j = C i j⌝ -/
meta def prove_row_eq (τx ρx Ax Bx Cx : expr) (k m n i : nat) : nat → tactic expr
| 0     := to_expr ``(forall_lt_zero_row_eq 
    %%Ax %%Bx %%Cx %%`(k) %%`(m) %%`(n) %%`(i))
| (c+1) := 
  do 
  p1 ← prove_entry_eq τx ρx Ax Bx Cx k m n i c,
     p2 ← prove_row_eq c, 
     to_expr ``(@forall_lt_succ_row_eq %%τx %%ρx %%Ax %%Bx %%Cx 
     %%`(k)
     %%`(m)
     %%`(n)
     %%`(i)
     %%`(c)
     %%p1 %%p2)

lemma forall_lt_zero_mat_eq (A B C : NN α) (k m n c : nat) : 
  ∀ i < 0, ∀ j < c, (mul A B k m n i j) = C i j := forall_lt_zero _

lemma forall_lt_succ_mat_eq {A B C : NN α} {k m n r c : nat} : 
  (∀ j < c, (mul A B k m n r j) = C r j) → 
  (∀ i < r, ∀ j < c, (mul A B k m n i j) = C i j) → 
  (∀ i < r.succ, ∀ j < c, (mul A B k m n i j) = C i j) := forall_lt_succ _ r
  
/- Return ⌜C : NN α⌝ and ⌜h : ∀ i < r, ∀ j < c, mul A B k m n i j = C i j⌝ -/
meta def prove_mat_eq (τx ρx Ax Bx Cx : expr) (k m n : nat) : 
  nat → nat → tactic expr
| 0 c := to_expr ``(@forall_lt_zero_mat_eq 
    %%τx %%ρx %%Ax %%Bx %%Cx %%`(k) %%`(m) %%`(n) %%`(c))
| (r+1) c := 
  do 
  p1 ← prove_row_eq τx ρx Ax Bx Cx k m n r c,
     p2 ← prove_mat_eq r c,
     to_expr ``(forall_lt_succ_mat_eq %%p1 %%p2)

/- Return ⌜C : NN α⌝ and ⌜h : ∀ i < k, ∀ j < n, (mul A B k m n i j) = C i j⌝ -/
meta def norm_mat (Ax Bx : expr) (k m n : nat) : tactic (expr × expr) := 
do `(NN %%τx) ← infer_type Ax, 
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx τx),
   tx ← to_expr ``(@inhabited.default %%τx %%ix),
   rhx ← to_expr ``(ring),
   ρx ← mk_instance (app rhx τx),
   Cx ← mk_meta_NN τx tx k n, 
   px ← prove_mat_eq τx ρx Ax Bx Cx k m n k n,
   return (Cx,px)

def row_cell_size [has_repr α] (A : NN α) (m : nat) : nat → nat 
| 0     := 0 
| (n+1) := max (row_cell_size n) (repr $ A m n).length

def mat_cell_size [has_repr α] (A : NN α) : nat → nat → nat  
| 0     n := 0
| (m+1) n := max (mat_cell_size m n) (row_cell_size A m n)

def row_repr [has_repr α] (A : NN α) (k m : nat) : nat → string 
| 0     := "|" 
| (n+1) := row_repr n ++ " " ++ (repr $ A m n).resize k ++ " |"

def mat_repr_aux [has_repr α] (A : NN α) (k : nat) : nat → nat → string 
| 0     n := "" 
| (m+1) n := mat_repr_aux m n ++ "\n" ++ row_repr A k m n

def mat_repr [has_repr α] (A : NN α) (m n : nat) : string := 
mat_repr_aux A (mat_cell_size A m n) m n 

def list_to_N [inhabited α] : list α → nat →  α 
| []      _     := inhabited.default α
| (a::as) 0     := a
| (a::as) (j+1) := list_to_N as j

def lists_to_NN [inhabited α] : list (list α) → NN α 
| []      _     _ := inhabited.default α
| (l::ll) 0     j := list_to_N l j 
| (l::ll) (i+1) j := lists_to_NN ll i j 

def eq_row (i n : nat) (A B : NN α) : Prop :=
∀ j < n, A i j = B i j

instance eq_row.decidable [decidable_eq α] (i n : nat) :
  decidable_rel (@eq_row α _ i n) := 
by {intros A B, apply forall_lt.decidable} 

def eq_mat (m n : nat) (A B : NN α) : Prop :=
∀ i < m, eq_row i n A B

instance eq_mat.decidable [decidable_eq α] (m n : nat) :
  decidable_rel (@eq_mat α _ m n) := 
by {intros A B, apply forall_lt.decidable} 

def eq_mat_trans {m n : nat} {A B C : NN α} : 
  eq_mat m n A B → eq_mat m n B C → eq_mat m n A C :=
begin
  intros h1 h2 i h3 j h4, 
  apply eq.trans (h1 i h3 j h4) (h2 i h3 j h4)
end

example : 
eq_mat 3 3 
  ( 
    mul 
    (
      lists_to_NN [
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int)
      ]
    )
    (
      lists_to_NN [
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int)
      ]
    )
    3 3 3
  )
  (λ x y : nat, (3 : int)) :=
begin 
  exact_dec_trivial,
end

lemma bar {r c} {A B C : NN α} :
  A = B → eq_mat r c B C → 
  eq_mat r c A C :=
begin intros h1 h2, rw h1, exact h2 end

meta def rw_mat : tactic unit :=
do `(eq_mat %%rx %%cx (mul %%Ax %%Bx %%kx %%mx %%nx) %%Cx) ← target,
   `(NN %%τx) ← infer_type Ax, 
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx τx),
   tx ← to_expr ``(@inhabited.default %%τx %%ix),
   rhx ← to_expr ``(ring),
   ρx ← mk_instance (app rhx τx),
   k ← eval_expr nat kx,
   m ← eval_expr nat mx,
   n ← eval_expr nat nx,
   (ABx,px) ← norm_mat Ax Bx k m n,
   to_expr ``(eq_mat_trans %%px _) >>= apply,
   --to_expr ``(@bar %%τx %%ρx %%rx %%cx  
   --(mul %%Ax %%Bx %%kx %%mx %%nx)
   --%%ABx %%Cx %%px _) >>= apply,
   skip

example : 
@eq_mat rat _ 3 3 
(
  @mul rat _ 
  (
    lists_to_NN [
      ([218.21,  -393.21,    0.1937] : list rat),
      ([-131/32, 34/13 - 53, -12.943]  : list rat),
      ([303.21,  213.283,    39.42]  : list rat)
    ]
  )
  (
    lists_to_NN [
      ([438.2,     94/314, 134/23] : list rat),
      ([543/3,     2.232,  45 * 213] : list rat),
      ([94 + 61/2, 421/3,  0] : list rat)
    ]
  )
  3 3 3
)
(
  @lists_to_NN rat _ _  [
    ([489454553/20000, -18490003211/23550000, -8665587041/2300] : list rat),
    ([-651294807/52000, -47270008507/24492000, -2310482501/4784] : list rat),
    ([35275727/200, 119688116499/19625000, 9411986781/4600] : list rat)
  ]
) := 
begin
  rw_mat, 
end

#exit

example : 
  ( 
    mul 
    (
      lists_to_NN [
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int)
      ]
    )
    (
      lists_to_NN [
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int),
        ([-1,-1,-1] : list int)
      ]
    )
    3 3 3
  )
  = 
  (λ x y : nat, (3 : int)) :=
by do 
  `(mul %%Ax %%Bx _ _ _ = _) ← target,
  (A'x,px) ← norm_mat 3 3 3 Ax Bx, 
  A' ← eval_expr (NN int) A'x,
  skip
#exit

