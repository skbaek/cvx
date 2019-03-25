import .LDLT .mat 

variables {α β : Type}
variables {k m n : nat}

open mat tactic

meta instance int.has_reflect : has_reflect ℤ :=
by tactic.mk_has_reflect_instance

meta def rat.to_expr : rat → expr 
| ⟨i,n,_,_⟩ := `(rat.mk %%`(i) (int.of_nat %%`(n)))

def array₂.to_mat [ring α] (A : array₂ m n α) : mat α m n := A.read

meta def array.to_list_expr (a₁ : array n rat) : expr :=
a₁.iterate
 `(@list.nil rat)  
  (λ i a x₁, let x := a.to_expr in 
    `(@list.cons rat %%x %%x₁))

meta def array₂.to_lists_expr (a₂ : array₂ m n rat) : expr :=
a₂.iterate `(@list.nil (list rat))
  (λ i a₁ x₂, let x₁ := a₁.to_list_expr in 
    `(@list.append (list rat) %%x₂ [@list.reverse rat %%x₁]))

def mat.write_to_row [ring α] (A : mat α m n) 
(i : fin m) (a₁ : array n α) : array n α := 
a₁.foreach (λ j _, A i j)

def mat.write_to_array₂ [ring α] (A : mat α m n) 
(a₂ : array₂ m n α) : array₂ m n α := 
array.foreach a₂ (mat.write_to_row A)

def mat.to_array₂ [ring α] (A : mat α m n) : array₂ m n α := 
let a₂ := array₂.mk m n (0 : α) in
mat.write_to_array₂ A a₂ 

instance mat.has_repr [ring α] [has_repr α] : has_repr (mat α m n) :=
⟨λ A, repr A.to_array₂⟩ 

lemma pos_semidef_of_eq_LDLT (A L D : mat rat m m) : 
   A = L * D * Lᵀ → pos_semidef A := sorry

meta def show_psd : tactic unit := 
do `(@pos_semidef %%mx rat _ %%Ax) ← target,
   m ← eval_expr nat mx,
   A ← eval_expr (mat rat m m) Ax,
   a₂ ← return (LDLT 0 A.to_array₂),
   llx ← return a₂.to_lists_expr,
   A'x ← to_expr ``(@lists_to_mat rat _ %%mx %%mx %%llx),
   Lx ← to_expr ``(mat.lower_triangle %%A'x),
   Dx ← to_expr ``(mat.get_diagonal %%A'x),
   to_expr ``(pos_semidef_of_eq_LDLT %%Ax %%Lx %%Dx) >>= apply,
   exact_dec_trivial

meta def trace_rhs : tactic unit := 
do `(@eq (mat rat %%mx _) %%lx %%rx) ← target,
   m ← eval_expr nat mx,
   rhs ← eval_expr (mat rat m m) rx,
   trace (repr rhs)
   
meta def trace_lhs : tactic unit := 
do `(@eq (mat rat %%mx _) %%lx %%rx) ← target,
   m ← eval_expr nat mx,
   lhs ← eval_expr (mat rat m m) lx,
   trace (repr lhs)

def foo_1 : array 3 rat := ([2,-1,0] : list rat).to_array 
def foo_2 : array 3 rat := ([-1,2,-1] : list rat).to_array 
def foo_3 : array 3 rat := ([0,-1,1] : list rat).to_array 
def foo : array₂ 3 3 rat := [foo_1, foo_2, foo_3].to_array
def bar : mat rat 3 3 := foo.to_mat

example : pos_semidef bar := by show_psd