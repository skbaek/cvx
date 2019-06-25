import .NN .misc system.io 

variables {α : Type} [has_mul α] [add_comm_monoid α] [has_le α]
variables {k m n : nat}

structure LP (α : Type) (m n : nat) := 
(obf : N α)
(lhs : NN α)
(rhs : N α)

def LP.feasible : LP α m n → N α → Prop  
| ⟨m, n, c, A, b⟩ x :=  N.le m (mul_vec n A x) b ∧ (N.le n (N.zero α) x)

def LP.is_feasible (P : LP α m n) : Prop :=
∃ x : N α, P.feasible x

instance LP.feasible.decidable [decidable_rel ((≤) : α → α → Prop)]
  (P : LP α m n) (x : N α) : decidable (P.feasible x) := 
by {cases P, unfold LP.feasible, apply_instance }
open tactic 

meta def Nx.repr (vx : expr) : nat → tactic string 
| 0       := return ""
| (k + 1) := 
  do vs ← Nx.repr k,
     a ← to_expr ``(%%vx %%`(k)) >>= eval_expr rat,
     return $ string.join [vs, " ", a.repr]

meta def NNx.repr_aux (Ax : expr) : nat → nat → tactic string 
| 0       n := return ""
| (m + 1) n :=
  do vs ← NNx.repr_aux m n,
     a ← to_expr ``(%%Ax %%`(m) %%`(n)) >>= eval_expr rat,
     return $ string.join [vs, " ", a.repr]

meta def NNx.repr (Ax : expr) (m : nat) : nat → tactic string 
| 0       := return ""
| 1       := NNx.repr_aux Ax m 0
| (n + 1) :=
  do As ← NNx.repr n,
     vs ← NNx.repr_aux Ax m n,
     return $ string.join [As, "\n", vs]

meta def put_LP : tactic (string × string × string) := 
do `((⟨_, _, %%cx, %%Ax, %%bx⟩ : LP rat %%mx %%nx).is_feasible) ← target, 
   m ← eval_expr nat mx,
   n ← eval_expr nat nx,
   cs ← Nx.repr cx n,
   As ← NNx.repr Ax m n,
   bs ← Nx.repr bx m,
   return ⟨cs, As, bs⟩ 

open tactic 

meta instance int.has_reflect : has_reflect ℤ := by tactic.mk_has_reflect_instance

meta def rat.has_reflect' : Π x : ℚ, Σ y : ℚ, Σ' h : x = y, reflected y
| ⟨x,y,h,h'⟩ := ⟨rat.mk_nat x y, by { rw [rat.num_denom',rat.mk_nat_eq] } , `(_)⟩

meta instance : has_reflect ℚ
| x :=
match rat.has_reflect' x with
| ⟨ ._, rfl, h ⟩ := h
end

meta def cvxopt_lp (cs As bs : string) : tactic string := 
unsafe_run_io $
io.cmd { 
  cmd  := "python", 
  args := ["lp.py", cs, As, bs],
  /- Change this parameter to location of lp.py-/
  cwd  := "/home/sk/Projects/cvx/src" 
}

open parser

def digits : list char := 
[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ]

def parser_digits : parser string := many_char (one_of digits)

def parser_sign : parser bool :=  
(ch '+' >> return tt) <|> (ch '-' >> return ff) <|> (return tt)

def parser_dnat : parser string := 
do d ← one_of digits,
   ch '.',
   ds ← parser_digits,
   return ⟨d::ds.data⟩

def drop_zeroes : string → string := string.drop_chars '0'

def drop_trailing_nl (s : string) : string :=
(s.reverse.drop_chars '\n').reverse 

def parser_mantissa : parser rat :=  
do b ← parser_sign, 
   ds ← parser_dnat, 
   let i := int.of_nat (drop_zeroes ds).to_nat,
   let numer : int := if b then i else -i,
   let denom : nat := 10 ^ ds.length.pred,
   return (rat.mk_nat numer denom)

def parser_magnitude : parser rat :=  
do b ← parser_sign, 
   ds ← parser_digits,
   let m : nat := 10 ^ (drop_zeroes ds).to_nat,
   return (if b then (rat.mk_nat m 1) else (rat.mk_nat 1 m))

def parser_scinot : parser rat :=  
do r ← parser_mantissa,
   ch 'e',
   s ← parser_magnitude,
   return (r * s)

def ws : parser unit := many' (ch ' ')

def parser_entry : parser rat := 
ch '[' *> ws *> parser_scinot <* ws <* ch ']' 

def parser_vector : parser (list rat) := 
sep_by (ch '\n') parser_entry  

meta def LP.show_is_feasible : tactic unit := 
do ⟨cs, As, bs⟩ ← put_LP,
   vs ← cvxopt_lp cs As bs, 
   match run_string parser_vector (drop_trailing_nl vs) with 
   | (sum.inl _)  := fail "Cannot parse vector"
   | (sum.inr rs) := 
     do vx ← to_expr ``(@N.of_list rat _ %%`(rs)),
        existsi vx, 
        exact_dec_trivial
   end

def ex_c : N rat := N.of_list [2, 1]
def ex_A : NN rat := NN.of_lists rat [[-1, 1], [-1, -1], [0, -1], [1, -2]]
def ex_b : N rat := N.of_list [1, -2, 0, 4]

example : LP.is_feasible ⟨4, 2, ex_c, ex_A, ex_b⟩ :=
by LP.show_is_feasible