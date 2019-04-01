import data.rat tactic.norm_num .misc .string 

universes u v 

variables {α : Type} 

def N (α : Type) : Type := nat → α 

def NN (α : Type) : Type := nat → nat → α 

def N.eq (n : nat) (a b : N α) : Prop :=
∀ j < n, a j = b j

def NN.eq (m n : nat) (A B : NN α) : Prop :=
∀ i < m, ∀ j < n, A i j = B i j

def NN.mul_aux [ring α] (A B : NN α) (i j : nat) : nat → α 
| 0       := 0
| (m + 1) := NN.mul_aux m + (A i m * B m j)

def NN.mul [ring α] (k m n : nat) (A B : NN α) : NN α | i j := 
NN.mul_aux A B i j m 

lemma N.eq_zero (a b : N α) : 
  N.eq 0 a b := forall_lt_zero _

lemma N.eq_succ {n : nat} {a b : N α} : 
  a n = b n → N.eq n a b → N.eq n.succ a b := 
forall_lt_succ _ n

lemma NN.eq_zero {n : nat} {A B : NN α} : 
  NN.eq 0 n A B := forall_lt_zero _

lemma NN.eq_succ {m n : nat} {A B : NN α} : 
  N.eq n (A m) (B m) → NN.eq m n A B → 
  NN.eq m.succ n A B := forall_lt_succ _ m

lemma NN.eq_symm {m n : nat} {A B : NN α} : 
NN.eq m n A B → NN.eq m n B A := 
begin
  intros h1 i hi j hj,  
  exact (h1 i hi j hj).symm
end

lemma NN.eq_trans {m n : nat} {A B C : NN α} : 
NN.eq m n A B → NN.eq m n B C → NN.eq m n A C :=
begin
  intros h1 h2 i hi j hj, 
  apply eq.trans (h1 i hi j hj) (h2 i hi j hj)
end

def N.of_list [inhabited α] : list α → nat →  α 
| []      _     := inhabited.default α
| (a::as) 0     := a
| (a::as) (j+1) := N.of_list as j

def NN.of_lists (α : Type) [inhabited α] : list (list α) → NN α 
| []      _     _ := inhabited.default α
| (l::ll) 0     j := N.of_list l j 
| (l::ll) (i+1) j := NN.of_lists ll i j 

instance N.eq.decidable [decidable_eq α] (n : nat) :
  decidable_rel (@N.eq α n) := 
by {intros A B, apply forall_lt.decidable} 

instance NN.eq.decidable [decidable_eq α] (m n : nat) :
  decidable_rel (@NN.eq α m n) := 
by {intros A B, apply forall_lt.decidable} 


/- repr -/

def N.cell_size [has_repr α] (b : N α) : nat → nat 
| 0     := 0 
| (n+1) := max (N.cell_size n) (repr $ b n).length

def NN.cell_size [has_repr α] (A : NN α) : nat → nat → nat  
| 0     n := 0
| (m+1) n := max (NN.cell_size m n) (N.cell_size (A m) n)

def N.repr [has_repr α] (k : nat) (b : N α) : nat → string 
| 0     := "|" 
| (n+1) := N.repr n ++ " " ++ (repr $ b n).resize k ++ " |"

def NN.repr_aux [has_repr α] (k : nat) (A : NN α) : nat → nat → string 
| 0     n := "" 
| (m+1) n := NN.repr_aux m n ++ "\n" ++ N.repr k (A m) n

def NN.repr (m n : nat) [has_repr α] (A : NN α) : string := 
NN.repr_aux (NN.cell_size A m n) A m n  


/- norm -/

open tactic expr

/- (N.mk_meta n) returns ⌜g : nat → α⌝, where ⌜f j⌝ is 
   a unique metavariable for any j < n, and ⌜g j⌝ = x 
   otherwise. -/
meta def N.mk_meta (τx tx : expr) : nat → tactic expr 
| 0     := to_expr ``(λ x : nat, (%%tx : %%τx))
| (n+1) := 
  do gx ← N.mk_meta n,
     sx ← mk_meta_var τx, 
     to_expr ``(update %%τx %%`(n) %%sx %%gx)

/- (mk_meta m n) returns ⌜f : NN α⌝, where each 
   ⌜f i j⌝ is a unique metavariable for any 
   i < m and j < n, and ⌜f i j⌝ = x otherwise. -/
meta def NN.mk_meta (αx ax : expr) : nat → nat → tactic expr 
| 0     _ := to_expr ``(λ i j : nat, (%%ax : %%αx))
| (m+1) n := 
  do fx ← NN.mk_meta m n,
     gx ← N.mk_meta αx ax n,
     to_expr ``(update (N %%αx) %%`(m) %%gx %%fx)
  
meta def mul_simp_lemmas : list name := 
[`NN.mul, `NN.mul_aux, `N.of_list, `NN.of_lists] 

meta def get_simp_lemmas : list name → tactic simp_lemmas 
| []      := return simp_lemmas.mk
| (n::ns) := 
  do s ← get_simp_lemmas ns,
     s.add_simp n

meta def simp_mul (x : expr) : tactic (expr × expr) := 
do s ← get_simp_lemmas mul_simp_lemmas,
   simplify s [] x

/- Return ⌜h : t = s⌝ -/
meta def prove_eq (αx tx ux : expr) : tactic expr := 
do (sx,px) ← simp_mul tx,
   (rx,qx) ← norm_num sx,
   unify rx ux,
   to_expr ``(@eq.trans %%αx %%tx %%sx %%rx %%px %%qx)

/- Return ⌜h : N.eq n a b⌝ -/
meta def N.prove_eq (αx ax bx : expr) : nat → tactic expr
| 0     := return `(@N.eq_zero %%αx %%ax %%bx)
| (n+1) := 
  do px ← prove_eq αx (app ax `(n)) (app bx `(n)),
     qx ← N.prove_eq n,
     return `(@N.eq_succ %%αx %%`(n) %%ax %%bx %%px %%qx)

/- Return ⌜h : NN.eq m n A B⌝ -/
meta def NN.prove_eq (αx Ax Bx : expr) : nat → nat → tactic expr
| 0     n := return `(@NN.eq_zero %%αx %%`(n) %%Ax %%Bx)
| (m+1) n :=
  do px ← N.prove_eq αx (app Ax `(m)) (app Bx `(m)) n,
     qx ← NN.prove_eq m n,
     return `(@NN.eq_succ %%αx %%`(m) %%`(n) %%Ax %%Bx %%px %%qx)

/- Return ⌜B : NN α⌝ and ⌜h : NN.eq m n A B⌝ -/
meta def NN.norm (αx ax Ax : expr) (m n : nat) : tactic (expr × expr) := 
do Bx ← NN.mk_meta αx ax m n, 
   px ← NN.prove_eq αx Ax Bx m n,
   return (Bx,px)

meta def NN.equate : tactic unit :=
do `(@NN.eq %%αx %%mx %%nx %%Ax %%Bx) ← target,
   ax ← get_default αx, 
   m ← eval_expr nat mx, 
   n ← eval_expr nat nx, 
   (A'x, px) ← NN.norm αx ax Ax m n, 
   (B'x, qx) ← NN.norm αx ax Bx m n, 
   ( do is_def_eq A'x B'x, 
        pq ← to_expr ``(@NN.eq_trans %%αx %%mx %%nx %%Ax %%A'x %%Bx
               %%px (@NN.eq_symm %%αx %%mx %%nx %%Bx %%B'x %%qx)),
        apply pq, skip ) <|>
   fail "Not definitionally equal"


/- Tests -/

set_option profiler true

lemma ex1 :
NN.eq 2 2
  ( NN.mul 2 2 2
    ( NN.of_lists int 
      [ [ 9  , -7 ], 
        [ 18 , 4  ] ] )
    ( NN.of_lists int 
      [ [ -14 , 1 ], 
        [ 5   , 22 ] ] ) ) 
  ( NN.of_lists int
    [ [ -161 , -145 ],    
      [ -232 , 106  ] ] ) :=
by NN.equate

lemma ex2 :
NN.eq 3 2
  ( NN.mul 3 4 2
    ( NN.of_lists rat 
      [ [ 4.5  , -3.5 , 12.5 , 0.5 ], 
        [ -1/2 , -3/2 , -2   , 0   ], 
        [ 20   , 2    , 3    , 1   ] ] )
    ( NN.of_lists rat 
      [ [ 8    , 1/2   ], 
        [ 5/2  , -13.5 ], 
        [ 1/2  , 4     ],
        [ 21.5 , 11    ] ] ) ) 
  ( NN.of_lists rat
    [ [ 177/4 , 105 ],
      [ -35/4 , 12  ],
      [ 188   , 6   ] ] ) :=
by NN.equate

lemma ex3 :
NN.eq 3 3
  ( NN.mul 3 3 3
    ( NN.of_lists rat 
      [ [ 1/3 , -3.2   , 0.9 ], 
        [ -1/2 , 3 - 5 , -2  ], 
        [ 20   , 2     , 3.4 ] ] )
    ( NN.of_lists rat 
      [ [ 8   , 1/4 , 4/3   ], 
        [ 5/3 , 3   , 4 * 7 ], 
        [ 1/2 , 4   , 0     ] ] ) ) 
  ( NN.of_lists rat 
    [ [ -133/60 , -71/12 , -4012/45 ],
      [ -25/3   , -113/8 , -170/3   ],
      [ 4951/30 , 123/5  , 248/3    ] ] ) := 
by NN.equate

lemma ex4 :
NN.eq 4 4 
  ( NN.mul 4 4 4
    ( NN.of_lists int 
      [ [ 9   , -71 , 25  , 1  ], 
        [ -1  , -3  , -4  , 92 ], 
        [ 133 , -39 , -23 , 0  ], 
        [ 40  , 26  , 366 , 28 ] ] )
    ( NN.of_lists int 
      [ [ 16  , 1   , 55  , -11 ], 
        [ 512 , -27 , 219 , 129 ], 
        [ 1   , 8   , -89 , 5   ],
        [ 43  , 22  , 4   , 42  ] ] ) ) 
  ( NN.of_lists int 
    [ [ -36140 , 2148 , -17275 , -9091 ],
      [ 2400   , 2072 , 12     , 3468  ],
      [ -17863 , 1002 , 821    , -6609 ],
      [ 15522  , 2882 , -24568 , 5920  ] ] ) := 
by NN.equate

lemma ex5 :
NN.eq 5 5 
  ( NN.mul 5 5 5
    ( NN.of_lists int 
      [ [ 9   , -71 , 25  , 1   , 910 ], 
        [ -1  , -3  , -4  , 92  , 52  ], 
        [ 133 , -39 , -23 , 0   , -20 ], 
        [ -12 , 492 , 9   , 10 , 1929 ], 
        [ 40  , 26  , 366 , 28 , 2    ] ] )
    ( NN.of_lists int 
      [ [ 16  , 1    , 55  , -11  , 13  ], 
        [ 512 , -27  , 219 , 1921 , 212 ], 
        [ 828   , 8  , -2  , 35   , 0   ],
        [ 1   , 4283 , -89 , 5    , 431 ],
        [ 43  , 22   , 4   , 42   , 880 ] ] ) ) 
  ( NN.of_lists int
    [ [ 23623  , 26429  , -11553 , -97390  , 786296  ],
      [ -2536  , 395228 , -8684  , -3248   , 84763   ],
      [ -37744 , 562    , -1260  , -78027  , -24139  ],
      [ 342121 , 72044  , 113896 , 1026647 , 1805978 ],
      [ 317114 , 122234 , 4678   , 62540   , 19860   ] ] ) :=
by NN.equate