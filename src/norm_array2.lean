import tactic.norm_num .array2

open tactic




#check @array.ext'
meta def prove_array₂_mul_array₂_eq (Ax Bx Cx : expr) : nat → nat → tactic expr 
| 0 n := sorry




meta def norm_array₂_mul_array₂ (Ax Bx : expr) : tactic (expr × expr) :=
do `(array₂ %%αx %%mx %%nx) ← infer_type Ax, 
   m ← eval_expr nat mx, 
   n ← eval_expr nat nx, 
   Cx ← mk_meta_array₂ αx m n,
   Px ← prove_array₂_mul_array₂_eq Ax Bx Cx m n,
   return (Cx, Px)
  
