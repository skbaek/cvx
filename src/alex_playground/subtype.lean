
inductive var : Type*
| X : var 
| Y : var 
| Z : var

open var

def var_type : var → Type*
| X := ℕ
| Y := ℕ
| Z := ℕ 

inductive condition_id : Type* 
| H : condition_id
| G : condition_id

open condition_id

structure optimization_problem :=
(vars : Type*)
(var_type : vars → Type*)
(condition_id : Type*)
(conditions : condition_id → (Π v : vars, var_type v) → Prop)
(obj_fun_type : Type*)
(obj_fun : (Π v : vars, var_type v) → obj_fun_type)

#check optimization_problem.mk 
  var
  var_type
  condition_id
  (λ c v, match c with 
    | G := v X ≥ v Y
    | H := v X ≥ 0
    end)