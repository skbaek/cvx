namespace optimization

structure var :=
(name : string)
(type : Type)

structure named_prod (name : string) (α : Type) (β : Type) :=
(fst : α) 
(rest : β)

def domain : list var → Type
| [] := unit
| (v :: vs) := named_prod v.name v.type (domain vs)

structure constraint (vars : list var) :=
(name : string)
(predicate : domain vars → Prop)

structure problem :=
(vars : list var)
(obj_type : Type)
(obj_fun : domain vars → obj_type)
(constrs : list (constraint vars))

def problem.domain (p : problem) := domain p.vars

structure problem.solution (p : problem) [has_le p.obj_type] :=
(point : p.domain)
(feasability : ∀ c ∈ p.constrs, constraint.predicate c point)
(optimality : ∀ x, p.obj_fun x ≤ p.obj_fun x)

structure equiv (p q : problem) [has_le p.obj_type] [has_le q.obj_type] :=
(to_fun : p.solution → q.solution)
(inv_fun : q.solution → p.solution)

infix `≃`:10 := equiv

def my_equiv (p : problem) (c : string) (v : string)
  (f : constraint p.vars)
  (hf : f.predicate = (λ p, p.get v = 0))
  (h : f ∈ p.constrs) :
sorry := sorry
--p ≃ p.remove_constr (p.subst_var v 0) `$v = 0`


/-
def my_equiv (p : problem) (v : var) (h : `$v = 0` ∈ constr p₁)) :
p ≃ p.remove_constr (p.subst_var v 0) `$v = 0`

-/


end optimization


