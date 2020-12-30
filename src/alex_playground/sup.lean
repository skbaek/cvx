import data.real.basic
import order.lattice
import tactic.interactive
noncomputable theory


section curried

universe variables u v w x
variables {α : Sort u}  {β : Type w}

class curried (α : Sort u) (β : Type w) :=
(uncurried_arg_type : Sort x)
(uncurry (f : α): uncurried_arg_type → β)

notation `↿`:max x:max := curried.uncurry x

instance curried_base : curried (α → β) β := ⟨α, id⟩

instance curried_induction {α' : α → Type v} [∀ a, curried (α' a) β] : 
  curried (Π (a : α), α' a) β :=
⟨Σ' (a : α), curried.uncurried_arg_type (α' a) β, λ f p, ↿(f p.1) p.2⟩

def range [curried α β] (f : α) := set.range (@curried.uncurry α β _ f)

end curried


def optimal_value {α : Type*} [curried α ℝ] (f : α) : ℝ := Sup (range f)

def optimal_point {α : Type*} [curried α ℝ] (f : α) := {x : curried.uncurried_arg_type α ℝ // ↿f x = optimal_value f}

def optimal_point' {α : Type*} [curried α ℝ] (f : α) := {x : curried.uncurried_arg_type α ℝ // ∀ y, ↿f x ≥ ↿f y}


notation `subject_to ` binders ` maximize ` f:(scoped Q, Q) := optimal_point' f



def my_optimal_point1 : optimal_point (λ (x y : ℝ) (h : x ≤ 0) (h : y ≤ 0), x + y) := sorry

def my_optimal_point2 : optimal_point (λ (x : ℝ) (h : x ≤ 0), x) :=
⟨(psigma.mk 0 (le_refl 0) : Σ' x : ℝ, x ≤ 0), sorry⟩


def my_optimal_point3 : subject_to (x y : ℝ) (h : x ≤ 0) (h : y ≤ 0) maximize x + y := sorry



def transform {α β : Type*} [curried α ℝ] [curried β ℝ] 
  (f : α) (g : β) 
  (t : curried.uncurried_arg_type α ℝ → curried.uncurried_arg_type β ℝ)
  (t' : curried.uncurried_arg_type β ℝ → curried.uncurried_arg_type α ℝ)
  (ht : ∀ x, ↿f x = ↿g (t x)) (ht' : ∀ x, ↿f (t' x) = ↿g x)
  (p : optimal_point' f) : optimal_point' g := 
⟨t p.val, λ y, begin rw [←ht, ←ht'], apply p.property (t' y) end⟩


#check (psigma.mk 3 (psigma.mk 3 rfl) : Σ' (x : ℕ), Σ' (y : ℕ), (x = y))


def my_optimal_point4 
  (h : subject_to (y : ℝ) maximize 5 + y) : 
  subject_to (x y : ℝ) (h : x = 5) maximize x + y :=
begin
  apply transform (λ (y : ℝ), 5 + y) (λ (x y : ℝ) (h : x = 5), x + y)
    (λ p, (psigma.mk 5 (psigma.mk p rfl) : Σ' (x : ℝ), Σ' (y : ℝ), (x = 5)))
    (@curried.uncurry (Π (x y : ℝ) (h : x = 5), ℝ) ℝ _ (λ (x y : ℝ) (h : x = 5), y))--(λ p, p.2.1)
    (λ p, rfl) 
    begin intro p, unfold curried.uncurry, simp, exact p.2.2.symm end,
  exact h,
end

open tactic
open expr
setup_tactic_parser

meta def get_obj_fun : expr → tactic expr
| `(optimal_point' %%a) := return a
| _ := fail "no optimization problem"

meta def get_vars : expr → list (name × expr)
| (lam var_name bi var_type body) := (var_name, var_type) :: get_vars body
| _ := []

meta def transformtac (new : pexpr) : tactic unit :=
do
  old_obj_fun <- target >>= get_obj_fun,
  new_obj_fun <- to_expr new >>= get_obj_fun, 
  old_obj_fun_type <- infer_type old_obj_fun,
  new_obj_fun_type <- infer_type new_obj_fun,
  trace (get_vars old_obj_fun),
  trace (get_vars new_obj_fun),
  refine ``(@transform 
    %%new_obj_fun_type %%old_obj_fun_type _ _
    %%new_obj_fun %%old_obj_fun 
    _ --(λ x, ⟨_, _, _⟩ : ℝ → Σ' (x y : ℝ), x = 5) 
    _ --(λ x : Σ' (x y : ℝ), x = 5, (x.cases_on (λ x yh, _) : ℝ)) 
    _ _ _)


meta def tactic.interactive.transformtac (new : parse texpr) : tactic unit :=
  transformtac new

#check tactic.apply
#check tactic.interactive.apply
#check tactic.interactive.cases


def my_optimal_point4 : 
  subject_to (x y : ℝ) (h : x = 5) maximize x + y :=
begin
  transformtac (subject_to (y : ℝ) maximize 5 + y),
  
  --refine @transform (ℝ → ℝ) (Π (x y : ℝ) (h : x = 5), ℝ) _ _ _ _ _ _ _ _ _,
end