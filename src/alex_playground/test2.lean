open interactive (parse)
open lean.parser (ident tk)
open tactic.interactive («have»)
open tactic (get_local infer_type to_expr)
open interactive.types (texpr location)


-- Using type class inference (carrier only):

class solution_type (α : Type) :=
(carrier : Type*)
(uncurry : α → carrier → ℕ)

instance base_case : solution_type ℕ :=
{ carrier := unit,
  uncurry := λ x _, x, }

instance rec_case (β : Type*) [g : solution_type β]: solution_type (ℕ → β) :=
{ carrier := ℕ × g.carrier,
  uncurry := λ (f : ℕ → β) (c : ℕ × g.carrier), solution_type.uncurry (f c.1) c.2  }

def solution {α : Type*} (objfun: α) [t : solution_type α] := 
{ x : t.carrier // let f := solution_type.uncurry objfun in ∀ x' : t.carrier, f x' ≤ f x}

set_option pp.implicit true

#reduce solution 3 -- unit; λ _, 3
#reduce solution (λ x, x + 3) -- nat x unit; λ z, z.1 + 3
#reduce solution (λ x y : ℕ, x + y) -- nat x nat x unit; λ z, z.1.1 + z.1.2

-- Using type class inference (carrier only):

class solution_type (α : Type) :=
(carrier : Type*)

instance base_case : solution_type ℕ :=
{ carrier := unit,}

instance rec_case (β : Type*) [g : solution_type β]: solution_type (ℕ → β) :=
{ carrier := ℕ × g.carrier  }

def solution {α : Type*} (objfun: α) [t : solution_type α] := t 

set_option pp.implicit true

#reduce solution 3 -- unit
#reduce solution (λ x, x + 3) -- nat x unit
#reduce solution (λ x y : ℕ, x + y) -- nat x nat x unit



-- Using type class inference:

class solution_type {α : Type} (x : α) :=
(carrier : Type*)
(objfun : carrier → ℕ)

instance base_case (x : ℕ) : solution_type x :=
{ carrier := unit,
  objfun := λ _, x }

instance rec_case {β : Type*} (f : ℕ → β) [g : Π x : ℕ, solution_type (f x)]: solution_type f :=
{ carrier := unit,
  objfun := λ _, x }

def solution {α : Type*} (objfun: α) [t : solution_type objfun] := t 

set_option pp.implicit true

#check solution 3
#check solution (λ x, x + 3)

-- Using tactics:

-- meta def tactic.blah (i: pexpr) (e : pexpr) : tactic unit :=
--  to_expr ``(∀ (x : %%i), %%e) >>= tactic.exact

meta def tactic.blah (i: pexpr) (e : pexpr) : tactic unit :=
do 
 s <- to_expr (expr.pi `x binder_info.default ``(ℕ) ``(%%e)),
 tactic.exact  s

 

meta def tactic.interactive.blah  (i : parse texpr) (q : parse (tk "with" *> texpr)) : tactic unit :=
tactic.blah i q

lemma ss : begin blah (ℕ) with (x = 0), end := begin sorry end

example (a b j k : ℤ) (h₁ : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  add_eq h₁ h₂,
  exact this
end




def foo {α : Type} (P Q : α → Prop) : Prop := (∃ x, P x) ∧ (∀ x, (P x → Q x))


notation `𝔽` binders `, ` s:(scoped Q, Q) ` >>' ` r:(scoped P, P) := foo s r

variables {α : Type} (P Q : α → Prop)

#check 𝔽 x, P x >>' Q x

def blah {α : Type*} : α → Prop := sorry

notation [parsing_only] `over` binders 
`maximize` f:(scoped P, P) 
`subject` s:(scoped P, P) := (f, s)

#check over (x y : ℕ) maximize x + y subject x - y > 0

#print notation

#check subtype

def problem := subtype (λ x, subtype (λ y, x + y > 0))

def x : problem := ⟨ 1, by simp⟩

def problem1 := @psigma ℕ (λ (x : ℕ), x>0)

def problem2 := Σ' (x : ℕ), Σ' (y : ℕ), ∀ x' y', x - y ≥ x' - y'


def objfun := λ (x : ℕ), λ (y : ℕ), x + y

def largest {β : Type*} [has_le β] (f : ℕ → β) := Σ' (x : ℕ), ∀ x', f x' ≤ f x

def problem3 := largest (λ (x : ℕ), largest (λ (y : ℕ), x + y))