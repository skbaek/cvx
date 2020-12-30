import data.real.basic
import tactic.interactive
import order.liminf_limsup

universe variables u v w x

-- copied from current mathlib, but changed to support sorts.
section uncurry

variables {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class has_uncurry (α : Sort*) (β : out_param Sort*) (γ : out_param Sort*) := (uncurry : α → (β → γ))

notation `↿`:max x:max := has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (Σ' (a : α), γ) δ :=
⟨λ f p, ↿(f p.1) p.2⟩

-- My own addition for dependent products:
-- instance has_uncurry_induction_dep {φ : α → Sort w} [s : ∀ a : α, has_uncurry β (φ a) δ] : 
--   has_uncurry (α → β) (Σ' (a : α), φ a) δ :=
-- ⟨λ f p, begin haveI := s p.1, exact ↿(f p.1) p.2 end⟩

instance has_uncurry_induction_dep {φ : α → Sort w} [∀ a : α, has_uncurry (φ a) γ δ] : 
  has_uncurry (Π (a : α), φ a) (Σ' (a : α), γ) δ :=
⟨λ f p, ↿(f p.1) p.2⟩

end uncurry

-- merge objfun and feasable:

def solution {α β γ : Sort*} [has_uncurry α β γ] [has_le γ] 
 (objfun : α) := 
{ x : β // 
  ∀ y : β, ↿objfun y ≤ ↿objfun x }

notation `over ` binders ` maximize ` f:(scoped Q, Q) := solution f

-- class instantiation isnt smart enough:
#check @solution _ _ _ (@has_uncurry_induction_dep _ _ _ (λ (x : ℝ), x ≥ 0 →  ℝ) (λ a, _)) _ (λ (x : ℝ), λ (h : x ≥ 0), x)
#check @solution _ _ _ _ _ (λ (x : ℝ), λ (h : x ≥ 0), x)


class myinhabited (α : Sort u) (β : out_param Sort*) :=
(default : α)

instance : myinhabited ℝ ℝ :=
{ default := 0 }

instance foo {α : Sort u} {β : Sort v} {φ : α → Sort w} [∀ n : α, myinhabited (φ n) β] : myinhabited (Π n, φ n) β :=
{ default := (λ n : α, @myinhabited.default (φ n) β _) }

#check @myinhabited.default (Π n : ℕ, ℝ) ℝ _



def mysolution : 
  over (x y : ℝ) (h : x ≤ 0 ∧ y ≤ 0)
  maximize x + y  := 
begin 
  use (0, 0),
  split,
  split,
  simp,
  simp,
  intros y hy,
  change y.1 + y.2 ≤ 0 + 0,
  change y.1 ≤ 0 ∧ y.2 ≤ 0 at hy,
  linarith,
end

#print mysolution