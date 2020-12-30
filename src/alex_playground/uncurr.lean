import data.real.basic
import tactic.interactive
import order.liminf_limsup


-- copied from current mathlib
section uncurry

variables {α β γ δ : Type*}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class has_uncurry (α : Type*) (β : out_param Type*) (γ : out_param Type*) := (uncurry : α → (β → γ))

notation `↿`:max x:max := has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
⟨λ f p, ↿(f p.1) p.2⟩

end uncurry



def solution {α α' β γ : Type*} [has_uncurry α β γ] [has_uncurry α' β Prop] [has_le γ] 
 (objfun : α) (feasable : α') := 
{ x : β // 
  ↿feasable x ∧
  ∀ y : β, ↿feasable y → ↿objfun y ≤ ↿objfun x }

notation `over ` binders ` maximize ` f:(scoped Q, Q) ` subject ` p:(scoped P, P) := solution f p

def mysolution : 
  over (x y : ℝ) 
  maximize x + y 
  subject x ≤ 0 ∧ y ≤ 0 := 
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