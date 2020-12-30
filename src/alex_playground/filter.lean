import data.real.basic
import order.lattice
noncomputable theory


section curried

variables {α α' β γ δ : Type*}

class curried (α β γ δ : Type*) := 
(comp (f : γ → δ) : α → β)

instance curried_base : curried (α → γ) (α → δ) γ δ := ⟨λ f g x, f (g x)⟩

instance curried_induction [curried α β γ δ] : curried (α' → α) (α' → β) γ δ :=
⟨λ f g x, curried.comp f (g x)⟩

end curried

example: curried.comp (nat.succ) (λ x y z : ℕ, 0) = (λ x y z : ℕ, 1) := rfl



universe variables u v w x

-- Need filters for non-sets! (Mario already proposed that refactoring)
-- Add non-empty axiom?
structure filter (α : Type*) [partial_order α] :=
(elements : set α)
(nonempty : ∃ x, x ∈ elements)
(exists_inf (x y : α) : x ∈ elements → y ∈ elements → ∃ z, z ≤ x ∧ z ≤ y ∧ z ∈ elements)
(mem_elements_of_le (x y : α) : x ∈ elements → x ≤ y → y ∈ elements)

instance {α : Type*} [partial_order α] : has_mem α (filter α) := ⟨λ U F, U ∈ F.elements⟩

namespace filter
variables {α : Type u} 
variables [partial_order α] {f g : filter α} {s t : α}

open set

@[simp] protected lemma mem_mk {t : set α} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t := iff.rfl

@[simp] protected lemma mem_elements : s ∈ f.elements ↔ s ∈ f := iff.rfl

lemma filter_eq : ∀{f g : filter α}, f.elements = g.elements → f = g
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.elements = g.elements :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by simp only [filter_eq_iff, ext_iff, filter.mem_elements]

@[ext]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
filter.ext_iff.2

lemma mem_sets_of_superset : ∀{x y : α}, x ∈ f → x ≤ y → y ∈ f :=
f.mem_elements_of_le

section principal

/-- The principal filter of `s` is the set of all elements larger than or equal to `s`. -/
def principal (s : α) : filter α :=
{ elements := {t | s ≤ t},
  nonempty := ⟨s, le_refl s⟩,
  exists_inf := λ x y hx hy, ⟨s, hx, hy, le_refl s⟩,
  mem_elements_of_le := λ x y hx hxy, le_trans hx hxy }

localized "notation `𝓟` := filter.principal" in filter

instance [inhabited α]: inhabited (filter α) :=
⟨𝓟 (default α)⟩

instance : complete_lattice (filter α) := sorry
end principal

open_locale filter

def at_top [preorder α] : filter (set α) := ⨅ a, 𝓟 (Ici a)


end filter


def filter.Limsup (f : filter (set ℝ)) : ℝ := Inf { a | {n | n ≤ a} ∈ f }


variables {α α' β γ δ : Type*} [partial_order β]

def filter.map (f : filter (set ℝ)) [curried α β ℝ Prop] (u : α) : filter β := sorry

def limsup (f : filter (set ℝ)) [curried α β ℝ Prop] (u : α) : ℝ := (f.map u).Limsup





def at_top [has_bot α] [partial_order β] [preorder γ] [curried α β ℝ Prop] : filter β := 
  ⨅ a : ℝ, filter.principal (curried.comp (λ x, a ≤ x) (⊥ : α))


-- section semilattice_inf

-- variables {α : Type u} 
-- variables [semilattice_inf α] {f g : filter α} {s t : α}

-- open semilattice_inf

-- namespace filter

-- def of_semilattice (α : Type*) [semilattice_inf α] (elements : set α) 
--   (inf_in_elements : ∀ x y, x ∈ elements → y ∈ elements → semilattice_inf.inf x y ∈ elements) 
--   (in_elements_of_le : ∀ x y, x ∈ elements → x ≤ y → y ∈ elements) : 
--   filter α :=

-- example: semilattice_inf (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop) := by apply_instance

-- def of_set (α : Type*) (elements : set (set α)) 
--   (inf_in_elements : ∀ x y, x ∈ elements → y ∈ elements → x ∩ y ∈ elements) 
--   (in_elements_of_le : ∀ x y, x ∈ elements → x ⊆ y → y ∈ elements) : 
--   filter (set α) :=
-- of_semilattice (set α) elements inf_in_elements in_elements_of_le

-- end filter

-- def solution (f : ℝ → ℝ) := 
-- { a : ℝ // a = filter.at_bot.liminf (λ x, f x)}


def solution (f : ℝ → ℝ) := 
Σ' a : ℝ, a = filter.at_bot.liminf (λ x, f x)



#check filter.liminf

#check optimize (λ (x : ℝ) (y : ℝ) (h : x + y ≤ 0), x - y)

