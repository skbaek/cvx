
import linear_algebra.basic
import data.real.basic
import data.set.basic
import tactic.interactive
import .inner_product_space

section

variables {α : Type*} {β : Type*} {ι : Sort _} 
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β] 
  (A : set α) (B : set α) (x : α)  

open set

-- Cones

def cone (A : set α) : Prop :=
  ∀x ∈ A, ∀(c :real), 0 ≤ c → c • x ∈ A

lemma cone_empty : 
  cone ({} : set α) := 
by finish

lemma cone_univ : 
  cone (univ : set α) := 
by finish

lemma cone_inter (hA: cone A) (hB: cone B) : 
  cone (A ∩ B) :=
λ x hx c hc,
  mem_inter (hA _ (mem_of_mem_inter_left  hx) _ hc)
            (hB _ (mem_of_mem_inter_right hx) _ hc)

lemma cone_Inter {s: ι → set α} (h: ∀ i : ι, cone (s i)) : 
  cone (Inter s) :=
by unfold cone; finish

lemma cone_union (hA: cone A) (hB: cone B) : 
  cone (A ∪ B) :=
begin
  intros x hx c hc,
  apply or.elim (mem_or_mem_of_mem_union hx),
  { intro h, 
    apply mem_union_left, 
    apply hA _ h _ hc },
  { intro h, 
    apply mem_union_right,
    apply hB _ h _ hc }
end

lemma cone_Union {s: ι → set α} (h: ∀ i : ι, cone (s i)) : 
  cone (Union s) :=
begin
  intros x hx c hc,
  apply exists.elim (mem_Union.1 hx),
  intros i hi,
  apply mem_Union.2,
  use i,
  apply h i _ hi _ hc
end

lemma cone_subspace {s : subspace ℝ α} : 
  cone (s.carrier) :=
λ x hx c hc, s.smul c hx

lemma cone_contains_0 (hA : cone A) : 
  A ≠ ∅ ↔ (0 : α) ∈ A :=
begin
 apply iff.intro,
 { intros h, 
   apply exists.elim (exists_mem_of_ne_empty h), 
   intros x hx, rw ←zero_smul ℝ, 
   apply hA x hx 0 (le_refl 0) },
 { intros h, 
   exact ne_empty_of_mem h }
end

lemma cone_0 : cone ({0} : set α) :=
begin
  intros x hx c hc,
  apply mem_singleton_of_eq,
  convert smul_zero c,
  exact eq_of_mem_singleton hx
end

end


def norm_cone (α : Type*) [normed_space ℝ α] : set (α × ℝ) :=
{ x : α × ℝ | ∥ x.1 ∥ ≤ x.2 }

-- TODO: better seperate space & norm?

lemma cone_norm_cone (α : Type*) [normed_space ℝ α] : cone (norm_cone α) :=
begin
  intros x ha c hc,
  unfold norm_cone at *,
  simp [norm_smul c x.fst, real.norm_eq_abs, abs_of_nonneg hc],
  apply mul_le_mul (le_refl _),
  { simp at ha, assumption },
  { simp [abs_nonneg _] },
  { exact hc }
end


-- Dual cone

section

variables {α : Type*} {β : Type*}
  [real_inner_product_space α] 
  [real_inner_product_space β] 
  (A : set α) (B : set α)

open real_inner_product_space

def dual_cone (A : set α) : set α := { y | ∀ x ∈ A, 0 ≤ ⟪ x , y ⟫ }

lemma cone_dual_cone : cone (dual_cone A) :=
begin
  intros x ha c hc z hz,
  rw inner_smul_right,
  apply zero_le_mul hc,
  exact ha _ hz
end

--TODO: dual norm

lemma inner_product_cone (α : Type*) [decidable_eq α] [real_inner_product_space α] : 
  dual_cone (norm_cone α) = norm_cone α := sorry


end