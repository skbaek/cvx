/-
Linear combinations with duplicates
-/
import linear_algebra.basic
noncomputable theory

open classical function lattice
local attribute [instance] prop_decidable

/-- linear combinations over an indexed family -/
@[reducible] def lc (ι : Type*) (α : Type*) (β : Type*) [has_zero α] (v : ι → β) := ι →₀ α

namespace lc

variables {ι : Type*} {ι' : Type*} {ι'' : Type*} {α : Type*} 
          {β : Type*} {β' : Type*} {β'' : Type*} {γ : Type*} 
          {v : ι → β} {v' : ι' → β'} {v'' : ι'' → β''}
variables [ring α] [add_comm_group β] [add_comm_group β'] [add_comm_group β''] [add_comm_group γ]
variables [module α β] [module α β'] [module α β''] [module α γ]
open submodule linear_map

def vsupport (l : lc ι α β v) : multiset β := l.support.val.map v

instance : add_comm_group (lc ι α β v) := finsupp.add_comm_group

instance : has_scalar α (lc ι α β v) := finsupp.to_has_scalar

instance : module α (lc ι α β v) := finsupp.to_module ι α

variables (α) (β) (v)
def supported (s : set ι) : submodule α (lc ι α β v) :=
{ carrier := {l | ↑l.support ⊆ s},
  zero := by simp,
  add := λ l₁ l₂ h₁ h₂, set.subset.trans (finset.coe_subset.2 finsupp.support_add)
    (by simpa using set.union_subset h₁ h₂),
  smul := λ a l h, set.subset.trans (finset.coe_subset.2 finsupp.support_smul)
    (by simpa using h) }
variables {α} {β} {v}

theorem mem_supported {s : set ι} {l : lc ι α β v} :
  l ∈ supported α β v s ↔ ↑l.support ⊆ s := iff.rfl

theorem mem_supported' {s : set ι} {l : lc ι α β v} :
  l ∈ supported α β v s ↔ ∀ x ∉ s, l x = 0 :=
by simp [mem_supported, set.subset_def, not_imp_comm]

variables (β) (v)
theorem single_mem_supported {s : set ι} (a : α) {b : ι} (h : b ∈ s) :
  finsupp.single b a ∈ supported α β v s :=
set.subset.trans finsupp.support_single_subset (set.singleton_subset_iff.2 h)
variables {β} {v}

theorem supported_eq_span_single (s : set ι) :
  lc.supported α β v s = span α ((λ i, finsupp.single i (1 : α)) '' s) :=
begin
  refine (span_eq_of_le _ _ (le_def'.2 $ λ l hl, _)).symm,
  { rintro _ ⟨l, hl, rfl⟩, exact single_mem_supported β v (1:α) hl },
  { rw ← l.sum_single,
    refine sum_mem _ (λ i il, _),
    convert @smul_mem α (lc ι α β v) _ _ _ _ (finsupp.single i (1 : α)) (l i) _,
    { simp },
    apply subset_span,
    apply set.mem_image_of_mem _ (hl il) }
end

variables (α) (β) (v)
def restrict_dom (s : set ι) : lc ι α β v →ₗ supported α β v s :=
linear_map.cod_restrict _
  { to_fun := finsupp.filter (∈ s),
    add := λ l₁ l₂, finsupp.filter_add,
    smul := λ a l, finsupp.filter_smul }
  (λ l, mem_supported'.2 $ λ x, finsupp.filter_apply_neg (∈ s) l)
variables {α} {β} {v}

@[simp] theorem restrict_dom_apply (s : set ι) (l : lc ι α β v) :
  ↑((restrict_dom α β v s : lc ι α β v →ₗ supported α β v s) l) = finsupp.filter (∈ s) l := rfl

theorem restrict_dom_comp_subtype (s : set ι) :
  (restrict_dom α β v s).comp (submodule.subtype _) = linear_map.id :=
by ext l; apply subtype.coe_ext.2; simp; ext a;
   by_cases a ∈ s; simp [h]; exact (mem_supported'.1 l.2 _ h).symm

theorem range_restrict_dom (s : set ι) : (restrict_dom α β v s).range = ⊤ :=
begin
  have := linear_map.range_comp (submodule.subtype _) (restrict_dom α β v s),
  rw [restrict_dom_comp_subtype, linear_map.range_id] at this,
  exact eq_top_mono (submodule.map_mono le_top) this.symm
end

theorem supported_mono {s t : set ι} (st : s ⊆ t) :
  supported α β v s ≤ supported α β v t :=
λ l h, set.subset.trans h st

@[simp] theorem supported_empty : supported α β v (∅ : set ι) = ⊥ :=
eq_bot_iff.2 $ λ l h, (submodule.mem_bot α).2 $
by ext; simp [*, mem_supported'] at *

@[simp] theorem supported_univ : supported α β v (set.univ : set ι) = ⊤ :=
eq_top_iff.2 $ λ l _, set.subset_univ _

theorem supported_Union {δ : Type*} (s : δ → set ι) :
  supported α β v (⋃ i, s i) = ⨆ i, supported α β v (s i) :=
begin
  refine le_antisymm _ (supr_le $ λ i, supported_mono $ set.subset_Union _ _),
  suffices : ((submodule.subtype _).comp (restrict_dom α β v (⋃ i, s i))).range ≤ ⨆ i, supported α β v (s i),
  { rwa [range_comp, range_restrict_dom, map_top, range_subtype] at this },
  rw [range_le_iff_comap, eq_top_iff],
  rintro l ⟨⟩, rw mem_coe,
  apply finsupp.induction l, {exact zero_mem _},
  refine λ x a l hl a0, add_mem _ _,
  by_cases (∃ i, x ∈ s i); simp [h],
  cases h with i hi,
  exact le_supr (λ i, supported α β v (s i)) i (single_mem_supported β v _ hi)
end

theorem supported_union (s t : set ι) :
  supported α β v (s ∪ t) = supported α β v s ⊔ supported α β v t :=
by erw [set.union_eq_Union, supported_Union, supr_bool_eq]; refl

theorem supported_Inter {δ : Type*} (s : δ → set ι) :
  supported α β v (⋂ i, s i) = ⨅ i, supported α β v (s i) :=
begin
  refine le_antisymm (le_infi $ λ i, supported_mono $ set.Inter_subset _ _) _,
  simp [le_def, infi_coe, set.subset_def],
  exact λ l, set.subset_Inter
end

def apply (i : ι) : lc ι α β v →ₗ α :=
⟨λ l, l i, λ _ _, finsupp.add_apply, λ _ _, finsupp.smul_apply⟩

@[simp] theorem apply_apply (i : ι) (l : lc ι α β v) :
  (lc.apply i : lc ι α β v →ₗ α) l = l i := rfl

protected def lsum (f : ι → α →ₗ[α] γ) : lc ι α β v →ₗ[α] γ :=
⟨λ d, d.sum (λ i, f i),
  assume d₁ d₂, by simp [finsupp.sum_add_index],
  assume a d, by simp [finsupp.sum_smul_index, finsupp.smul_sum,
    -smul_eq_mul, smul_eq_mul.symm]⟩

@[simp] theorem lsum_apply (f : ι → α →ₗ γ) (l : lc ι α β v) :
  (lc.lsum f : lc ι α β v →ₗ γ) l = l.sum (λ b, f b) := rfl

section
variables (ι α β v)
protected def total : lc ι α β v →ₗ β := lc.lsum (λ i, linear_map.id.smul_right (v i))
end

theorem total_apply (l : lc ι α β v) :
  lc.total ι α β v l = l.sum (λ i a, a • v i) := rfl

@[simp] theorem total_single (a : α) (i : ι) :
  lc.total ι α β v (finsupp.single i a) = a • (v i) :=
by simp [total_apply, finsupp.sum_single_index]

theorem total_range (h : surjective v) : (lc.total ι α β v).range = ⊤ :=
begin
  apply range_eq_top.2,
  intros x,
  apply exists.elim (h x),
  exact λ i hi, ⟨finsupp.single i 1, by simp [hi]⟩
end

variables (α) (v) (v')
protected def map (f : ι → ι') : lc ι α β v →ₗ[α] lc ι' α β' v' :=
{ to_fun := finsupp.map_domain f,
  add := λ l₁ l₂, finsupp.map_domain_add,
  smul := λ a l, finsupp.map_domain_smul _ _ }
variables {α} {v} {v'}

@[simp] theorem map_apply (f : ι → ι') (l : lc ι α β v) :
  (lc.map α v v' f : _ →ₗ _) l = finsupp.map_domain f l := rfl

@[simp] theorem map_id : (lc.map α v v id : lc ι α β v →ₗ[α] lc ι α β v) = linear_map.id :=
linear_map.ext $ λ l, finsupp.map_domain_id

theorem map_comp (f : ι → ι') (g : ι' → ι'') :
  lc.map α v v'' (g ∘ f) = (lc.map α v' v'' g).comp (lc.map α v v' f) :=
linear_map.ext $ λ l, finsupp.map_domain_comp

theorem supported_comap_map (f : ι → ι') (s : set ι') :
  supported α β v (f ⁻¹' s) ≤ (supported α β' v' s).comap (lc.map α v v' f) :=
λ l (hl : ↑l.support ⊆ f ⁻¹' s),
show ↑(finsupp.map_domain f l).support ⊆ s, begin
  rw [← set.image_subset_iff, ← finset.coe_image] at hl,
  exact set.subset.trans finsupp.map_domain_support hl
end

theorem map_supported [inhabited ι] (f : ι → ι') (s : set ι) :
  (supported α β v s).map (lc.map α v v' f) = supported α β' v' (f '' s) :=
begin
  refine le_antisymm (map_le_iff_le_comap.2 $
    le_trans (supported_mono $ set.subset_preimage_image _ _)
       (supported_comap_map _ _)) _,
  intros l hl,
  refine ⟨(lc.map α v' v (inv_fun_on f s) : lc ι' α β' v' →ₗ lc ι α β v) l, λ x hx, _, _⟩,
  { rcases finset.mem_image.1 (finsupp.map_domain_support hx) with ⟨c, hc, rfl⟩,
    exact inv_fun_on_mem (by simpa using hl hc) },
  { rw [← linear_map.comp_apply, ← map_comp],
    refine (finsupp.map_domain_congr $ λ c hc, _).trans finsupp.map_domain_id,
    exact inv_fun_on_eq (by simpa using hl hc) }
end

theorem map_disjoint_ker (f : ι → ι') {s : set ι}
  (H : ∀ a b ∈ s, f a = f b → a = b) :
  disjoint (supported α β v s) (lc.map α v v' f).ker :=
begin
  rintro l ⟨h₁, h₂⟩,
  rw [mem_coe, mem_ker, map_apply, finsupp.map_domain] at h₂,
  simp, ext x,
  by_cases xs : x ∈ s,
  { have : finsupp.sum l (λ a, finsupp.single (f a)) (f x) = 0, {rw h₂, refl},
    rw [finsupp.sum_apply, finsupp.sum, finset.sum_eq_single x] at this,
    { simpa [finsupp.single_apply] },
    { intros y hy xy, simp [mt (H _ _ (h₁ hy) xs) xy] },
    { simp {contextual := tt} } },
  { by_contra h, exact xs (h₁ $ finsupp.mem_support_iff.2 h) }
end

theorem map_total (f : ι → ι') (g : β →ₗ[α] β') (h : ∀ i, g (v i) = v' (f i)):
  (lc.total ι' α β' v').comp (lc.map α v v' f) = g.comp (lc.total ι α β v) :=
by ext l; simp [total_apply, finsupp.sum_map_domain_index, add_smul, h]

end lc

namespace lc
variables {ι : Type*} {α : Type*} {β : Type*} {v : ι → β}
          [discrete_field α] [add_comm_group β] [vector_space α β]

instance : vector_space α (lc ι α β v) := { .. lc.module }

end lc

section module
variables {ι : Type*} {α : Type*} {β : Type*} {γ : Type*} {v : ι → β}
          [ring α] [add_comm_group β] [add_comm_group γ] 
variables [module α β] [module α γ] 
variables {a b : α} {s t : set ι} {x y : β}
include α
open submodule

theorem span_eq_map_lc : span α (v '' s) = (lc.supported α β v s).map (lc.total ι α β v) :=
begin
  apply span_eq_of_le,
  { intros x hx, 
    rw set.mem_image at hx,
    apply exists.elim hx,
    intros i hi,
    exact ⟨_, lc.single_mem_supported β v 1 hi.1, by simp [hi.2]⟩ },
  { refine map_le_iff_le_comap.2 (λ z hz, _),
    have : ∀i, z i • v i ∈ span α (v '' s),
    { intro c, by_cases c ∈ s,
      { exact smul_mem _ _ (subset_span (set.mem_image_of_mem _ h)) },
      { simp [lc.mem_supported'.1 hz _ h] } },
    refine sum_mem _ _, simp [this] }
end

theorem mem_span_iff_lc : 
  x ∈ span α (v '' s) ↔ ∃ l ∈ lc.supported α β v s, lc.total ι α β v l = x :=
by rw span_eq_map_lc; simp

variables (α) (β) (v)
def lc.total_on (s : set ι) : lc.supported α β v s →ₗ span α (v '' s) :=
linear_map.cod_restrict _ ((lc.total ι α _ v).comp (submodule.subtype _)) $
  λ ⟨l, hl⟩, mem_span_iff_lc.2 ⟨l, hl, rfl⟩
variables {α} {β} {v}

theorem lc.total_on_range (s : set ι) : (lc.total_on α β v s).range = ⊤ :=
by rw [lc.total_on, linear_map.range, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
  range_subtype, map_top, linear_map.range_comp, range_subtype]; exact le_of_eq span_eq_map_lc

lemma linear_eq_on (s : set β) {f g : β →ₗ[α] γ} (H : ∀x∈s, f x = g x) {x} (h : x ∈ span α s) : f x = g x :=
by apply span_induction h H; simp {contextual := tt}

end module
