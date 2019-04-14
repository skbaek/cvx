
import linear_algebra.basis
import data.finset
import algebra.module



local attribute [instance] classical.prop_decidable

variables (α : Type) {ι β : Type} [inhabited ι] [division_ring α] [decidable_eq β] [add_comm_group β] [module α β]

open function set finsupp

def linear_independent_family (s : ι → β) : Prop :=
linear_independent α (range s) ∧ injective s

#check image_inv_fun

noncomputable def foo (s : ι → β) (hs : injective s) (l : β →₀ α) (hl : l.support.to_set ⊆ range s):= 
finsupp.mk (l.support.image (inv_fun s)) (λ i, l (s i)) (begin 
intros i,
split,
{ intros hi,
rw finset.mem_image at hi,
apply exists.elim hi,
intros x hx,
apply exists.elim hx,
intros hx hx',
rw hx'.symm,
rw @inv_fun_eq _ _ _  s x,
  
  let H := left_inverse_inv_fun hs,
 unfold left_inverse at H, }
 end)

lemma linear_dependent_sum (s : ι → β) (h : ¬ linear_independent_family α s) :
    ∃ c : ι →₀ α, c.support.sum (λ i, c i • s i) = 0 :=
begin
  by_cases h_cases : injective s,
  { have h_lin_indep : ¬ linear_independent α (range s), 
    { unfold linear_independent_family at h, finish },
    show ∃ c : ι →₀ α, c.support.sum (λ i, c i • s i) = 0,
    {
      rw [linear_independent_iff, not_forall] at h_lin_indep,
      apply exists.elim h_lin_indep,
      intros l hl,
      let c : ι →₀ α := 
      existsi c,
      rw [not_imp,not_imp] at hl,
      let H := @finset.sum_image _ _ _ (λ x, l x • x) _ _ c.support s _,
      convert H.symm,
      simp,
    }
  },
  { unfold injective at h_cases,
    rw not_forall at h_cases,
    apply exists.elim h_cases,
    intros i h_not_inj,
    rw not_forall at h_not_inj,
    apply exists.elim h_not_inj,
    intros j hij,
    let c := single i (1 : α) - single j 1,
    existsi c,
    have h_disjoint : disjoint (single i (1 : α)).support (- single j (1 : α)).support,
    { rw [support_neg, support_single_ne_zero one_ne_zero, 
          support_single_ne_zero one_ne_zero],
      simp [ne.symm (not_imp.1 hij).2] },
    have h_disjoint' : finset.singleton i ∩ finset.singleton j = ∅,
    { convert (finset.disjoint_iff_inter_eq_empty.1 h_disjoint),
      { apply (support_single_ne_zero one_ne_zero).symm },
      { rw [support_neg, support_single_ne_zero one_ne_zero], 
        refl } },
    have h : c.support = finset.singleton i ∪ finset.singleton j,
    { dsimp only [c],
      rw [sub_eq_add_neg, support_add_eq h_disjoint,
            support_neg, support_single_ne_zero one_ne_zero, 
            support_single_ne_zero one_ne_zero],
      refl, },
    show finset.sum c.support (λ i, c i • s i) = 0,
    { dsimp only [c],
      rw [h, finset.sum_union h_disjoint'],
      simp [finset.sum_singleton, sub_apply, single_apply, (not_imp.1 hij).2, 
            ne.symm (not_imp.1 hij).2, (not_imp.1 hij).1] } }
end