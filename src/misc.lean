import data.nat.basic

universe u

def string.drop_chars (c : char) (s : string) : string := 
⟨s.data.drop_while (λ x, x = c)⟩ 

def string.reverse (s : string) : string := ⟨s.data.reverse⟩ 

def update (α : Type u) (k : nat) (a : α) (f : nat → α) : nat → α := 
λ x : nat, if x = k then a else f x

lemma forall_lt_zero (p : nat → Prop) : ∀ x < 0, p x := 
λ x h, by cases h

axiom any {P : Prop} : P

lemma forall_lt_succ (p : nat → Prop) (k : nat) : 
  p k → (∀ x < k, p x) → (∀ x < k.succ, p x) := 
begin
  intros h1 h2 m h3,
  apply or.elim (nat.lt_succ_iff_lt_or_eq.elim_left h3); intro h4,
  apply h2 m h4, 
  apply @eq.rec _ _ p h1 _ h4.symm, 
end

lemma forall_lt_succ_iff (p : nat → Prop) (k : nat) : 
  (∀ x < k.succ, p x) ↔ (p k ∧ (∀ x < k, p x)) := 
iff.intro 
  (λ h, ⟨ h k (nat.lt_succ_self k), 
          λ x h2, h x (lt.trans h2 (nat.lt_succ_self k))⟩) 
  (λ h, forall_lt_succ p k h.left h.right)

instance forall_lt.decidable (p : nat → Prop) [decidable_pred p] : 
  ∀ k : nat, decidable (∀ x < k, p x) 
| 0     := decidable.is_true (forall_lt_zero p)
| (k+1) := decidable_of_iff' _ (forall_lt_succ_iff p k)

open tactic

meta def get_default (αx : expr) : tactic expr := 
to_expr ``(@inhabited.default %%αx _)
