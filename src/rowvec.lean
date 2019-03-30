 import .colvec
 
variables {α : Type} [ring α] {k m n : nat}

-- TODO: move
namespace fin

open finset

lemma image_val (n : nat) : image (@val n) univ = range n :=
begin
  apply subset.antisymm,
  { intros k hk, 
    rw mem_range, 
    rw mem_image at hk, 
    apply exists.elim hk,
    intros l hl,
    apply exists.elim hl, 
    intros hl' hl'',
    rw hl''.symm,
    exact l.2 },
  { intros k hk, 
    rw mem_range at hk, 
    rw mem_image,
    use ⟨k, hk⟩,
    use (mem_univ _) }
end

lemma sum_univ {α : Type} [comm_ring α] {n : nat} (f : ℕ → α) : 
  sum univ (λ x : fin n, f x) = sum (range n) f :=
begin
  convert (finset.sum_image _).symm,
  apply (image_val _).symm,
  intros _ _ _ _ h,
  apply (eq_iff_veq _ _).2 h,
end

lemma sum_image_cast_succ_univ {α : Type} [comm_ring α] {n : nat} (f : fin (n + 1) → α) : 
  sum (image cast_succ univ) (λ x, f x) = sum univ (λ i, f (cast_succ i)) :=
begin
  rw finset.sum_image,
  intros _ _ _ _ h,
  apply (eq_iff_veq _ _).2,
  apply (eq_iff_veq _ _).1 h
end

#check nat.lt_of_le_and_ne

lemma image_cast_succ_univ (n : nat) : 
  insert (⟨n, nat.lt_succ_self n⟩ : fin (n + 1)) (image cast_succ (univ : finset (fin n)))
    = (univ : finset (fin (n + 1))) :=
begin
  apply subset.antisymm,
  { intros k hk,
    rw mem_insert at hk,
    apply or.elim hk (λ _, mem_univ) (λ _, mem_univ),
  },
  { intros k _,
    by_cases h_cases: k = ⟨n, nat.lt_succ_self n⟩,
    { rw h_cases,
      apply mem_insert_self _ },
    { apply mem_insert_of_mem,
      rw mem_image,
      let hk := nat.lt_of_succ_lt_succ (nat.lt_of_le_and_ne k.2 
        (λ h, h_cases ((eq_iff_veq _ _).2 (@nat.add_right_cancel _ 1 _ h)))),
      use ⟨k.val, hk⟩,
      use mem_univ _,
      rw eq_iff_veq,  
      refl } }
end

lemma not_mem_image_cast_succ_univ (n : nat) :  
  ¬ (⟨n, nat.lt_succ_self n⟩ : fin (n + 1)) ∈ image cast_succ (univ : finset (fin n)) :=
begin
  intros h,
  rw mem_image at h,
  apply exists.elim h,
  intros k hk,
  apply exists.elim hk,
  intros _ hk',
  unfold cast_succ cast_add cast_le cast_lt at hk',
  rw eq_iff_veq at hk',
  simp at hk',
  exact ne_of_lt k.2 hk'
end

lemma sum_succ {α : Type} [comm_ring α] {n : nat} (f : ℕ → α) : 
  finset.sum finset.univ (λ x : fin (n + 1), f x) = f n + finset.sum finset.univ (λ x : fin n, f x) :=
by rw [sum_univ, sum_univ, range_succ, sum_insert not_mem_range_self]


lemma sum_succ' {α : Type} [comm_ring α] {n : nat} (f : fin (n + 1) → α) : 
  finset.sum finset.univ (λ x : fin (n + 1), f x) = f ⟨n, nat.lt_succ_self n⟩ + finset.sum finset.univ (λ x : fin n, f (cast_succ x)) :=
begin
  rw [← sum_image_cast_succ_univ],
  rw [← image_cast_succ_univ n],
  rw sum_insert,
  apply not_mem_image_cast_succ_univ n
end

end fin

namespace rowvec

def last (x : rowvec α (n+1)) : α := x 0 ⟨n, nat.lt_succ_self n⟩
def butlast (x : rowvec α (n+1)) : rowvec α n := λ i j, x i ⟨j.1, nat.le_succ_of_le j.2⟩

lemma last_transpose (x : rowvec α (n+1)) : colvec.last xᵀ = rowvec.last x :=
by refl

lemma last_transpose' (x : colvec α (n+1)) : rowvec.last xᵀ = colvec.last x := 
by refl

@[simp] lemma butlast_transpose (x : rowvec α (n+1)): 
  colvec.butlast (xᵀ) = (rowvec.butlast x)ᵀ := 
by refl

@[simp] lemma butlast_transpose' (x : colvec α (n+1)): 
  rowvec.butlast (xᵀ) = (colvec.butlast x)ᵀ := 
by refl

variables 

-- TODO: move?
local infix ` ⬝ ` : 70 := matrix.mul

def inner (v w : rowvec α n) : α := w ⬝ vᵀ

lemma inner_self_nonneg {α : Type} [linear_ordered_comm_ring α] (x : rowvec α n) : 
  0 ≤ inner x x :=
begin -- TODO: use transfer?
  dsimp [inner, colvec, mat, matrix.mul], 
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
  intros,
  apply finset.zero_le_sum,
  intros i _,
  apply mul_self_nonneg
end

lemma eq_zero_of_inner_self_eq_zero {α : Type} [linear_ordered_comm_ring α] (x : rowvec α n) : 
  inner x x = 0 → x = 0 :=
begin -- TODO: use transfer?
  dsimp [inner, colvec, mat, matrix.mul],
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
  intros h,
  rw finset.sum_eq_zero_iff_of_nonneg at h,
  { ext i j,
    rw fin1_eq_zero i,
    apply eq_zero_of_mul_self_eq_zero,
    convert h _ _,
    simp },
  { intros i hi,
    apply mul_self_nonneg }
end

lemma inner_self_pos {α : Type} [linear_ordered_comm_ring α] {x : rowvec α n} (h : x ≠ 0) : 
  0 < inner x x :=
lt_of_le_of_ne (inner_self_nonneg x) (λ h', h (eq_zero_of_inner_self_eq_zero x h'.symm))

lemma mul_last_add_mul_butlast {α : Type} [comm_ring α] (x : rowvec α (n+1)) (y : colvec α (n+1)) :
  x.last * y.last + x.butlast ⬝ y.butlast = x ⬝ y := 
begin
  unfold matrix.mul,
  dsimp [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe, one_by_one_matrix.coe], --TODO WTF?
  rw fin.sum_succ' (λ j : fin (n+1), x 0 j * y j 0),
  refl
end


end rowvec