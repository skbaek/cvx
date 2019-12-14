
import tactic.interactive
import .mat .one_by_one_matrix
import tactic.transfer
import logic.relator
import .inner_product_space


-- TODO: move
namespace fin

open finset

lemma sum_image_succ_univ {α : Type} [comm_ring α] {n : nat} (f : fin (n + 1) → α) : 
  sum (image fin.succ univ) (λ x, f x) = sum univ (λ i, f (fin.succ i)) :=
begin
  rw finset.sum_image,
  intros _ _ _ _ h,
  apply (eq_iff_veq _ _).2,
  apply (eq_iff_veq _ _).1 (succ.inj h),
end

lemma image_succ_univ (n : nat) : 
  insert (⟨0, nat.zero_lt_succ n⟩ : fin (n + 1)) (image fin.succ (univ : finset (fin n)))
    = (univ : finset (fin (n + 1))) :=
begin
  apply subset.antisymm,
  { intros k hk,
    rw mem_insert at hk,
    apply or.elim hk (λ _, mem_univ) (λ _, mem_univ),
  },
  { intros k _,
    by_cases h_cases: k = ⟨0, nat.zero_lt_succ n⟩,
    { rw h_cases,
      apply mem_insert_self _ },
    { apply mem_insert_of_mem,
      rw mem_image,
      use fin.pred k h_cases,
      use mem_univ _,
      apply succ_pred } }
end

lemma not_mem_image_succ_univ (n : nat) :  
  ¬ (⟨0, nat.zero_lt_succ n⟩ : fin (n + 1)) ∈ image fin.succ (univ : finset (fin n)) :=
begin
  intros h,
  rw mem_image at h,
  apply exists.elim h,
  intros k hk,
  apply exists.elim hk,
  intros _ hk',
  rw eq_iff_veq at hk',
  simp at hk',
  exact nat.succ_ne_zero _ hk'
end

lemma sum_succ {α : Type} [comm_ring α] {n : nat} (f : fin (n + 1) → α) : 
  finset.sum finset.univ (λ x : fin (n + 1), f x) = f ⟨0, nat.zero_lt_succ n⟩ + finset.sum finset.univ (λ x : fin n, f x.succ) :=
begin
  rw [← sum_image_succ_univ],
  rw [← image_succ_univ n],
  rw sum_insert,
  apply not_mem_image_succ_univ n
end

end fin

section transport 

open tactic

@[user_attribute]
meta def to_rowvec_attr : user_attribute (name_map name) name :=
{ name      := `to_rowvec,
  descr     := "Transport column vector to row vector",
  cache_cfg := ⟨λ ns, ns.mfoldl (λ dict n, do
    val ← to_rowvec_attr.get_param n,
    pure $ dict.insert n val) mk_name_map, []⟩,
  parser    := lean.parser.ident,
  after_set := some $ λ src _ _, do
    env ← get_env,
    dict ← to_rowvec_attr.get_cache,
    tgt ← to_rowvec_attr.get_param src,
    (get_decl tgt >> skip) <|>
      transport_with_dict dict src tgt }

end transport

def colvec (n : Type) [fintype n] (α : Type) : Type := matrix n (fin 1) α
def rowvec (n : Type) [fintype n] (α : Type) : Type := matrix (fin 1) n α
attribute [to_rowvec rowvec] colvec

section instances

variables {α : Type} {n : Type} [fintype n]

instance colvec.has_scalar [semiring α] : has_scalar α (colvec n α) := matrix.has_scalar
instance rowvec.has_scalar [semiring α] : has_scalar α (rowvec n α) := matrix.has_scalar
attribute [to_rowvec rowvec.has_scalar] colvec.has_scalar

instance colvec.has_add [has_add α] : has_add (colvec n α) := matrix.has_add
instance rowvec.has_add [has_add α] : has_add (rowvec n α) := matrix.has_add
attribute [to_rowvec rowvec.has_add] colvec.has_add

instance colvec.has_zero [has_zero α] : has_zero (colvec n α) := matrix.has_zero
instance rowvec.has_zero [has_zero α] : has_zero (rowvec n α) := matrix.has_zero
attribute [to_rowvec rowvec.has_zero] colvec.has_zero

instance colvec.add_comm_group [add_comm_group α] : add_comm_group (colvec n α) := matrix.add_comm_group
instance rowvec.add_comm_group [add_comm_group α] : add_comm_group (rowvec n α) := matrix.add_comm_group
attribute [to_rowvec rowvec.add_comm_group] colvec.add_comm_group

instance colvec.module [ring α] : module α (colvec n α) := matrix.module
instance rowvec.module [ring α] : module α (rowvec n α) := matrix.module
attribute [to_rowvec rowvec.add_comm_group] colvec.add_comm_group

def colvec.nth (x : colvec n α) (i : n) : α := x i 0
def rowvec.nth (x : rowvec n α) (i : n) : α := x 0 i
attribute [to_rowvec rowvec.nth] colvec.nth

def colvec.mk (f : n → α) : colvec n α := λ i j, f i
def rowvec.mk (f : n → α) : rowvec n α := λ i j, f j
attribute [to_rowvec rowvec.mk] colvec.mk

@[simp, to_rowvec rowvec.nth_mk]
lemma colvec.nth_mk (f : n → α) : colvec.nth (colvec.mk f) = f :=
by refl

@[simp, to_rowvec rowvec.nth_mk]
lemma colvec.nth_zero [has_zero α] (i : n): (0 : colvec n α).nth i = 0 :=
by refl

lemma colvec.eq_of_nth_eq (x : colvec n α) (y : colvec n α) (h : ∀i, x.nth i = y.nth i) : x = y :=
begin
  ext i j,
  rw fin.eq_zero_fin1 j,
  apply h,
end

lemma rowvec.eq_of_nth_eq (x : rowvec n α) (y : rowvec n α) (h : ∀i, x.nth i = y.nth i) : x = y :=
begin
  ext i j,
  rw fin.eq_zero_fin1 i,
  apply h,
end

attribute [to_rowvec rowvec.eq_of_nth_eq] colvec.eq_of_nth_eq

end instances

section inner

variables {α : Type} [has_mul α] [add_comm_monoid α] {n : Type} [fintype n]

def colvec.inner (v w : colvec n α) : α := (matrix.mul vᵀ w) 0 0
def rowvec.inner (v w : rowvec n α) : α := (matrix.mul v wᵀ) 0 0

end inner

section transfer

variables {α : Type} [has_mul α] [add_comm_monoid α] {n : Type} [fintype n]

open transfer

/- Set up relators for transfer tactic to transfer from colvec to rowvec -/

lemma colvec.rel_eq_inner {α : Type} [comm_ring α]: 
  ((λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ (λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ @eq α) rowvec.inner colvec.inner := 
begin 
  intros x xt hx y yt hy, 
  unfold colvec.inner rowvec.inner,
  rw [hy,←hx,matrix.transpose_transpose]
end

lemma colvec.rel_transpose_add {α : Type} [comm_ring α]: 
  ((λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ (λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ (λ (x : rowvec n α) (y : colvec n α), xᵀ = y)) (+) (+) := 
begin 
  intros x xt hx y yt hy,
  rw [←hx,←hy,matrix.transpose_add]
end

lemma relator.rel_eq_add {α : Type} [comm_ring α]: 
  ((@eq α) ⇒ (@eq α) ⇒ (@eq α)) (+) (+) := 
begin 
  intros x x' hx y y' hy,
  rw [hx,hy]
end

lemma relator.rel_le {α  : Type} [has_le α] : 
  (@eq α ⇒ @eq α ⇒ (↔)) (≤) (≤) := 
λ _ _ h1 _ _ h2, by rw [h1, h2]

lemma relator.rel_pos {α  : Type} [has_le α] [has_zero α] : 
  (@eq α ⇒ (↔)) (has_le.le 0) (has_le.le 0) := 
λ _ _ h, by rw [h]

lemma relator.rel_eq_const {α  : Type} {a : rowvec n α} : 
  ((@eq (rowvec n α))) (a) (a) := rfl

lemma relator.rel_eq_zero_transpose {α  : Type} [has_zero α] : 
  ((λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ (↔)) (eq 0) (eq 0) := 
begin 
  intros x y h,
  convert matrix.eq_iff_transpose_eq _ _,
  apply h.symm
end

lemma colvec.rel_smul_transpose {α  : Type} [semiring α] (a : α) : 
  ((λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ 
  (λ (x : rowvec n α) (y : colvec n α), xᵀ = y)) 
  (has_scalar.smul a) (has_scalar.smul a) := 
λ _ _ h, by rw [matrix.transpose_smul,h]

lemma relator.rel_mul_const {α  : Type} [has_mul α] (a : α) : 
  ((=) ⇒ (=)) (has_mul.mul a) (has_mul.mul a) := 
λ _ _ h, by rw [h]

lemma relator.rel_eq_zero {α  : Type} [has_zero α] : 
  ((@eq α) ⇒ (↔)) (eq 0) (eq 0) := 
λ _ _ h, by rw [h]

-- TODO: move
lemma relator.rel_imp' : ((↔) ⇒ (↔) ⇒ (↔)) (→) (→) := 
λ _ _ h1 _ _ h2, by rw [h1, h2]  

-- TODO: move
lemma relator.rel_eq_same {α  : Type} : (@eq α ⇒ @eq α ⇒ (↔)) (=) (=) := 
begin
  apply relator.rel_eq,
  split,
  exact λ a b c h1 h2, eq.trans h1 h2.symm,
  exact λ a b c h1 h2, eq.trans h1.symm h2
end

instance colvec.bi_total_transpose : relator.bi_total (λ (x : rowvec n α) (y : colvec n α), xᵀ = y) :=
⟨λ x, ⟨xᵀ, eq.refl _⟩, λ x, ⟨xᵀ, matrix.transpose_transpose _⟩⟩

lemma colvec.rel_forall_transpose : (((λ (x : rowvec n α) (y : colvec n α), xᵀ = y) ⇒ iff) ⇒ iff) (λp, ∀i, p i) (λq, ∀i, q i) :=
by apply relator.rel_forall_of_total

meta def colvec.transfer : tactic unit := 
tactic.transfer [
  `relator.rel_eq_zero_transpose,
  `relator.rel_eq_zero,
  `relator.rel_eq_same, 
  `relator.rel_eq_add,
  `relator.rel_pos,
  `relator.rel_imp',
  `colvec.rel_forall_transpose, 
  `colvec.rel_eq_inner, 
  `colvec.rel_transpose_add,
  `relator.rel_eq_const,
  `colvec.rel_smul_transpose,
  `relator.rel_mul_const
]

end transfer

section inner 

variables {α : Type} [comm_ring α] {n : Type} [fintype n] (a : α) (x y z : colvec n α)

lemma colvec.inner_comm : x.inner y = y.inner x :=
begin
  dsimp [colvec.inner, colvec, mat], 
  intros,
  rw [←matrix.transpose_transpose ((matrix.transpose y).mul x), matrix.transpose_mul, matrix.transpose_transpose y],
  refl
end

lemma rowvec.inner_comm : ∀ (x y : rowvec n α), x.inner y = y.inner x :=
begin colvec.transfer, exact colvec.inner_comm end

lemma colvec.inner_add_left : (x + y).inner z = x.inner z + y.inner z := 
by simp [colvec.inner, colvec, mat, matrix.transpose_add, matrix.add_mul']

lemma rowvec.inner_add_left : ∀ (x y z : rowvec n α), (x + y).inner z = x.inner z + y.inner z :=
begin colvec.transfer, exact colvec.inner_add_left end

lemma colvec.inner_smul_left : (a • x).inner y = a * x.inner y := 
by simp [colvec.inner, colvec, mat, matrix.smul_mul, matrix.transpose_smul]; refl

lemma rowvec.inner_smul_left (a : α) : ∀ (x y : rowvec n α), (a • x).inner y = a * x.inner y := 
begin colvec.transfer, exact colvec.inner_smul_left a end

end inner

section inner

variables {α : Type} [linear_ordered_comm_ring α] {m : Type} [fintype m] {n : Type} [fintype n] [decidable_eq n] (a : α) (x y z : colvec n α)

lemma colvec.inner_self_nonneg : 0 ≤ x.inner x :=
begin
  dsimp [colvec.inner, colvec, mat, matrix.mul],
  apply finset.sum_nonneg,
  intros i _,
  apply mul_self_nonneg
end

lemma rowvec.inner_self_nonneg : ∀ (x : rowvec n α), 0 ≤ x.inner x :=
begin colvec.transfer, exact colvec.inner_self_nonneg end

lemma colvec.eq_zero_of_inner_self_eq_zero : 0 = x.inner x → 0 = x :=
begin
  dsimp [colvec.inner, colvec, mat, matrix.mul],
  intros h,
  apply colvec.eq_of_nth_eq,
  intro i,
  apply (eq_zero_of_mul_self_eq_zero ((finset.sum_eq_zero_iff_of_nonneg _).1 h.symm i (finset.mem_univ _))).symm,
  intros i hi,
  apply mul_self_nonneg
end

lemma rowvec.eq_zero_of_inner_self_eq_zero : ∀ (x : rowvec n α), 0 = x.inner x → 0 = x :=
begin colvec.transfer, exact colvec.eq_zero_of_inner_self_eq_zero end

local attribute [instance] classical.prop_decidable

noncomputable instance colvec.real_inner_product_space : real_inner_product_space (colvec n ℝ) :=
{
  inner := colvec.inner,
  inner_add_left := colvec.inner_add_left,
  inner_smul_left := colvec.inner_smul_left,
  inner_comm := colvec.inner_comm,
  inner_self_nonneg := colvec.inner_self_nonneg,
  eq_zero_of_inner_self_eq_zero := λ x h, (colvec.eq_zero_of_inner_self_eq_zero x h.symm).symm
}

noncomputable instance rowvec.real_inner_product_space : real_inner_product_space (rowvec n ℝ) :=
{
  inner := rowvec.inner,
  inner_add_left := rowvec.inner_add_left,
  inner_smul_left := rowvec.inner_smul_left,
  inner_comm := rowvec.inner_comm,
  inner_self_nonneg := rowvec.inner_self_nonneg,
  eq_zero_of_inner_self_eq_zero := λ x h, (rowvec.eq_zero_of_inner_self_eq_zero x h.symm).symm
}

lemma colvec.inner_eq_sum_nth : 
  x.inner y = finset.univ.sum (λi, x.nth i * y.nth i) :=
by unfold colvec.inner matrix.mul colvec.nth; refl

lemma rowvec.inner_eq_sum_nth (x : rowvec n α) (y : rowvec n α) : 
  x.inner y = finset.univ.sum (λi, x.nth i * y.nth i) :=
by unfold rowvec.inner matrix.mul colvec.nth; refl

attribute [to_rowvec rowvec.inner_eq_sum_nth] colvec.inner_eq_sum_nth


--TODO @[to_rowvec rowvec.inner_mul]
lemma colvec.inner_mul (A : matrix m n ℝ) (x : colvec n ℝ) (y : colvec m ℝ) : 
  ⟪ x, Aᵀ.mul y ⟫ = ⟪ y, A.mul x ⟫ :=
begin
  unfold has_inner.inner colvec.inner,
  rw [←one_by_one_matrix.transpose ℝ (matrix.mul xᵀ (matrix.mul Aᵀ y)),
      matrix.transpose_mul, matrix.transpose_mul, ←matrix.mul_assoc, 
      matrix.transpose_transpose, matrix.transpose_transpose]
end

end inner

section fin_index

variables {α : Type} {n : nat} (a : α) (x y z : colvec (fin n) α)

@[to_rowvec rowvec.head]
def colvec.head (x : colvec (fin (n+1)) α) : α := x.nth ⟨0, nat.zero_lt_succ n⟩

@[to_rowvec rowvec.tail]
def colvec.tail (x : colvec (fin (n+1)) α) : colvec (fin n) α := 
  colvec.mk (λ i, x.nth ⟨i.1.succ, nat.succ_lt_succ i.2⟩)

@[to_rowvec rowvec.cons]
def colvec.cons (c : α) (x : colvec (fin n) α) : colvec (fin (n+1)) α := 
  colvec.mk (λ i, dite (i.val = 0) (λ_, c) (λhi, x.nth ⟨i.val.pred,nat.pred_lt_pred hi i.2⟩))

@[simp, to_rowvec rowvec.head_smul] 
lemma colvec.head_smul [semiring α] (c : α) (x : colvec (fin (n+1)) α) : 
  (c • x).head = c * x.head :=
by refl

@[simp, to_rowvec rowvec.tail_smul] 
lemma colvec.tail_smul [semiring α] (c : α) (x : colvec (fin (n+1)) α) : 
  (c • x).tail = c • x.tail :=
by refl

@[simp, to_rowvec rowvec.head_cons] 
lemma colvec.head_cons (c : α) (x : colvec (fin n) α) : (colvec.cons c x).head = c :=
by refl

-- TODO: get rid of this?
attribute [to_rowvec rowvec.head.equations._eqn_1] colvec.head.equations._eqn_1
attribute [to_rowvec rowvec.tail.equations._eqn_1] colvec.tail.equations._eqn_1
attribute [to_rowvec rowvec.cons.equations._eqn_1] colvec.cons.equations._eqn_1

@[simp, to_rowvec rowvec.tail_cons]
lemma colvec.tail_cons (x : colvec (fin n) α) (c : α) : (colvec.cons c x).tail = x :=
by apply colvec.eq_of_nth_eq; simp [colvec.tail,colvec.cons,nat.pred_succ,dif_eq_if, nat.succ_ne_zero]

@[simp, to_rowvec rowvec.cons_head_tail]
lemma colvec.cons_head_tail (x : colvec (fin (n+1)) α) : colvec.cons x.head x.tail = x :=
begin
  apply colvec.eq_of_nth_eq,
  intro i,
  unfold colvec.cons colvec.head colvec.tail,
  by_cases h_cases : i.val = 0, 
  { have hi : i = ⟨0, nat.zero_lt_succ n⟩, 
      from (fin.eq_iff_veq _ _).2 h_cases,
    simp [hi] },
  { simp [h_cases, nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_cases)] },
end


--TODO: @[to_rowvec rowvec.last]
lemma colvec.mul_head_add_mul_tail {α : Type} [comm_ring α] (x y : colvec (fin (n+1)) ℝ) :
  x.head * y.head + ⟪ x.tail, y.tail ⟫ = ⟪ x, y ⟫  := 
begin
  unfold has_inner.inner,
  simp only [colvec.inner_eq_sum_nth],
  unfold colvec.head colvec.tail,
  rw fin.sum_succ (λ j : fin (n+1), x.nth j * y.nth j),
  congr,
  simp,
  funext,
  congr,
  apply (fin.eq_iff_veq _ _).2,
  simp,
  apply (fin.eq_iff_veq _ _).2,
  simp,
end

@[to_rowvec rowvec.last]
def colvec.last (x : colvec (fin (n+1)) α) : α := x.nth ⟨n, nat.lt_succ_self n⟩

@[to_rowvec rowvec.butlast]
def colvec.butlast (x : colvec (fin (n+1)) α) : colvec (fin n) α := 
  colvec.mk (λ i, x.nth ⟨i.1, nat.le_succ_of_le i.2⟩)

@[to_rowvec rowvec.snoc]
def colvec.snoc (x : colvec (fin n) α) (c : α) : colvec (fin (n+1)) α := 
  colvec.mk (λ i, dite (i.val < n) (λhi, x.nth ⟨i.val,hi⟩) (λ_, c))

--TODO: Lemmas about last, butlast, snoc

end fin_index
