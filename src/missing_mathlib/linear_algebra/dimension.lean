import linear_algebra.dimension
import missing_mathlib.set_theory.cardinal

universe variables u u' u'' v v' w w'

variables {α : Type u} {β γ δ ε : Type v}
variables {ι : Type w} {ι' : Type w'} {η : Type u''} {φ : η → Type u'}
-- TODO: relax these universe constraints

section vector_space
variables [decidable_eq ι] [decidable_eq ι'] [field α] [decidable_eq α] [add_comm_group β] [vector_space α β]
include α
open submodule lattice function set
open vector_space

lemma submodule.bot_of_dim_zero (p : submodule α β) (h_dim : dim α p = 0) : p = ⊥ :=
begin
  haveI : decidable_eq β := classical.dec_eq β,
  obtain ⟨b, hb⟩ : ∃b : set p, is_basis α (λ i : b, i.val) := @exists_is_basis α p _ _ _,
  rw ←le_bot_iff,
  intros x hx,
  have : (⟨x, (submodule.mem_coe p).1 hx⟩ : p) = (0 : p), 
  { rw ←@mem_bot α p _ _ _,
    rw [← @span_empty α p _ _ _, ←(@set.range_eq_empty p b (λ (i : b), i.val)).2, hb.2],
    apply mem_top,
    unfold_coes,
    rw [nonempty_subtype],
    push_neg,
    rw [←set.eq_empty_iff_forall_not_mem, ←cardinal.mk_zero_iff_empty_set],
    rwa cardinal.lift_inj.1 hb.mk_eq_dim }, 
  rw [mem_bot],
  rw <-coe_eq_zero at this,
  apply this,
end

lemma linear_independent.le_lift_dim [decidable_eq β] {v : ι → β} (hv : linear_independent α v) :
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) := 
calc
  cardinal.lift.{w v} (cardinal.mk ι) 
      = cardinal.lift.{v w} (cardinal.mk (range v)) : 
          by rw ←cardinal.mk_range_eq_of_injective (linear_independent.injective hv)
  ... = cardinal.lift.{v w} (dim α (span α (range v))) : 
          by rw ←dim_span hv
  ... ≤ cardinal.lift.{v w} (dim α (⊤ : submodule α β)) : 
          cardinal.lift_le.2 (dim_le_of_submodule (submodule.span α (set.range v)) ⊤ le_top)
  ... ≤ cardinal.lift.{v w} (dim α β) : 
          by rw dim_top

lemma linear_independent_le_dim {α : Type u} {β : Type v} {ι : Type w}
  [field α] [decidable_eq β] [add_comm_group β] [vector_space α β] [decidable_eq ι]
  {v : ι → β} (hv : @linear_independent _ α _ v (@comm_ring.to_ring _ (field.to_comm_ring _)) _ _) : 
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (dim α β) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) : 
     (cardinal.mk_range_eq_of_injective (linear_independent.injective hv)).symm
  ... = cardinal.lift.{v w} (dim α (submodule.span α (set.range v))) : by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (dim α β) : cardinal.lift_le.2 (dim_submodule_le (submodule.span α _))

lemma powers_linear_dependent_of_dim_finite (α : Type v) (β : Type w) 
  [field α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (h_dim : dim α β < cardinal.omega) (v : β) : 
  ¬ linear_independent α (λ n : ℕ, (f ^ n) v) :=
begin
  intro hw,
  apply not_lt_of_le _ h_dim,
  rw [← cardinal.lift_id (dim α β), cardinal.lift_umax.{w 0}],
  apply linear_independent_le_dim hw
end

lemma exists_mem_ne_zero_of_dim_pos' {α : Type v} {β : Type w} 
  [field α] [add_comm_group β] [vector_space α β] 
  (h_dim : 0 < dim α β) : ∃ x : β, x ≠ 0 :=
begin
  obtain ⟨b, _, _⟩ : (∃ b : β, b ∈ (⊤ : submodule α β) ∧ b ≠ 0),
  { apply exists_mem_ne_zero_of_dim_pos, 
    rw dim_top,
    apply h_dim },
  use b
end

lemma dim_pos_of_mem_ne_zero {α : Type v} {β : Type w} 
  [field α] [add_comm_group β] [vector_space α β] 
  (x : β) (h : x ≠ 0) : 0 < dim α β :=
begin
  classical,
  by_contra hc,
  rw [not_lt, cardinal.le_zero, ←dim_top] at hc,
  have x_mem_bot : x ∈ ⊥,
  { rw ← submodule.bot_of_dim_zero ⊤ hc, 
    apply mem_top },
  exact h ((mem_bot α).1 x_mem_bot)
end

end vector_space