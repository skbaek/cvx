-- based on Jeremy's Lean2 formalization

import algebra.module
import analysis.normed_space.basic
import data.real.basic
import linear_algebra.basic

local attribute [instance] classical.prop_decidable
noncomputable theory

-- TODO: move
lemma le_of_sqr_le_sqr {a : ℝ} {b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 ≤ b ^ 2) : a ≤ b := 
begin 
  rw [pow_two,pow_two] at hab, 
  apply or.elim (le_or_gt a b) (λh, h),
  assume h, 
  apply false.elim,
  apply lt_irrefl (b * b),
  exact  (lt_of_lt_of_le (mul_self_lt_mul_self hb h) hab)
end

class has_inner (V : Type*) (W : Type*):=
(inner : W → W → V)

notation `⟪` v `, ` w `⟫` := has_inner.inner ℝ v w


--TODO: try to move add_comm_group in front and use `attribute [-instance] nat.cast_coe`
class real_inner_product_space (V : Type*) extends has_inner ℝ V, add_comm_group V, vector_space ℝ V :=
(inner_add_left : ∀ u v w, inner (u + v) w = inner u w + inner v w)
(inner_smul_left : ∀ r v w, inner (r • v) w = r * inner v w)
(inner_comm : ∀ v w, inner v w = inner w v)
(inner_self_nonneg : ∀ v, 0 ≤ inner v v)
(eq_zero_of_inner_self_eq_zero : ∀ {v}, inner v v = 0 → v = 0)

namespace real_inner_product_space

variables 
  {V : Type*} [real_inner_product_space V] 
  {W : Type*} [real_inner_product_space W]

open real_inner_product_space

@[simp] lemma inner_add_right (u v w : V) : ⟪u, v + w⟫ = ⟪u, v⟫ + ⟪u, w⟫ :=
by rw [inner_comm, inner_add_left, inner_comm, inner_comm w]

@[simp] lemma inner_smul_right (r : ℝ) (v w : V) : ⟪v, r • w⟫ = r * ⟪v, w⟫ :=
by rw [inner_comm, inner_smul_left, inner_comm]

@[simp] lemma inner_neg_left (u v : V) : ⟪-u, v⟫ = -⟪u, v⟫ :=
by rw [←neg_one_smul _ u, inner_smul_left, ←neg_eq_neg_one_mul]

@[simp] lemma inner_neg_right (u v : V) : ⟪u, -v⟫ = -⟪u, v⟫ :=
by rw [inner_comm, inner_neg_left, inner_comm]

lemma neg_inner_neg (x y : V): ⟪ - x, - y ⟫ = ⟪ x, y ⟫ := 
by rw [inner_neg_left, inner_neg_right, neg_neg]

@[simp] lemma inner_sub_left (u v w : V) : ⟪u - v, w⟫ = ⟪u, w⟫ - ⟪v, w⟫ :=
by rw [sub_eq_add_neg, sub_eq_add_neg, inner_add_left, inner_neg_left]

@[simp] lemma inner_sub_right (u v w : V) : ⟪u, v - w⟫ = ⟪u, v⟫ - ⟪u, w⟫ :=
by rw [sub_eq_add_neg, sub_eq_add_neg, inner_add_right, inner_neg_right]

@[simp] lemma inner_zero_left (v : V) : ⟪0, v⟫ = 0 :=
by rw [←zero_smul _ v, inner_smul_left, zero_mul]

@[simp] lemma inner_zero_right (v : V) : ⟪v, 0⟫ = 0 :=
by rw [inner_comm, inner_zero_left]

@[simp] lemma inner_self_pos {v : V} (h : v ≠ 0) : 0 < ⟪v, v⟫ :=
lt_of_le_of_ne (inner_self_nonneg _) (λ  h_inner_0, h (eq_zero_of_inner_self_eq_zero h_inner_0.symm))

def orthogonal (u v : V) : Prop := ⟪u, v⟫ = 0

infix ` ⊥ `:50 := orthogonal

lemma orthogonal_comm {u v : V} (H : u ⊥ v) : v ⊥ u :=
by unfold orthogonal at *; rw [inner_comm, H]


section 

/- first, we define norm internally, to show that an inner product space is a normed space -/

private def ip_norm (v : V):= real.sqrt ⟪v, v⟫

private lemma ip_norm_zero : ip_norm (0 : V) = 0 :=
by rw [ip_norm, inner_zero_left, real.sqrt_zero]

private lemma ip_norm_squared (v : V) : (ip_norm v) ^2 = ⟪v, v⟫ :=
real.sqr_sqrt (inner_self_nonneg v)

private lemma ip_norm_nonneg (v : V) : 0 ≤ ip_norm v := real.sqrt_nonneg _

private lemma eq_zero_of_ip_norm_eq_zero {v : V} (H : ip_norm v = 0) : v = 0 :=
have ⟪v, v⟫ = 0, by rw [←ip_norm_squared, H, pow_two, zero_mul],
eq_zero_of_inner_self_eq_zero this

private lemma ip_norm_eq_zero_iff (v : V) : ip_norm v = 0 ↔ v = 0 :=
begin
  apply iff.intro,
  { intro h, 
    apply eq_zero_of_ip_norm_eq_zero h },
  { intro h,
    rw [h, ip_norm_zero] }
end

private lemma ip_norm_neg (v : V) : ip_norm (- v) = ip_norm v :=
by rw [ip_norm, inner_neg_left, inner_neg_right , neg_neg, ip_norm]

private lemma ip_norm_smul (r : ℝ) (v : V) : ip_norm (r • v) = abs r * ip_norm v :=
begin
  rw [ip_norm, inner_smul_left, inner_smul_right , ←mul_assoc],
  rw [real.sqrt_mul (mul_self_nonneg r) _, real.sqrt_mul_self_eq_abs, ip_norm]
end

private lemma ip_norm_pythagorean {u v : V} (ortho : u ⊥ v) :
    (ip_norm (u + v))^2 = (ip_norm u)^2 + (ip_norm v)^2 :=
begin
  rw [orthogonal] at ortho,
  rw [ip_norm_squared, ip_norm_squared, inner_add_right, inner_add_left, inner_add_left],
  rw [inner_comm v u, ortho, zero_add, add_zero, ip_norm, real.sqr_sqrt (inner_self_nonneg _)]
end

private def ip_proj_on (u : V) {v : V} (H : v ≠ 0) : V :=
(⟪u, v⟫ / (ip_norm v)^2) • v

private lemma ip_proj_on_orthogonal (u : V) {v : V} (H : v ≠ 0) :
  ip_proj_on u H ⊥ (u - ip_proj_on u H) :=
begin
  rw [ip_proj_on, orthogonal, inner_sub_right, inner_smul_left, inner_smul_left, inner_smul_right],
  rw [ip_norm_squared],
  rw [div_mul_cancel _ (assume H', H (eq_zero_of_inner_self_eq_zero H'))],
  rw [inner_comm v u, sub_self]
end

private lemma ip_norm_proj_on_eq (u : V) {v : V} (H : v ≠ 0) :
  ip_norm (ip_proj_on u H) = abs ⟪u, v⟫ / ip_norm v :=
have H1 : ip_norm v ≠ 0, from assume H', H (eq_zero_of_ip_norm_eq_zero H'),
begin
  rw [ip_proj_on, ip_norm_smul, abs_div, abs_of_nonneg (pow_two_nonneg (ip_norm v)), pow_two],
  rw [div_mul_eq_mul_div, ←div_mul_div, div_self H1, mul_one]
end

private lemma ip_norm_squared_pythagorean (u : V) {v : V} (H : v ≠ 0) :
  (ip_norm u)^2 = (ip_norm (u - ip_proj_on u H))^2 + (ip_norm (ip_proj_on u H))^2 :=
calc
  (ip_norm u)^2 = (ip_norm (u - ip_proj_on u H + ip_proj_on u H))^2 :
                    by rw sub_add_cancel
            ... = (ip_norm (u - ip_proj_on u H))^2 + (ip_norm (ip_proj_on u H))^2 :
                    ip_norm_pythagorean (orthogonal_comm (ip_proj_on_orthogonal u H))

private lemma ip_norm_proj_on_le (u : V) {v : V} (H : v ≠ 0) :
  ip_norm (ip_proj_on u H) ≤ ip_norm u :=
have (ip_norm u)^2 ≥ (ip_norm (ip_proj_on u H))^2,
  begin
    rw [ip_norm_squared_pythagorean u H],
    apply le_add_of_nonneg_left (pow_two_nonneg (ip_norm (u - ip_proj_on u H)))
  end,
le_of_sqr_le_sqr (ip_norm_nonneg _) (ip_norm_nonneg _) this

private lemma ip_cauchy_schwartz (u v : V) : abs ⟪u, v⟫ ≤ ip_norm u * ip_norm v :=
begin
  by_cases h_cases : v = (0 : V),
  { rw [h_cases, inner_zero_right, abs_zero, ip_norm_zero, mul_zero] },
  { have h_norm_ne : ip_norm v ≠ 0, from λH, h_cases (eq_zero_of_ip_norm_eq_zero H),
    have h_norm_gt : ip_norm v > 0, from lt_of_le_of_ne (real.sqrt_nonneg _) (ne.symm h_norm_ne),
    let H := ip_norm_proj_on_le u h_cases,
    rw [ip_norm_proj_on_eq u h_cases] at H,
    exact (div_le_iff h_norm_gt).1 H
 }
end

private lemma ip_cauchy_schwartz' (u v : V) : ⟪u, v⟫ ≤ ip_norm u * ip_norm v :=
le_trans (le_abs_self _) (ip_cauchy_schwartz _ _)

private lemma ip_norm_triangle (u v : V) : ip_norm (u + v) ≤ ip_norm u + ip_norm v :=
have H : ⟪u, v⟫ ≤ ip_norm u * ip_norm v, from ip_cauchy_schwartz' u v,
have (ip_norm (u + v))^2 ≤ (ip_norm u + ip_norm v)^2, from
  calc
    (ip_norm (u + v))^2 = (ip_norm u)^2 + (ip_norm v)^2 + ⟪u, v⟫ + ⟪u, v⟫ :
            begin simp only [ip_norm, real.sqr_sqrt (inner_self_nonneg _)],
              rw [inner_add_left, inner_add_right, inner_add_right, inner_comm v u],
              rw [←add_assoc, ←add_right_comm _ _ ⟪v, v⟫, ←add_right_comm _ _ ⟪v, v⟫]
            end
    ... ≤ (ip_norm u)^2 + (ip_norm v)^2 + ip_norm u * ip_norm v + ⟪u, v⟫ :
            add_le_add_right (add_le_add_left H _) _
    ... ≤ (ip_norm u)^2 + (ip_norm v)^2 + ip_norm u * ip_norm v + ip_norm u * ip_norm v :
            add_le_add_left H _
    ... = (ip_norm u + ip_norm v)^2 :
            by rw [pow_two, pow_two, pow_two, right_distrib, left_distrib, left_distrib, ←add_assoc,
                         add_right_comm _ (ip_norm v * ip_norm v),
                         add_right_comm _ (ip_norm v * ip_norm v),
                         mul_comm (ip_norm v) (ip_norm u)],
le_of_sqr_le_sqr (ip_norm_nonneg _) (add_nonneg (ip_norm_nonneg _) (ip_norm_nonneg _)) this
 
instance has_norm [real_inner_product_space V] :
has_norm V := { norm := ip_norm }.


lemma normed_group_core : normed_group.core V := 
{
  norm_eq_zero_iff := ip_norm_eq_zero_iff,
  triangle := ip_norm_triangle,
  norm_neg := ip_norm_neg
}

instance is_normed_group [real_inner_product_space V] :
  normed_group V := 
normed_group.of_core _ normed_group_core


-- TODO: Should we have a similar setup like "normed_group_core" for inner_product_space?

instance is_normed_space [real_inner_product_space V] :
  normed_space ℝ V := 
{
  norm_smul := ip_norm_smul
}


end

/- now we restate the new theorems using the norm notation -/

lemma norm_squared (v : V) : ∥ v ∥^2 = ⟪v, v⟫ := ip_norm_squared v

lemma norm_pythagorean {u v : V} (ortho : u ⊥ v) : ∥ u + v ∥^2 = ∥ u ∥^2 + ∥ v ∥^2 :=
ip_norm_pythagorean ortho

def proj_on (u : V) {v : V} (H : v ≠ 0) : V := (⟪u, v⟫ / ∥ v ∥^2) • v

lemma proj_on_orthogonal (u : V) {v : V} (H : v ≠ 0) :
  proj_on u H ⊥ (u - proj_on u H) :=
ip_proj_on_orthogonal u H

lemma norm_proj_on_eq (u : V) {v : V} (H : v ≠ 0) :
  ∥ proj_on u H ∥ = abs ⟪u, v⟫ / ∥ v ∥ :=
ip_norm_proj_on_eq u H

lemma norm_squared_pythagorean (u : V) {v : V} (H : v ≠ 0) :
  ∥ u ∥^2 = ∥ u - proj_on u H ∥^2 + ∥ proj_on u H ∥^2 :=
ip_norm_squared_pythagorean u H

lemma norm_proj_on_le (u : V) {v : V} (H : v ≠ 0) :
  ∥ proj_on u H ∥ ≤ ∥ u ∥ := ip_norm_proj_on_le u H

theorem cauchy_schwartz (u v : V) : abs ⟪u, v⟫ ≤ ∥ u ∥ * ∥ v ∥ := ip_cauchy_schwartz u v

theorem cauchy_schwartz' (u v : V) : ⟪u, v⟫ ≤ ∥ u ∥ * ∥ v ∥ := ip_cauchy_schwartz' u v

theorem eq_proj_on_cauchy_schwartz {u v : V} (H : v ≠ 0) (H₁ : abs ⟪u, v⟫ = ∥ u ∥ * ∥ v ∥) :
  u = proj_on u H :=
have ∥ v ∥ ≠ 0, from assume H', H ((normed_group_core.norm_eq_zero_iff _).1 H'),
have ∥ u ∥ = ∥ proj_on u H ∥, by rw [norm_proj_on_eq, H₁, mul_div_cancel _ this],
have ∥ u - proj_on u H ∥^2 + ∥ u ∥^2 = 0 + ∥ u ∥^2,
begin 
  rw zero_add, 
  convert (norm_squared_pythagorean u H).symm
end,
have ∥ u - proj_on u H ∥^2 = 0, from eq_of_add_eq_add_right this,
show u = proj_on u H,
begin 
  rw pow_two at this,
  exact eq_of_sub_eq_zero ((normed_group_core.norm_eq_zero_iff _).1 ((or_self _).1 (mul_eq_zero.1 this)))
end


/- Instances of real_inner_product_space -/

instance real :
  real_inner_product_space ℝ :=
{ real_inner_product_space .
  inner := (*),
  inner_add_left := add_mul,
  inner_smul_left := mul_assoc,
  inner_comm := mul_comm,
  inner_self_nonneg := mul_self_nonneg,
  eq_zero_of_inner_self_eq_zero := by apply eq_zero_of_mul_self_eq_zero,
}

-- TODO: move
@[simp] lemma real.ring_add (x y : ℝ) : ring.add x y = x + y := rfl
@[simp] lemma real.no_zero_divisors_mul (x y : ℝ) : no_zero_divisors.mul x y = x * y := rfl

section
set_option class.instance_max_depth 50
instance prod {V : Type*} [real_inner_product_space V] {W : Type*} [real_inner_product_space W]:
  real_inner_product_space (V × W):= 
{
  inner := λ x y, ⟪x.1,y.1⟫ + ⟪x.2,y.2⟫,
  inner_add_left := 
  begin 
    intros u v w, 
    dsimp [inner_add_left],
    let H1 := @inner_add_left V _ u.fst v.fst w.fst, 
    let H2 := @inner_add_left W _ u.snd v.snd w.snd,
    unfold add_group.add, unfold add_comm_group.add, unfold add_comm_semigroup.add, unfold add_semigroup.add,
    simp [H1, H2] --TODO: why so complicated?
  end,
  inner_smul_left := begin simp [inner_smul_left, mul_add], end,
  inner_comm := by simp [inner_comm],
  inner_self_nonneg := by intros; exact add_nonneg (inner_self_nonneg _) (inner_self_nonneg _),
  eq_zero_of_inner_self_eq_zero := 
    begin 
      intros x hx, 
      apply prod.eq_iff_fst_eq_snd_eq.2, 
      dsimp at hx,
      rw add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg 
          (inner_self_nonneg _) (inner_self_nonneg _) at hx,
      apply and.intro,
      { apply eq_zero_of_inner_self_eq_zero hx.1 },
      { apply eq_zero_of_inner_self_eq_zero hx.2 }
    end
}
end

end real_inner_product_space
