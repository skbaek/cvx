import analysis.normed_space.basic linear_algebra.sesquilinear_form topology.instances.complex

open vector_space field set real

class real_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends sym_sesq_form ℝ α (ring_invo.id ℝ) :=
(sesq_self_nonneg : ∀ (x : α), sesq x x ≥ 0)
(sesq_self_eq_zero_iff : ∀ (x : α), sesq x x = 0 ↔ x = 0)

namespace real_inner_product_space

open ring_invo

variables {α : Type*} [add_comm_group α] [vector_space ℝ α] [real_inner_product_space α]

noncomputable def inner_product : α → α → ℝ := (real_inner_product_space.to_sym_sesq_form α).to_sesq_form.sesq  

local infix `₀` : 74 := inner_product 

namespace inner_product

lemma comm (x y : α) : x ₀ y = y ₀ x := sym_sesq_form.map_sesq (ring_invo.id ℝ) y x 

lemma self_nonneg (x : α) : x ₀ x ≥ 0 := sesq_self_nonneg x   

lemma self_eq_zero_iff {x : α} : (inner_product x x) = 0 ↔ x = (0 : α) := sesq_self_eq_zero_iff x

@[simp] lemma add_left (x y z : α) : 
(x + y) ₀ z = x ₀ z + y ₀ z := sesq_form.sesq_add_left _ _ _ _
 
@[simp] lemma add_right (x y z : α) : 
x ₀ (y + z) = x ₀ y + x ₀ z := sesq_form.sesq_add_right _ _ _ _

@[simp] lemma smul_left (a : ℝ) (x y : α) :
(a • x) ₀ y = a * (x ₀ y) := sesq_form.sesq_smul_left _ _ _ _

@[simp] lemma smul_right (a : ℝ) (x y : α) :
x ₀ (a • y) = a * (x ₀ y) := sesq_form.sesq_smul_right _ _ _ _

open sym_sesq_form sesq_form

@[simp] lemma zero_left (x : α) :
0 ₀ x = 0 := zero_sesq x  

@[simp] lemma zero_right (x : α) :
x ₀ 0 = 0 := sesq_zero x 

@[simp] lemma neg_left (x y : α) : 
-x ₀ y = -(x ₀ y) := sesq_neg_left x y 

@[simp] lemma neg_right (x y : α) : 
x ₀ -y = -(x ₀ y) := sesq_neg_right x y   

lemma sub_left (x y z : α) : 
(x - y) ₀ z = (x ₀ z) - (y ₀ z) := sesq_sub_left x y z

lemma sub_right (x y z : α) : 
x ₀ (y - z) = (x ₀ y) - (x ₀ z) := sesq_sub_right x y z

lemma self_eq_zero (x : α) : 
x ₀ x = 0 ↔ x = 0 := 
begin
  split; intros H,
  { suffices : x ₀ x = 0,
    { exact inner_product.self_eq_zero_iff.mp this },
    { simpa }
  },
  { rw H,
    simp }
end

lemma self_ne_zero_iff {x : α} : 
(x ₀ x) ≠ 0 ↔ x ≠ 0 :=
⟨ λ H, (iff_false_left H).mp inner_product.self_eq_zero_iff, 
  λ H, (iff_false_right H).mp inner_product.self_eq_zero_iff⟩ 

end inner_product

noncomputable def ip_norm (x : α) := sqrt(x ₀ x)

local notation |a| := ip_norm a 

lemma mul_self_ip_norm (x : α) : |x| * |x| = x ₀ x :=
begin
  dunfold ip_norm,
  rw mul_self_sqrt (inner_product.self_nonneg x),
end

lemma ip_norm_sqr (x : α) : |x|^2 = x ₀ x := 
by rw pow_two; exact mul_self_ip_norm x

open classical

theorem abs_inner_product_le_mul_ip_norm (x y : α) :
abs (x ₀ y) ≤ |x|*|y| := 
sorry

def ip_norm_eq_zero_iff (x : α) :
|x| = 0 ↔ x = 0 := 
sorry

theorem abs_inner_product_eq_mul_ip_norm_iff (x y : α) : 
abs(x ₀ y) = |x|*|y| ↔ (∃ (a : ℝ), x = a • y) ∨ (∃ (a : ℝ), y = a • x) :=
sorry

noncomputable instance : metric_space α := 
{ 
  dist := λ x y, |x - y|, 
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry
}

@[simp] lemma ip_norm_smul (a : ℝ) (x : α) : 
|a • x| = abs(a)*|x| := sorry

noncomputable instance complex.normed_field : normed_field ℝ :=
{ norm := abs,
  dist_eq := by intros; refl, 
  norm_mul := abs_mul,}

noncomputable instance : normed_space ℝ α := 
{ norm := ip_norm,
  dist_eq := by intros; refl,
  norm_smul := ip_norm_smul}

@[simp] lemma ip_norm_zero : 
|(0 : α)| = 0 := @norm_zero α _

lemma norm_ne_zero_iff_ne_zero {G : Type*} [normed_group G] {g : G} : 
∥g∥ ≠ 0 ↔ g ≠ 0 := 
⟨ λ H, (iff_false_left H).mp (norm_eq_zero g), 
  λ H, (iff_false_right H).mp (norm_eq_zero g)⟩ 

theorem parallelogram_law (x y : α) :
|x + y|^2 + |x - y|^2 = 2*|x|^2 + 2*|y|^2 :=
begin
  dunfold ip_norm,
  rw [sqr_sqrt (inner_product.self_nonneg (x + y)), sqr_sqrt (inner_product.self_nonneg (x - y)),
    sqr_sqrt (inner_product.self_nonneg x), sqr_sqrt (inner_product.self_nonneg y)],
  suffices : (x ₀ x) + ((x ₀ x) + ((y ₀ y) + (y ₀ y))) = 2 * (x ₀ x) + 2 * (y ₀ y),
  { rw [inner_product.add_left, inner_product.add_right, inner_product.add_right,
      inner_product.sub_left, inner_product.sub_right, inner_product.sub_right],
    simpa },
  { rw [←inner_product.comm y],
    ring }
end

lemma inner_product.self_add (x y : α) :
(x + y) ₀ (x + y) = (x ₀ x) + (y ₀ y) + (x ₀ y) + (y ₀ x) :=
begin
  rw [inner_product.add_left, inner_product.add_right, inner_product.add_right],
  simpa [field.add_assoc, field.add_comm],
end

def is_normalized (x : α) := |x| = 1

noncomputable def normalize (x : α) := |x|⁻¹ • x 

lemma normalize.is_normalized (x : α) (ho : x ≠ 0) : 
is_normalized (normalize x) :=
sorry

def normalize_set :
set α → set α := image(λ x, |x|⁻¹ • x)

lemma normalize_set.is_normalized 
(A : set α) (Ho : (0 : α) ∉ A) : 
∀ x ∈ normalize_set(A), is_normalized x :=
begin
  dunfold normalize_set,
  dunfold image, 
  intros,
  have Ha : ∃ (a : α), a ∈ A ∧ normalize a = x,
  { rw mem_set_of_eq at H, 
    exact H },
  cases Ha with a Hl,
  rw ←Hl.right,
  have ho : a ≠ 0,
  { intros h,
    rw h at Hl,
    exact Ho Hl.left },
  exact normalize.is_normalized a ho,
end

def orthogonal (x y : α) : Prop := x ₀ y = 0 

local notation a ⊥ b := orthogonal a b 

def orthogonal_sym (x y : α) :
(x ⊥ y) ↔ (y ⊥ x) := @sym_sesq_form.ortho_sym ℝ α _ (ring_invo.id ℝ) _ _ (to_sym_sesq_form α) _ _ 
 
lemma orthogonal_refl_iff_zero (x : α) : 
(x ⊥ x) ↔ x = 0 := inner_product.self_eq_zero_iff  

def orthogonal_smul_left (x y : α) (a : ℝ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ ((a • x) ⊥ y) := @sesq_form.ortho_smul_left _ _ _ _ _ _ (real_inner_product_space.to_sym_sesq_form α).to_sesq_form _ _ _ ha

def orthogonal_smul_right (x y : α) (a : ℝ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ (x ⊥ (a • y)) := @sesq_form.ortho_smul_right _ _ _ _ _ _ (real_inner_product_space.to_sym_sesq_form α).to_sesq_form _ _ _ ha

theorem orthogonal_imp_not_lindep (x y : α) (hx : x ≠ 0) (hy : y ≠ 0) : 
(x ⊥ y) → ¬∃ (a : ℝ), (a ≠ 0) ∧ (x = a • y ∨ a • x = y) :=
begin
  intros H1,
  apply not_exists.mpr,
  intros a,
  intros H2,
  unfold orthogonal at H1,
  cases H2 with ha H2,
  cases H2,  
  { rw H2 at H1,
    rw [inner_product.smul_left, mul_eq_zero] at H1,
    cases H1,
    { trivial }, 

    { exact hy ((inner_product.self_eq_zero_iff).mp H1) }},
    
  { rw ←H2 at H1,
    rw [inner_product.smul_right, mul_eq_zero] at H1,
    cases H1,
    { exact ha H1 },

    { exact hx ((inner_product.self_eq_zero_iff).mp H1) }}
end 

/-- Pythagorean Theorem -/
theorem sq_norm_add (x y : α) (H : x ⊥ y) :
|x + y|^2 = |x|^2 + |y|^2 :=
begin
  dunfold ip_norm,
  rw [sqr_sqrt (inner_product.self_nonneg (x + y)), sqr_sqrt (inner_product.self_nonneg x),
    sqr_sqrt (inner_product.self_nonneg y), inner_product.self_add],
  unfold orthogonal at H,
  rw [←inner_product.comm x y, H,
    field.add_zero, field.add_zero],
end

def is_orthogonal_set (s : set α) :=
∀ x y ∈ s, (x ⊥ y) ↔ x ≠ y 

def is_orthonormal_set (s : set α) :=
is_orthogonal_set s ∧ ∀ x ∈ s, is_normalized x

noncomputable def proj (x y : α) :=
((y ₀ x)/( |x|*|x| )) • x

lemma zero_proj (x : α) :
proj 0 x = 0 := by dunfold proj; simp

lemma proj_zero (x : α) :
proj x 0 = 0 := by dunfold proj; simp

lemma proj_self_eq_self (x : α) :
proj x x = x :=
begin
  have ho : x = 0 ∨ x ≠ 0,
  { apply em },
  dunfold proj,
  cases ho,
  { rw ho,
    simp },

  { rw [mul_self_ip_norm,
      div_self (inner_product.self_ne_zero_iff.mpr ho), one_smul] }
end

lemma smul_proj (x y : α) {a : ℝ} : 
proj x (a • y) = a • (proj x y) :=
begin
  dunfold proj,
  rw [inner_product.smul_left, smul_smul],
  ring,
end

lemma proj_smul (x y : α) {a : ℝ} (ha : a ≠ 0) :
proj (a • x) y = proj x y := 
sorry

lemma norm_proj_le (x y : α) : 
|proj x y| ≤ |y| :=
sorry

lemma proj_eq_zero_of_orthogonal {x y : α} (H : x ⊥ y) :
proj y x = 0 := 
begin
  delta orthogonal at H,
  delta proj,
  simp [H]
end

lemma proj_eq_self_iff_lindep {x y : α} :
proj x y = y ↔ ∃ (a : ℝ), y = a • x :=
sorry

end real_inner_product_space

set_option trace.class_instances true


noncomputable instance sesq_form.real : @sesq_form ℝ ℝ _ (ring_invo.id ℝ) (ring.to_add_comm_group ℝ) ring.to_module:=
{
  sesq := sorry,
  sesq_add_left := sorry,
  sesq_smul_left := sorry,
  sesq_add_right := sorry,
  sesq_smul_right := sorry
}

noncomputable instance sym_sesq_form.real : @sym_sesq_form ℝ ℝ _ (ring_invo.id ℝ) (ring.to_add_comm_group ℝ) ring.to_module:=
{
  map_sesq := sorry
}

noncomputable instance real_inner_product_space.real : @real_inner_product_space ℝ (ring.to_add_comm_group ℝ) discrete_field.to_vector_space :=
{
  sesq_self_nonneg := sorry,
  sesq_self_eq_zero_iff := sorry
}

-- TODO: move
@[simp] lemma real.ring_add (x y : ℝ) : ring.add x y = x + y := rfl
@[simp] lemma real.no_zero_divisors_mul (x y : ℝ) : no_zero_divisors.mul x y = x * y := rfl


local infix `₀` : 74 := real_inner_product_space.inner_product 


noncomputable instance sesq_form.prod 
  {V : Type*} [add_comm_group V] [vector_space ℝ V] [real_inner_product_space V] 
  {W : Type*} [add_comm_group W] [vector_space ℝ W] [real_inner_product_space W] :
  @sesq_form ℝ (V × W) _ (ring_invo.id ℝ) prod.add_comm_group prod.module:=
{
  sesq := λ x y, x.1 ₀ y.1 + x.2 ₀ y.2,
  sesq_add_left := sorry,
  sesq_smul_left := sorry,
  sesq_add_right := sorry,
  sesq_smul_right := sorry
}

noncomputable instance sym_sesq_form.prod 
  {V : Type*} [add_comm_group V] [vector_space ℝ V] [real_inner_product_space V] 
  {W : Type*} [add_comm_group W] [vector_space ℝ W] [real_inner_product_space W] : 
  @sym_sesq_form ℝ (V × W) _ (ring_invo.id ℝ) prod.add_comm_group prod.module:=
{
  map_sesq := sorry
}

noncomputable instance real_inner_product_space.prod
  {V : Type*} [add_comm_group V] [vector_space ℝ V] [real_inner_product_space V] 
  {W : Type*} [add_comm_group W] [vector_space ℝ W] [real_inner_product_space W] : 
   @real_inner_product_space ℝ (ring.to_add_comm_group ℝ) (discrete_field.to_vector_space) :=
{
  sesq_self_nonneg := sorry,
  sesq_self_eq_zero_iff := sorry
}


/-
class Hilbert_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends real_inner_product_space α :=
(complete : ∀{f : filter α}, cauchy f → ∃x, f ≤ nhds x) 

instance Hilbert_space.to_complete_space (α : Type*) [add_comm_group α] [vector_space ℝ α] [Hilbert_space α] : complete_space α :=
{complete := @Hilbert_space.complete _ _ _ _}
-/