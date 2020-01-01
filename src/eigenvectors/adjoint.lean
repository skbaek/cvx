import analysis.normed_space.real_inner_product
import missing_mathlib.linear_algebra.basic

noncomputable theory
open_locale classical

-- TODO: Same for complex inner product?
-- Or for bilinear forms?

variables {V : Type*} [inner_product_space V]

namespace linear_map

def has_adjoint (F G : V →ₗ[ℝ] V) : Prop :=
∀ x y, inner (F x) y = inner x (G y)

lemma has_adjoint_def {F G : V →ₗ[ℝ] V} (hG : has_adjoint F G) : 
  ∀ x y, inner (F x) y = inner x (G y) := hG

lemma has_adjoint_symm {F G : V →ₗ[ℝ] V} : 
  has_adjoint F G ↔ has_adjoint G F := 
begin 
  unfold has_adjoint,
  split,
  repeat
  { intros h x y,
    rw inner_product_space.comm _ y,
    rw inner_product_space.comm x _,
    apply (h y x).symm }
end
  
lemma has_adjoint_unique_left {F F' G : V →ₗ[ℝ] V}
  (hF : has_adjoint F G) (hF' : has_adjoint F' G) : F = F' :=
begin
  ext,
  rw ←sub_eq_zero,
  apply inner_product_space.definite,
  simp only [inner_sub_left, inner_sub_right],
  simp [has_adjoint_def hF, has_adjoint_def hF']
end

lemma has_adjoint_unique_right {F G G' : V →ₗ[ℝ] V}
  (hG : has_adjoint F G) (hG' : has_adjoint F G') : G = G' :=
begin
  rw has_adjoint_symm at *,
  apply has_adjoint_unique_left hG hG'
end

lemma has_adjoint_zero : has_adjoint (0 : V →ₗ[ℝ] V) 0 :=
by simp [has_adjoint, linear_map.zero_apply, inner_zero_left, inner_zero_right]

lemma has_adjoint_id : has_adjoint (id : V →ₗ[ℝ] V) id :=
by simp [has_adjoint, linear_map.id_apply]

lemma has_adjoint_smul {F G : V →ₗ[ℝ] V} (c : ℝ) :
  has_adjoint F G → has_adjoint (c • F) (c • G) :=
by simp [has_adjoint, inner_smul_left, inner_smul_right] {contextual := tt}

lemma has_adjoint_neg {F G : V →ₗ[ℝ] V} :
  has_adjoint F G → has_adjoint (- F) (- G) :=
begin
  rw ← neg_one_smul _ F,
  rw ← neg_one_smul _ G,
  apply has_adjoint_smul (-1),
end

lemma has_adjoint_add {F G F' G' : V →ₗ[ℝ] V} :
  has_adjoint F G → has_adjoint F' G' → has_adjoint (F + F') (G + G') :=
by simp [has_adjoint, inner_add_left, inner_add_right] {contextual := tt}

lemma has_adjoint_sub {F G F' G' : V →ₗ[ℝ] V} :
  has_adjoint F G → has_adjoint F' G' → has_adjoint (F - F') (G - G') :=
by simp [has_adjoint, inner_add_left, inner_add_right] {contextual := tt}

def adjoint (F : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
if h : ∃ G, has_adjoint F G then classical.some h else 0

lemma adjoint_of_has_adjoint {F G : V →ₗ[ℝ] V} (hF : has_adjoint F G) : 
  F.adjoint = G :=
begin
  apply has_adjoint_unique_right _ hF,
  rw [adjoint, dif_pos],
  apply classical.some_spec ⟨G, hF⟩,
end

lemma has_adjoint_adjoint {F : V →ₗ[ℝ] V} (h : ∃ G, has_adjoint F G) : 
  has_adjoint F (adjoint F) :=
begin
  rcases h with ⟨w, hw⟩,
  rw adjoint_of_has_adjoint hw,
  apply hw,
end

lemma inner_adjoint {F : V →ₗ[ℝ] V} (h : ∃ G, has_adjoint F G) : 
  ∀ x y, inner (F x) y = inner x (F.adjoint y) :=
has_adjoint_def (has_adjoint_adjoint h)

lemma adjoint_adjoint {F : V →ₗ[ℝ] V} (h : ∃ G, has_adjoint F G) :
   F.adjoint.adjoint = F :=
begin
  rw adjoint_of_has_adjoint,
  rw has_adjoint_symm,
  apply has_adjoint_adjoint h,
end

lemma adjoint_zero : (0 : V →ₗ[ℝ] V).adjoint = 0 := 
adjoint_of_has_adjoint has_adjoint_zero

lemma adjoint_id : (id : V →ₗ[ℝ] V).adjoint = id := 
adjoint_of_has_adjoint has_adjoint_id

lemma adjoint_smul (c : ℝ) (F : V →ₗ[ℝ] V) (h : ∃ G, has_adjoint F G) : 
  (c • F).adjoint = c • F.adjoint := 
adjoint_of_has_adjoint (has_adjoint_smul c (has_adjoint_adjoint h))

lemma adjoint_neg (F : V →ₗ[ℝ] V) (h : ∃ G, has_adjoint F G) : 
  (- F).adjoint = - F.adjoint := 
adjoint_of_has_adjoint (has_adjoint_neg (has_adjoint_adjoint h))

lemma adjoint_add (F G : V →ₗ[ℝ] V) 
  (hF : ∃ F', has_adjoint F F') (hG : ∃ G', has_adjoint G G'): 
  (F + G).adjoint = F.adjoint + G.adjoint := 
adjoint_of_has_adjoint (has_adjoint_add (has_adjoint_adjoint hF) (has_adjoint_adjoint hG))

lemma adjoint_sub (F G : V →ₗ[ℝ] V) 
  (hF : ∃ F', has_adjoint F F') (hG : ∃ G', has_adjoint G G'): 
  (F - G).adjoint = F.adjoint - G.adjoint := 
adjoint_of_has_adjoint (has_adjoint_sub (has_adjoint_adjoint hF) (has_adjoint_adjoint hG))

def normal (F : V →ₗ[ℝ] V) : Prop := 
∃ G, has_adjoint F G ∧ F.comp G = G.comp F

lemma has_adjoint_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  ∃ G, has_adjoint F G :=
begin
  unfold normal at h,
  rcases h with ⟨w, hw⟩,
  use w,
  apply hw.left,
end

lemma adjoint_comm_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  F.comp F.adjoint = F.adjoint.comp F :=
begin
  unfold normal at h,
  rcases h with ⟨w, hw⟩,
  rw adjoint_of_has_adjoint hw.left,
  apply hw.right,
end

lemma normal_adjoint_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  normal F.adjoint :=
begin
  use F,
  split,
  { rw has_adjoint_symm,
    apply has_adjoint_adjoint (has_adjoint_of_normal h) },
  { rw adjoint_comm_of_normal h },
end

lemma normal_of_has_adjoint_self {F : V →ₗ[ℝ] V} (h : has_adjoint F F) :
  normal F :=
⟨F, ⟨h, rfl⟩⟩

lemma normal_zero : normal (0 : V →ₗ[ℝ] V) :=
normal_of_has_adjoint_self has_adjoint_zero

lemma normal_id : normal (id : V →ₗ[ℝ] V) :=
normal_of_has_adjoint_self has_adjoint_id

lemma normal_smul_of_normal {F : V →ₗ[ℝ] V} (c : ℝ) (h : normal F) :
  normal (c • F) :=
begin
  rcases h with ⟨G, hG_adjoint, hG_comm⟩,
  refine ⟨c • G, ⟨has_adjoint_smul c hG_adjoint, _⟩⟩,
  simp only [comp_smul, smul_comp, hG_comm]
end

lemma normal_neg_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  normal (- F) :=
begin
  rw ← neg_one_smul _ F,
  apply normal_smul_of_normal (-1) h,
end

lemma normal_sub_algebra_map_of_normal
  {F G : V →ₗ[ℝ] V} (c : ℝ) (hF : normal F) :
  normal (F - algebra_map _ c) :=
begin
  rcases hF with ⟨G, hG_adjoint, hG_comm⟩,
  refine ⟨G - algebra_map _ c, ⟨has_adjoint_sub hG_adjoint (has_adjoint_smul c has_adjoint_id), _⟩⟩,
  simp only [comp_eq_mul] at *,
  simp [add_mul, mul_add, hG_comm, algebra.commutes]
end

lemma inner_adjoint_eq_inner_of_normal {F : V →ₗ[ℝ] V} (h : normal F) : 
  ∀ x, inner (F.adjoint x) (F.adjoint x) = inner (F x) (F x) :=
begin
  intros x,
  rw inner_adjoint (has_adjoint_of_normal h),
  rw ←comp_apply,
  rw ←inner_adjoint (has_adjoint_of_normal h),
  rw ←comp_apply,
  rw adjoint_comm_of_normal h,
  apply inner_comm
end

lemma ker_adjoint_of_normal {F : V →ₗ[ℝ] V} (h : normal F) : 
  F.adjoint.ker = F.ker := 
begin
  ext,
  rw [mem_ker, ←inner_self_eq_zero, inner_adjoint_eq_inner_of_normal h,
      mem_ker, ←inner_self_eq_zero],
end

lemma ker_pow_eq_ker_of_normal 
  {F : V →ₗ[ℝ] V} (k : ℕ) (hn : normal F) : 
  (F ^ k.succ).ker = F.ker :=
begin
  induction k with k ih,
  { refl },
  { ext,
    split,
    { assume h : x ∈ ker (F ^ k.succ.succ),
      have h0 : F.adjoint ((F ^ k.succ) x) = 0,
      { rw [mem_ker, pow_succ, mul_app, ←mem_ker, 
          ←ker_adjoint_of_normal hn, mem_ker] at h,
        exact h },
      show x ∈ ker F,
        by rw [←ih, mem_ker, ←inner_self_eq_zero, pow_succ, mul_app,
          inner_adjoint (has_adjoint_of_normal hn), ←mul_app F, 
          ←pow_succ, h0, inner_zero_right] },
    { intro h,
      rw [mem_ker] at *,
      rw [pow_succ', mul_app, h, map_zero] } }
end

end linear_map