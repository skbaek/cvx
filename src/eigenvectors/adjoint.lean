import analysis.normed_space.real_inner_product

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

lemma has_adjoint_comm {F G : V →ₗ[ℝ] V} : 
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
  rw has_adjoint_comm at *,
  apply has_adjoint_unique_left hG hG'
end

lemma has_adjoint_zero : has_adjoint (0 : V →ₗ[ℝ] V) 0 :=
by simp [has_adjoint, linear_map.zero_apply, inner_zero_left, inner_zero_right]

lemma has_adjoint_id : has_adjoint (id : V →ₗ[ℝ] V) id :=
by simp [has_adjoint, linear_map.id_apply]

def adjoint (F : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
if h : ∃ G, has_adjoint F G then classical.some h else 0

lemma adjoint_of_has_adjoint {F G : V →ₗ[ℝ] V} (hF : has_adjoint F G) : 
  F.adjoint = G :=
begin
  apply has_adjoint_unique_right _ hF,
  rw [adjoint, dif_pos],
  apply classical.some_spec ⟨G, hF⟩,
end

lemma adjoint_zero : (0 : V →ₗ[ℝ] V).adjoint = 0 := 
adjoint_of_has_adjoint has_adjoint_zero

lemma adjoint_id : (id : V →ₗ[ℝ] V).adjoint = id := 
adjoint_of_has_adjoint has_adjoint_id

def normal (F : V →ₗ[ℝ] V) : Prop := 
∃ G, has_adjoint F G ∧ F * G = G * F

lemma has_adjoint_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  ∃ G, has_adjoint F G :=
begin
  unfold normal at h,
  rcases h with ⟨w, hw⟩,
  use w,
  apply hw.left,
end

lemma adjoint_comm_of_normal {F : V →ₗ[ℝ] V} (h : normal F) :
  F * F.adjoint = F.adjoint * F :=
begin
  unfold normal at h,
  rcases h with ⟨w, hw⟩,
  rw adjoint_of_has_adjoint hw.left,
  apply hw.right,
end

-- lemma ker_adjoint_of_normal {F : V →ₗ[ℝ] V} (h : normal F) : 
--   F.adjoint.ker = F.ker := 
-- sorry

end linear_map