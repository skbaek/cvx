import linear_algebra.finite_dimensional
import missing_mathlib.linear_algebra.dimension

universes u v v' w
open_locale classical

open vector_space cardinal submodule module function

variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
{V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂]

namespace finite_dimensional

lemma findim_bot [finite_dimensional K V] : 
  findim K (⊥ : submodule K V) = 0 :=
begin
  apply cardinal.nat_cast_inj.1,
  rw findim_eq_dim,
  rw dim_bot,
  refl,
end

lemma bot_of_findim_zero [finite_dimensional K V]
  (s : submodule K V) (h : findim K s = 0) : s = ⊥ :=
begin
  apply submodule.bot_of_dim_zero,
  rw ←findim_eq_dim,
  apply cardinal.nat_cast_inj.2 h,
end

@[simp] lemma findim_top [finite_dimensional K V] : 
  findim K (⊤ : submodule K V) = findim K V :=
begin
  apply cardinal.nat_cast_inj.1,
  rw [findim_eq_dim, findim_eq_dim, dim_top]
end

lemma exists_mem_ne_zero_of_findim_pos
  [finite_dimensional K V] (h_dim : 0 < findim K V) : ∃ x : V, x ≠ 0 :=
begin
  apply @exists_mem_ne_zero_of_dim_pos' K V (by apply_instance),
  rw ←findim_eq_dim,
  rw ←cardinal.nat_cast_lt at h_dim,
  apply h_dim
end

lemma findim_sup_add_findim_inf_eq [finite_dimensional K V] (s t : submodule K V) :
  findim K (s ⊔ t : submodule K V) + findim K (s ⊓ t : submodule K V) 
    = findim K s + findim K t :=
begin
  have := s.dim_sup_add_dim_inf_eq t,
  repeat { rw ←findim_eq_dim at this },
  exact this,
end

lemma eq_top_of_disjoint [finite_dimensional K V] (s t : submodule K V) 
  (hdim : findim K s + findim K t = findim K V)
  (hdisjoint : disjoint s t) : s ⊔ t = ⊤ :=
begin
  have h_findim_inf : findim K ↥(s ⊓ t) = 0,
  { rw [disjoint, le_bot_iff] at hdisjoint,
    rw [hdisjoint, findim_bot] },
  apply eq_top_of_findim_eq,
  rw ←hdim,
  convert findim_sup_add_findim_inf_eq s t,
  rw h_findim_inf,
  refl,
end

lemma lt_omega_of_linear_independent {ι : Type w} [finite_dimensional K V]
  {v : ι → V} (h : linear_independent K v) : 
  cardinal.mk ι < cardinal.omega :=
begin
  apply cardinal.lift_lt.1,
  apply lt_of_le_of_lt,
  apply linear_independent_le_dim h,
  rw [←findim_eq_dim, cardinal.lift_omega, cardinal.lift_nat_cast],
  apply cardinal.nat_lt_omega,
end

end finite_dimensional