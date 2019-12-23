import linear_algebra.finite_dimensional

universes u v v' w
open_locale classical

open vector_space cardinal submodule module function

variables {K : Type u} {V : Type v} [discrete_field K] [add_comm_group V] [vector_space K V]
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

lemma findim_sup_add_findim_inf_eq [finite_dimensional K V] (s t : submodule K V) :
  findim K (s ⊔ t : submodule K V) + findim K (s ⊓ t : submodule K V) 
    = findim K s + findim K t :=
begin
  have := dim_sup_add_dim_inf_eq s t,
  repeat { rw ←findim_eq_dim at this },
  norm_cast at this,
  exact this,
end

lemma eq_top_of_disjoint [finite_dimensional K V] (s t : submodule K V) 
  (hdim : findim K s + findim K t = findim K V)
  (hdisjoint : disjoint s t) : s ⊔ t = ⊤ :=
begin
  have h_findim_inf : findim K ↥(s ⊓ t) = 0,
  { rw [disjoint, lattice.le_bot_iff] at hdisjoint,
    rw [hdisjoint, findim_bot] },
  apply eq_top_of_findim_eq,
  rw ←hdim,
  convert findim_sup_add_findim_inf_eq s t,
  rw h_findim_inf,
  refl,
end

end finite_dimensional