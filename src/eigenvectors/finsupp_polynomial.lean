import linear_algebra.finsupp
import data.polynomial

universes u v w

lemma finsupp_total_eq_eval₂ (β : Type v) (γ : Type w)
  [decidable_eq β] [decidable_eq γ] [comm_ring γ] [decidable_eq β] [add_comm_group β] [module γ β]
  (f : β →ₗ[γ] β) (v : β) (p : polynomial γ) : 
  (finsupp.sum p (λ n b, b • (f ^ n) v))  
    = polynomial.eval₂ (λ a, a • linear_map.id) f p v :=
begin
 dunfold polynomial.eval₂ finsupp.sum,
 convert @finset.sum_hom _ _ _ p.support _ _ _ (λ h : β →ₗ[γ] β, h v) _,
 simp
end

lemma finsupp_total_eq_eval₂ (β : Type v) (γ : Type w)
  [decidable_eq β] [decidable_eq γ] [comm_ring γ] [decidable_eq β] [add_comm_group β] [module γ β]
  (f : β →ₗ[γ] β) (v : β) (p : polynomial γ) : 
  (finsupp.total ℕ β γ (λ n : ℕ, (f ^ n) v) : (ℕ →₀ γ) → β) p 
    = polynomial.eval₂ (λ a, a • linear_map.id) f p v :=
begin


end