import linear_algebra.sesquilinear_form

universes u v

structure hermitian_form (R : Type u) (M : Type v) [ring R] (I : R ≃+* Rᵒᵖ)
  [add_comm_group M] [module R M] extends sesq_form R M I :=
(sesq_comm: ∀ (x y : M), (I (sesq x y)).unop = sesq y x)

variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]
variables {I : R ≃+* Rᵒᵖ} {H : hermitian_form R M I}

instance : has_coe_to_fun (hermitian_form R M I) :=
⟨_, λ H, H.to_sesq_form.sesq⟩

lemma hermitian_form.comm (H : hermitian_form R M I) : ∀ (x y : M), (I (H x y)).unop = H y x := 
by apply hermitian_form.sesq_comm