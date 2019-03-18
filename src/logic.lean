import logic.basic  

open tactic

variables {α β γ : Type} {p q r s : Prop}

lemma fun_mono_2 {p : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 = p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2 {p : α → β → Prop} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) :=
λ h1 h2, by rw [h1, h2]