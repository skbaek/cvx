import algebra.group_power

universes u v
variable {α : Type u}

 /- monoid -/
section monoid
variables [monoid α] {β : Type u} [add_monoid β]

lemma pow_eq_mul_pow_sub {α : Type*} [monoid α] (p : α) {m n : ℕ} (h : m ≤ n) : p ^ m * p ^ (n - m) = p ^ n :=
by rw [←pow_add, nat.add_sub_cancel' h]

lemma pow_eq_pow_sub_mul {α : Type*} [monoid α] (p : α) {m n : ℕ} (h : m ≤ n) : p ^ (n - m) * p ^ m = p ^ n :=
by rw [←pow_add, nat.sub_add_cancel h]

end monoid