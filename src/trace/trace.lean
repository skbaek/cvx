import data.matrix.basic

universe variables u v

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

open_locale matrix

section trace

def trace [add_comm_monoid α] (M : matrix m m α) : α := 
finset.univ.sum (λ i, M i i)

variables {L M N : matrix m m α}

@[simp] lemma trace_transpose [add_comm_monoid α] : 
  Mᵀ.trace = M.trace :=
rfl

lemma trace_add [add_comm_monoid α] : 
  (M + N).trace = M.trace + N.trace :=
finset.sum_add_distrib

lemma trace_smul [ring α] {a : α} : 
  (a • M).trace = a * M.trace :=
finset.mul_sum.symm

lemma trace_comm [comm_ring α] : 
  (M ⬝ N).trace = (N ⬝ M).trace :=
begin
  classical,
  unfold trace,
  dsimp [(⬝)],
  rw finset.sum_comm,
  simp only [mul_comm],
end

lemma trace_zero [add_comm_monoid α] : 
  trace (0 : matrix m m α) = 0 :=
by simp only [trace, add_monoid.smul_zero, finset.sum_const, matrix.zero_val]

lemma trace_diagonal [add_comm_monoid α] [decidable_eq m] {d : m → α} :
  trace (diagonal d) = finset.univ.sum d :=
by simp [trace, diagonal]

lemma trace_one [decidable_eq m] [add_comm_monoid α] [has_one α] :
  trace (1 : matrix m m α) = (fintype.card m : α) :=
begin
  unfold has_one.one,
  rw [trace_diagonal, finset.sum_const, add_monoid.smul_one],
  refl,
end

end trace

end matrix