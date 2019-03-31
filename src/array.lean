import .vector  

variables {α β : Type}
variables {k m n : nat}

open nat

namespace array

def cell_size [has_repr α] (as : array m α) : nat := 
as.foldl 0 (λ a n, max n (repr a).length)

def sum [has_zero α] [has_add α] (v : array n α) : α := foldl v 0 (+)

def dot_prod [has_zero α] [has_add α] [has_mul α] (v w : array n α) : α := 
array.sum (map₂ (*) v w)

#check tactic.simplify


--#exit
--lemma ext'_succ (a b : array (k+1) α) : 
--  ∀ (m : nat) (h : m < k), read a ⟨m, _⟩ = read b ⟨m, _⟩ → 
--  read a ⟨k, lt_succ_self k⟩ = read b ⟨k, lt_succ_self k⟩ → 
--  a = b := 
--sorry


end array

#exit
def vector.to_array : ∀ {k : nat}, vector α k → array k α 
| 0     _ := array.nil 
| (k+1) v := 
  (mk_array (k+1) (v.nth ⟨0, nat.zero_lt_succ _⟩)).foreach 
  (λ i _, v.nth i)


#exit
run_cmd tactic.norm_num 
`(array.dot_prod
(vector.to_array (⟨([0,1,2] : list nat), rfl⟩ : vector nat 3))
(vector.to_array (⟨([0,1,2] : list nat), rfl⟩ : vector nat 3)))
