import .array2

variables {k m n : nat}

meta def write_col (A_jj' : rat) (j : nat) (v : array j rat) (h1 : j < n) : 
  nat → array₂ n n rat → array₂ n n rat | k A := 
if h2 : n ≤ k then A else 
let j' : fin n := ⟨j, h1⟩ in
let k' : fin n := ⟨k, lt_of_not_ge' h2⟩ in
let A_kj : rat := A.read k' j' in
let w : array j rat := (array.read A k').take j (le_of_lt h1) in
let r : rat := (A_kj - array.dot_prod w v) / A_jj' in
let A' : array₂ n n rat := A.write k' j' r in
write_col (k+1) A'

meta def LDLT : nat → array₂ n n rat → array₂ n n rat | j A := 
if h1 : n ≤ j then A else 
let h2 : j < n := lt_of_not_ge' h1 in
let j' : fin n := ⟨j, h2⟩ in
let v : array j rat := (mk_array j 0).foreach 
  (λ i _, 
    let i' : fin n := ⟨i.val, lt_trans i.is_lt h2⟩ in
    (A.read j' i') * (A.read i' i')) in  
let w : array j rat := ((array.read A j').take j (le_of_lt h2)) in
let A_jj : rat := A.read j' j' in
let A_jj' : rat := A_jj - (array.dot_prod w v) in
let A' : array₂ n n rat := A.write j' j' A_jj' in
let A'' : array₂ n n rat :=  write_col A_jj' j v h2 (j+1) A' in
LDLT (j+1) A''
