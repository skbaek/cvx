variable {α : Type}
variables {m n : nat}

namespace array

def cell_size [has_repr α] (as : array m α) : nat := 
as.foldl 0 (λ a n, max n (repr a).length)

def sum [has_zero α] [has_add α] (v : array n α) : α := foldl v 0 (+)

def dot_prod [has_zero α] [has_add α] [has_mul α] (v w : array n α) : α := 
array.sum (map₂ (*) v w)

end array