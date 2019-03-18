import data.nat.basic 

namespace nat

lemma max_succ_succ {m n} : 
  max (succ m) (succ n) = succ (max m n) :=
begin
  by_cases h1 : m ≤ n, 
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)], 
  { rw not_le at h1, have h2 := le_of_lt h1,
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)] }
end

end nat