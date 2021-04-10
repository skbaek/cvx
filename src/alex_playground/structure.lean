
import data.real.basic

structure myspace :=
(x : ℝ) (y : ℝ)


#check (λ s : myspace, s.x + s.y)

example : (λ s : myspace, s.x + s.y) ≠ (λ s : myspace, s.x + s.y) :=
begin
unfold myspace,
end