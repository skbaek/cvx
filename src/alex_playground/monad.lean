


def vars := [("x", ℕ), ("y", bool)]


def f : string → nat 
| "x" := 1
| _ := 0

example (s : string) : s ≠ "x" → f s = 0 :=
begin
intro h,
by_cases s = "x",

end

def vars' : string → Type 
| "x" := ℕ 
| "y" := bool
| _ := unit




#print vars'._main


def point : Π v, option (vars' v)
| "x" := some (0 : ℕ)
| "y" := some tt
| _ := none


.
(p : problem)
do
  constr <- p.get_constr "c"
  