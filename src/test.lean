import data.rat tactic.norm_num .mat

def foo_1 : list rat := [2,-1,0]
def foo_2 : list rat := [-1,2,-1]
def foo_3 : list rat := [0,-1,1]
def foo : list (list rat) := [foo_1, foo_2, foo_3]
def bar : mat rat 3 3 := lists_to_mat 3 3 foo
def quz : mat rat 3 3 := bar * bar
def qux : rat := quz ⟨0, nat.zero_lt_succ _⟩ ⟨0, nat.zero_lt_succ _⟩ 

open tactic

#check matrix.mul
#check whnf


example : qux = (5 : rat) :=
begin
  simp only [qux, quz, bar, foo, foo_1, foo_2, foo_3, 
  lists_to_mat],

end



#exit

def rs1 : list rat := [218.21,-3493.21,0.1937] 
def rs2 : list rat := [-131.32,2.232,-1293] 

def dot_prod : list rat → list rat → rat 
| [] []       := 0
| [] (_::_) := 0
| (_::_) [] := 0
| (r1::rs1) (r2::rs2) := r1 * r2 + dot_prod rs1 rs2 

def bar : rat := (-1835131801/50000 : rat)

example : dot_prod rs1 rs2 = bar :=
begin
  simp only [rs1,rs2,bar,dot_prod],
  norm_num,
end