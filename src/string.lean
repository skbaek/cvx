namespace string

def resize_core : nat → list char → list char 
| 0     _       := [] 
| k     []      := list.repeat ' ' k
| (k+1) (c::cs) := c::(resize_core k cs)

def resize (k : nat) (s : string) : string := 
⟨resize_core k s.data⟩

end string