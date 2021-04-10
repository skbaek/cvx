import data.finsupp

universe variable u

instance has_zero_Type : has_zero Type :=
{ zero := unit }

def mytype := string →₀ Type

structure varbag (ty : string → Type) :=
(val : Π (v : string), ty v)

def myvarbag : varbag (λ v, if v = "x" then ℕ else unit) :=
 varbag.mk begin
intro v,
by_cases v = "x",
simp [h],
exact 0,
simp [h],
exact ()
 end



-- def myvarbag : varbag (λ v, match v with | "x" := ℕ | _ := unit end) :=
-- varbag.mk (λ (v : string), (match v with | "x" := 0 | _ := () end : (match v with | "x" := ℕ | _ := unit end : Type)))

/- ---------------/

def var_list := list (string × Type)

def var_bag : var_list → Type
| [] := unit
| (x :: xs) := x.2 × var_bag xs

namespace var_bag

def getty (v : string) : var_list → Type
| [] := unit
| (x :: xs) := if x.1 = v then x.2 else getty xs

def get (v : string) {vl : var_list} (vb : var_bag vl) : getty v vl :=
begin
  induction vl with x vl ih,
  exact (),
  cases vb with val vb,
  by_cases x.1 = v,
  simp [getty, h],
  exact val,
  simp [getty, h],
  exact ih vb,
end
-- match vl, vb, vl = vl with
-- | [], _, h := begin cases vl, end
-- | (x :: xs), (val, vb), _ := sorry--if x.1 = v then _ else get vb
-- end


def get' (v : string) : Π {vl : var_list}, var_bag vl → Σ ty : Type, ty
| [] _ := sigma.mk unit ()
| (x :: xs) (val, vb) := if x.1 = v then sigma.mk x.2 val else get' vb

end var_bag

def vb : var_bag [("x", ℕ), ("y", option ℕ)] :=
(0, some 1, ())

#reduce vb.get "x"
#reduce vb.get "y"
#reduce vb.get "z"

#check (λ vb : var_bag [("x", ℕ), ("y", ℕ)], @has_add.add ℕ _ ((vb.get "x") : ℕ) ((vb.get "y") : ℕ))

#check (λ vb : var_bag [("x", ℕ), ("y", ℕ)], @has_add.add ℕ _ ((vb.get' "x").2 : ℕ) ((vb.get' "y").2 : ℕ))