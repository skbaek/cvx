
universe variables u v w


def foo : Type 1 := sorry
def bar : Type 2 := sorry
def x : foo := sorry

set_option pp.universes true
#check lift.{2 9} x