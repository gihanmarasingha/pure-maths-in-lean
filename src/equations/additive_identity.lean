import myint.basic equations.backward_rewrite -- hide

/-
# Equations

## Level 9: Additive identity

The Lean theorem `add_zero` states that `x + 0 = x` for every integer `x`. In mathematics, this
property is called (right) additive identity. Note `add_zero` should appear as a 'Theorem statement'
in the left-hand pane. 
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

/- Axiom : add_zero (a : ℤ) :
a + 0 = a
-/
theorem add_zero (a : ℤ) : a + 0 = a := myint.add_zero' a -- hide

/- 
Your goal is to prove `zero_add`, the right additive identity property, using `add_zero`.
Once you've done this, `zero_add` will be available to you in future levels.

As always, construct a hand-written proof **before** writing your Lean proof.
-/

/- Theorem :
`0 + a = a` for every integer `a`.
-/
theorem zero_add (a : ℤ) : 0 + a = a :=
begin [pure_maths]
  rw add_comm, rw add_zero, refl,
end

end pre_group -- hide

end exlean -- hide