import myint.basic equations.backward_rewrite.level -- hide

/-
# Equations

## Level 9: Additive identity

The Lean theorem `add_zero` states that `x + 0 = x` for every integer `x`. In mathematics, this
property is called (right) additive identity.
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x y z : ℤ) -- hide


/- Axiom : add_zero (a : ℤ) :
a + 0 = a
-/
theorem add_zero (a : ℤ) : a + 0 = a := myint.add_zero' a -- hide

/- Hint: Hint for structured proof

Introduce and prove the hypotheses `h2 : y + z * x = (z + x) + y` and
`h3 : (z + x) + y = y + (z + x)` using the `have` tactic. Finish by rewriting with these
hypotheses.
-/

/- Theorem : zero_add (a : ℤ)
0 + a = a
-/
theorem zero_add : 0 + x = x :=
begin [pure_maths]
  rw add_comm, rw add_zero, refl,
end

end exlean -- hide