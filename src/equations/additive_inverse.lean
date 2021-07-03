import myint.basic equations.additive_identity -- hide

/-
# Equations

## Level 10: Additive inverse

The Lean theorem `add_right_neg` states that `x + (-x) = 0` for every integer `x`. In mathematics,
this property is called (right) additive identity.
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x y z : ℤ) -- hide

/- 
Your goal is to prove `zero_add`, the right additive identity property, using `add_zero`.
Once you've done this, `zero_add` will be available to you in future levels.
-/

/- Axiom : add_zero (a : ℤ) :
a + 0 = a
-/
theorem add_right_neg (a : ℤ) : a + (-a) = 0 := myint.add_right_neg a -- hide

/- Theorem : zero_add (a : ℤ)
0 + a = a
-/
theorem neg_add : (-x) + x = 0 :=
begin [pure_maths]
  rw add_comm, rw add_right_neg, refl,
end

end exlean -- hide