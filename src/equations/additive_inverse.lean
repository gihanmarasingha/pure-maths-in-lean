import myint.basic equations.unique_additive_identity -- hide

/-
# Equations

## Level 12: Additive inverse

The Lean theorem `add_left_neg` states that `(-a) + a = 0` for every integer `a`. In mathematics,
this property is called (left) additive inverse.

Likewise `add_right_neg (a : ℤ) : a + (-a) = 0`.

You'll use one of these properties in proving the next result.
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

/- Axiom : add_left_neg (a : ℤ) :
(-a) + a = 0
-/
theorem add_left_neg (a : ℤ) : (-a) + a = 0  := myint.add_left_neg a -- hide

/- Axiom : add_right_neg (a : ℤ) :
a + (-a) = 0
-/
theorem add_right_neg (a : ℤ) : a + (-a) = 0  := myint.add_right_neg a -- hide

/- Hint : Hint
You might find it useful to use the previously-proved theorem `add_right_comm`.
-/

/- Theorem :
For all integers `x` and `y`, we have `(x + y) + -x = y`.
-/
theorem add_add_neg (x y : ℤ) : (x + y) + (-x) = y :=
begin [pure_maths]
  rw add_right_comm,
  rw add_right_neg,
  rw zero_add,
  refl,
end

end pre_group -- hide

export pre_group (add_add_neg) -- hide

end exlean -- hide