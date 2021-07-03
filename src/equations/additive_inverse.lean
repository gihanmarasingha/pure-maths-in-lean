import myint.basic equations.unique_additive_identity -- hide

/-
# Equations

## Level 12: Additive inverse

The Lean theorem `add_right_neg` states that `x + (-x) = 0` for every integer `x`. In mathematics,
this property is called (right) additive inverse.
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

theorem add_right_neg (a : ℤ) : a + (-a) = 0 := myint.add_right_neg a -- hide

/- Hint : Hint
You might find it useful to use the previously-proved theorem `add_right_comm`.
-/

/- Theorem : no-side-bar
For all integers `x` and `y`, we have `(x + y) + -x = y`.
-/
theorem add_add_neg (x y : ℤ) : (x + y) + (-x) = y :=
begin [pure_maths]
  rw add_right_comm,
  rw add_right_neg,
  rw zero_add,
  refl,
end

end exlean -- hide