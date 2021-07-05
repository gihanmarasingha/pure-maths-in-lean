import myint.basic equations.cancellation_i -- hide

/-
# Equations

## Level 14: Uniqueness of additive inverse

We've seen the uniqueness of (right) additive identity. Now we'll show the uniqueness of (right)
additive inverse.
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

/- Hint : Hint
Use `add_add_neg`.
-/

/- Theorem : no-side-bar
Let `x` and `y` be integers. If `x + y = 0`, then `y = -x`. 
-/
theorem right_additive_inverse_unique (x y : ℤ) (h : x + y = 0)
  : y = -x :=
begin [pure_maths]
  rw ←add_add_neg x y,
  rw h,
  rw zero_add,
  refl,
end

end pre_group -- hide

end exlean -- hide