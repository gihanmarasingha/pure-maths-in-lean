import myint.basic equations.additive_inverse -- hide

/-
# Equations

## Level 13: Cancellation I

Recall the (right) uniqueness of additive identity. Let `y` be an integer. If for every integer `x`,
we have `x + y = x`, then `y = 0`.

In this level, we'll prove a theorem that is subtly different. Let `y` and `x` be integers. If
`x + y = x`, then `y = 0`.

**Question**: how does this new statement differ from from the uniqueness of additive identity?

The new result cannot be proved using only additive identity. You'll need to use the
additive inverse property.

This may be the most challenging level so far.
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

/- Hint : Hint
Use `add_add_neg`.
-/

/- Theorem : no-side-bar
If `a + b = a`, then `b = 0`.
-/
theorem eq_zero_of_add_right_eq_self (a b : ℤ) (h : a + b = a) : b = 0 :=
begin [pure_maths]
  have h2 : (a + b) + (-a) = b,
  { rw add_add_neg, refl,  },
  rw ← h2,
  rw h,
  rw add_right_neg,
  refl,
end

end exlean -- hide