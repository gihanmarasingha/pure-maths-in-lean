import myint.basic equations.additive_identity -- hide

/-
# Equations

## Level 11: Uniqueness of additive identity

In a previous level, we saw that there's an integer `0` with the properties that
`x + 0 = x` for every `x`.

In this level, you'll show that `0` is the *only* integer that satisfies this property.
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x e : ℤ) -- hide

/- Hint : Hint
Use the `specialize` tactic.
-/

/- Theorem : right_additive_identity_unique
Let `e` be an integer satsifying the property `∀ (x : ℤ), x + e = x`. Then `e` must be `0`.
-/
theorem right_additive_identity_unique (h : ∀ (x : ℤ), x + e = x) : e = 0 :=
begin [pure_maths]
  specialize h 0,
  rw [←h, zero_add],
  refl,
end

end exlean -- hide