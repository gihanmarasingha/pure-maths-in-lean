import myint.basic equations.additive_identity -- hide

/-
# Equations

## Level 11: Uniqueness of additive identity

In a previous level, we saw that there's an integer `0` with the properties that
`x + 0 = x` for every `x`.

In this level, you'll show that `0` is the *only* integer that satisfies this property.
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

/-
### Rewriting at a hypothesis

By default, `rw add_assoc` (say) applies `add_assoc` to the target. If `h` is a hypothesis in the
local context, `rw add_assoc at h` will rewrite `h` using `add_assoc`.

In the example below, we rewrite at `h` and finish with `exact`. Alternatively, we could have
performed a backward `rw` at the target using `rw ←add_assoc`.
-/

example (x y z : ℤ) (h : (x + y) + z = 20) : x + (y + z) = 20 :=
begin
  rw add_assoc at h,
  exact h,
end

/- Hint : Hint
Use the `specialize` tactic.
-/

/- Theorem : no-side-bar
Let `e` be an integer satsifying the property `∀ (x : ℤ), x + e = x`. Then `e` must be `0`.
-/
theorem right_additive_identity_unique (e : ℤ) (h : ∀ (x : ℤ), x + e = x) : e = 0 :=
begin [pure_maths]
  specialize h 0,
  rw zero_add at h,
  exact h,
end

end pre_group -- hide

end exlean -- hide