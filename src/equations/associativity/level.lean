import myint.basic equations.commutativity_rw.level -- hide

/-
# Equations

## Level 5: Associativity

Time for a new theorem. This one is called `add_assoc`, which is short for additive associativity.

The result `add_assoc a b c` states that `(a + b) + c = a + (b + c)`, for all integers `a`, `b`,
and `c`. You can see the statement in the sidebar on the left by unfolding 'Theorem statements'.

As with `add_comm`, you can use `add_assoc` to rewrite the goal using `rw add_assoc`.

Below, your task is to prove `(x + y) + z = x + (z + y)`.

**Before writing a Lean proof**, construct a hand-written proof.
-/

namespace exlean -- hide

open_locale mynum -- hide

/- Axiom : add_assoc (a b c : ℤ) :
(a + b) + c = a + (b + c)
-/
theorem myint.add_assoc (a b c : ℤ) : a + b + c = a + (b + c) := myint.add_assoc' a b c -- hide

open myint

variables (x y z : ℤ) -- hide

/- Hint : Hint

You'll need to rewrite with both `add_comm` and `add_assoc`. You may need to give arguments to one
of your rewrites, as described in the previous level.
-/

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. Then `(x + y) + z = x + (z + y)`.
-/
theorem add_assoc_right_comm : (x + y) + z = x + (z + y) :=
begin [pure_maths]
  rw add_assoc,
  rw add_comm y z,
  refl,
end

/-
## Translation to a hand-written proof

In the following hand-written proof, I omit the word 'rewriting'.

> By associativity, the goal is to prove `x + (y + z) = x + (z + y)`.
> By commutativity, the goal is to prove `x + (z + y) = x + (z + y)`.
> This follows by reflexivity.
-/

end exlean -- hide