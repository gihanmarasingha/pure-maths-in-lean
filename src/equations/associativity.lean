import myint.basic equations.commutativity_rw -- hide

/-
# Equations

## Level 5: Associativity

Time for a new theorem. This one is called `add_assoc`, which is short for additive associativity.

The result `add_assoc a b c` states that `(a + b) + c = a + (b + c)`, for all integers `a`, `b`,
and `c`. You can see the statement in the sidebar on the left by unfolding 'Theorem statements'.

As with `add_comm`, you can use `add_assoc` to rewrite the goal using `rw add_assoc`.

Below, your task is to prove `(x + y) + z = x + (z + y)`. In future levels, this theorem will
be available as `add_right_comm`.

**Before writing a Lean proof**, construct a hand-written proof.
-/

namespace exlean -- hide

open_locale mynum -- hide

namespace pre_group -- hide

/- Axiom : add_assoc (a b c : ℤ) :
(a + b) + c = a + (b + c)
-/
theorem myint.add_assoc (a b c : ℤ) : a + b + c = a + (b + c) := myint.add_assoc' a b c -- hide

open myint

/-
### Tasks

* Think about what would happen if you performed `rw add_assoc` once, twice, and thrice.
  Try it out and compare with your predication.

* Prove the theorem below.

-/


/- Hint : Hint

You'll need to rewrite with both `add_comm` and `add_assoc`. You may need to give arguments to one
of your rewrites, as described in the previous level.
-/

/- Theorem : 
Let `x`, `y`, and `z` be integers. Then `(x + y) + z = x + (z + y)`.
-/
theorem add_right_comm (x y z : ℤ) : (x + y) + z = (x + z) + y :=
begin [pure_maths]
  rw add_assoc,
  rw add_comm y z,
  rw add_assoc,
  refl,
end

/-
## Translation to a hand-written proof

In the following hand-written proof, I omit the word 'rewriting'.

> By associativity, the goal is to prove `x + (y + z) = x + (z + y)`.
> By commutativity, the goal is to prove `x + (z + y) = x + (z + y)`.
> This follows by reflexivity.
-/

end pre_group -- hide

end exlean -- hide