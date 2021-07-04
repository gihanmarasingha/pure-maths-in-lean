import myint.basic equations.commutativity_rw -- hide

/-
# Equations

## Level 3: Rewriting with hypotheses

Look at the theorem below. It seems that you're being asked to prove `x + y = x + 2 * x`.
Surely that isn't true in general! What's
going on? If you look carefully, you'll see an additional hypothesis, `h : y = 2 * x`.

The `:` is just notation for naming a hypothesis (also called an assumption).
So the statement of the theorem can be read:

> Let `x` and `y` be integers. Let `h` be the hypothesis `y = 2 * x`.
> Then `x + y = x + 2 * x`.

When you start the proof, you'll note in the top-right pane that `h : y = 2 * x` has been
added to the context.

You can use the hypothesis to rewrite the goal by typing `rw h` much as you used `rw add_comm`
to rewrite via the theorem `add_comm`.

### Tasks

* Before doing the problem in Lean, think about what effect `rw h` will have on the goal.
* Predict what error message Lean will produce if you replace `sorry` with `refl`. Test your
prediction.
-/

namespace exlean -- hide

open_locale mynum -- hide

namespace pre_group -- hide

variables (x y : ℤ) -- hide

/- Theorem : no-side-bar
Let `x` and `y` be integers. Let `h` be the hypothesis `y = 2 * x`. Then `x + y = x + 2 * x`.
-/
theorem add_eq_add_two_mul_self_of_eq_two_mul (h : y = 2 * x)
  : x + y = x + 2 * x :=
begin [pure_maths]
  rw h,
  refl,
end

end pre_group -- hide

end exlean -- hide

/-
## Translation to a hand-written proof

> Rewriting using `h`, the goal is to prove `x + 2 * x = x + 2 * x`.
> This follows by reflexivity.
-/

