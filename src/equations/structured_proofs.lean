import myint.basic equations.associativity -- hide

/-
# Equations

## Level 6: Structuring proofs with `have`

The `have` tactic introduces a hypothesis into the context. It's a way to add structure to your
proofs, stating and proving intermediate results before using them.

Consider the goal `⊢ x + ((x + y) + z) = x + (z + (x + y))`.

One way to close this goal is to rewrite, giving specific arguments to `add_comm`.
Another option is to introduce an intermediate goal of proving `(x + y) + z = z + (x + y)`.

This is accomplished using `have h : (x + y) + z = z + (x + y)` (followed by a comma). 
There's nothing special about `h` as the name of the hypothesis. Change it to whatever you wish.

This opens up a new goal: you'll see 2 goals in right-hand pane. The top goal is the new goal,
namely `⊢ (x + y) + z = z + (x + y)`. The bottom goal is the old goal, only with a new hypothesis,
`h : (x + y) + z = z + (x + y)`.

You first work on closing the new goal, then close the original goal using hypothesis `h`.
-/

/- Hint : Focussing on one goal at a time

If you want to work only on goal, put braces after the `have`. When you're cursor is in the
inner brace, you'll only be working on the first goal.
```
have h : (x + y) + z = z + (x + y),
{ sorry },
sorry
``` 
-/

/- Tactic : have
`have` is used to introduce a new hypothesis into the context. It opens a new goal for the proof
of the hypothesis.

For example, `have h2 : x + y = y + x` introduces a new goal, to prove
`x + y = y + x` while adding the hypothesis `h2 : x + y = y + x` to the context of the old goal.
-/


namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x y z : ℤ) -- hide

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. Then `x + ((x + y) + z) = x + (z + (x + y)))`.
-/
theorem add_right_comm_comm : x + ((x + y) + z) = x + (z + (x + y)) :=
begin [pure_maths]
  have h : (x + y) + z = z + (x + y),
  rw add_comm, refl,
  rw h, refl,
end

/-
## Translation to a hand-written proof

In my hand-written proof below, I omit references to reflexivity.

> I claim `h : (x + y) + z = z + (x + y)`.
> To prove this, use commutativity of addition.
> Rewrite the original goal using `h`.
-/

end exlean -- hide