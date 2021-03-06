import myint.basic -- hide

/-
# Equations

## Level 2: Commutativity of addition via `rw`

Now we'll prove something (slighlty) more interesting, that `x + y = y + x` for all integers `x`
and `y`. Try the `refl` tactic below (remember to put a comma after `refl`) and see what happens.

You'll get an error message:
```
invalid apply tactic, failed to unify
  x + y = y + x
with
  ?m_2 = ?m_2
```

Lean tells you that you're trying to use `refl` to prove `x + y = y + x`, but it expects a target
of the form `?m_2 = ?m_2`. There's no special meaning to the underscores here. It's the same as
writing `?X = ?X` as in the previous level.

The problem: even though we 'know' the left and right sides are equal, they are not
*identically equal*.
Fortunately, Lean comes with a *theorem* of just the right kind. It's called `add_comm`, which is
short for additive commutativity.
The result `add_comm a b` states that `a + b = b + a`, where `a` and `b` are integers.

To apply this theorem, we'll use the `rw` (short for `rewrite`) tactic.

Replace the `sorry` below with `rw add_comm` (followed by a comma—I won't mention this from now
on).

Lean will look for the first expression in the target that matches the pattern `a + b` and
replace every instance of that expression with `b + a`. Here, Lean finds `x + y` and replaces
it with `y + x`.

Equally, if `h` is an equation of the form `p = q` (where `p` and `q` are expressions),
`rw h` will cause Lean to look for `p` in the target and replace it with `q`.

Having issued `rw add_comm`, the goal is to prove `y + x = y + x`.
You know how to prove a goal of this kind from the previous level.
Write the proof on the line after the `rw add_comm`.
-/

namespace exlean -- hide

open_locale mynum -- hide

variables (x y : ℤ) -- hide

namespace pre_group -- hide

/- Axiom : add_comm (a b : ℤ) :
a + b = b + a
-/
theorem add_comm (a b : ℤ) : a + b = b + a := myint.add_comm' a b -- hide

/- Hint : Moving through a proof

Your proof of the theorem below will use two lines of code. If you move your cursor to a previous
line, Lean will show you the tactic state at any point in the proof. If you click on the name of
a theorem, you'll get some brief documentation.
-/

/- Theorem : no-side-bar
`x + y = y + x`, for all integers `x` and `y`.
-/
theorem x_plus_y_eq_y_plus_x : x + y = y + x :=
begin [pure_maths]
  rw add_comm,
  refl,
end

end pre_group -- hide

end exlean -- hide

/-
## Translation to a hand-written proof

In words, the `rw add_comm` says, "Rewrite using commuativity of addition".
As hand-written proofs aren't interactive, it's helpful to mention explicitly any changes to the
context. Here's a hand-written proof of the above result.

> Rewriting using commutativity of addition, the goal is to prove `y + x = y + x`.
> This follows by reflexivity.
-/

/- Tactic : rw
If `h` is an equation of the form `p = q`, `rw h` rewrites replaces `p` in the target with `q`.

If `k` is in the context, `rw h at k` performs the rewrite at `k` instead of at the target.

`rw ←h` will rewrite backward: every occurrence of `q` is replaced with `p`. Type `\l` to produce `←`.

`rw [h1, h2, h3]` rewrites with multiple hypotheses (you aren't limited to three)!
-/

/-
## Anatomy of a level

Each level contains three vertial panes. The left-hand pane contains a list of the tactics and
theorem statements you've seen so far. Click on the arrows to dig deeper.

The middle pane is the one you're reading now! It contains text and interactive exercises.
The right-hand pane contains the Lean Infoview window, showing the 'tactic state' and error messages.

You can navigate through the book using the buttons in the top horizonal pane. The circular arrow
resets your progress.
-/

/-
## How `rw` here differs from that in standard Lean

The `rw` tactic used in this book is slightly different the standard `rw`. In particular, if
the result of a rewrite is an equation of the form `X = X`, then the standard `rw` tactic will
automatically close the goal via reflexivity.

This automation has been disabled here to help you think more carefully about proof construction.
-/

