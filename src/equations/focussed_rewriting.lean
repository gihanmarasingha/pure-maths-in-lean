import myint.basic equations.commutativity_rw-- hide

/-
# Equations

## Level 4: Focussed rewriting

Here, you're asked to prove `(x + y) + z = z + (y + x)`. Clearly a case for rewriting with the
`add_comm` theorem.

Think about what `rw add_comm` will do. What will happen if you do `rw add_comm` twice? Try this
below and test your conjecture.

What happens is that `rw add_comm` looks for an expression of the form `a + b`. It finds one in
`(x + y) + z`, matching `a` with `x + y` and `b` with `z`. It replaces this with `b + a`. That is,
with `z + (x + y)`.

You might wonder why this is the first match. Why doesn't Lean work on `x + y` first, matching
`a` with `x` and `b` with `y`? It's because Lean works outside-in, then left-to-right. The second
`+` operator in `(x + y) + z` is the outermost operator, so is read first by Lean.

The problem: applying `rw add_comm` to the new goal `⊢ z + (x + y) = z + (y + x)` will match `a`
with `z` and `b` with `x + y`, rewriting the goal to `⊢ (x + y) + z = z + (y + x)`, taking us back
to where we started!

### Focussing a rewrite with arguments

Recall that `add_comm a b` is the theorem that `a + b = b + a`. The quantities `a` and `b` are
*arguments* to the theorem `add_comm`.
Equally, `add_comm x (y + z)` is the theorem that `x + (y + z) = (y + z) + x`. This theorem has
arguments `x` and `y + x`. Note than arguments can be expressions, not just variables.

Applying `rw add_comm x (y + z)` transforms `⊢ z + (x + (y + z)) = z` to
`⊢ z + ((y + z) + x) = z`.

Use arguments, where necessary, to prove the theorem below.

-/

namespace exlean -- hide

open_locale mynum -- hide

variables (x y z : ℤ) -- Declare `x`, `y`, and `z` to be integers.

/- Hint : Missing parentheses?

When you start the proof below, Lean displays the target as `⊢ x + y + z = z + (y + x)`.
What happened to the parentheses on the left-hand side? Lean treats addition as
'left associative'. This is a fancy way of saying that `x + y + z` should always be
interpreted as `(x + y) + z`.
-/

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. Then `(x + y) + z = z + (y + x)`.
-/
theorem add_comm_left_right : (x + y) + z = z + (y + x) :=
begin [pure_maths]
  rw add_comm,
  rw add_comm x y,
  refl,
end

end exlean -- hide

/-
## Translation to a hand-written proof

Here's a suggestion. When writing a proof by hand, you need not (and should not) aim at a direct
translation of a Lean proof. Here, I've kept the main idea of each line of my Lean proof while
translating for ease of human understanding.

> Rewriting by additive commutativity, the goal is to prove `z + (x + y) = z + (y + x)`.
> Rewriting with additive commutativity on `x + y`, the goal is to prove `z + (y + x) = z + (y + x)`.
> This follows by reflexivity.
-/

