import tactic -- hide

/-
# Variables

## Level 3: Proving 'there exists' statements
-/

/-
### There exist statements

In this level, you'll see how to prove 'there exists' statements. A 'there exists' statement
asserts that there exists $x$ for which a property, depending on $x$, holds.

To prove a 'there exists' statement is to provide (1) a particular value $m$ and (2) a proof that
the property holds for $m$.

Here is an example.

**Theorem**: There exists a natural number $x$ such that $x ^ 2 + x = 6$,

**Proof**: Take $2$ for $x$. We must show $2 ^ 2 + 2 = 6$. This holds by numerical
calculation. ∎

We use the notation $\exists$ for 'there exists. With this notation, the statement of the above
theorem is $\exists (x : \mathbb N), x ^ 2 + x = 6$.

Lean uses the notation `∃` for 'there exists'. The symbol `∃` is typed `\ex`.
Below, we use the tactic `use` in the proof of the 'there exists' statement. The effect of
`use 2` is to replace the goal `∃ (x : ℕ), x ^ 2 + x = 6` with the goal of proving `2 ^ 2 + 2 = 6`.
-/

example : ∃ (x : ℕ), x ^ 2 + x = 6 :=
begin
  use 2,
  show 2 ^ 2 + 2 = 6, norm_num,
end

/- Tactic : use
If the goal is `⊢ ∃ (x : α), P x` and if `y : α`, then `use y` changes the goal to
`⊢ P y`.

### Example
With a goal `⊢ ∃ (x : ℤ), x + 5 = 23`, typing `use 18` changes the goal to `⊢ 18 + 5 = 23`.
-/


/-

### Tasks

1. Replace `sorry` below with a Lean proof.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Hint: Starting the proof
Begin with `assume y : ℤ`. This changes the goal to one of showing `f(y + 1) = f(y) ∨ f(y) = 0`.
-/

namespace exlean


/- Theorem : no-side-bar
There exists a natural number $x$ such that $2x^2 + 5x - 30 = 22$.
-/
theorem use_1 : ∃ (x : ℕ), 2 * x ^ 2 + 5 * x - 30 = 22 :=
begin
  use 4,
  show 2 * 4 ^ 2 + 5 * 4 - 30 = 22,
  norm_num,




end


end exlean -- hide