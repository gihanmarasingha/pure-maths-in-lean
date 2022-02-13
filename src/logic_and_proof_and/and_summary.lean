import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 10: And summary

### Elimination and introduction

In logic, the entire meaning of $\land$ is encapsulated by two principles.

1. And introduction. Given $h_1 : p$ and $h_2 : q$, and introduction on $h_1$ and $h_2$ gives a 
proof of $p \land q$.
2. And elimination. Given $h : p \land q$,
    * Left and elimination on `h` gives a proof of `p`.
    * Right and elimination on `h` gives a proof of `q`.


In Lean, the principles are as follows.

1. And introduction. Given `h₁ : p` and `h₂ : q`, `and.intro h₁ h₂` is a proof of `p ∧ q`.
2. And elimination. Given `h : p ∧ q`,
    * `h.left` or `and.elim_left h` gives a proof of `p`.
    * `h.right` or `and.elim_right h` gives a proof of `q`.

### `cases` and `split`, backward proof

Lean provides the mechanism `cases` for doing left and right and elimination simultaneously.
If `h : p ∧ q`, then `cases h with h₁ h₂` replaces `h` with two new hypotheses, `h₁ : p` and
`h₂ : q`.

The `split` tactic is used for 'backward' and introduction. If the target is `p ∧ q`, a forward
application of and introduction requires having proved first `h₁ : p` and `h₂ : q`. 
Via `split`, Lean creates two new goals, one for each of the conditions of and introduction.
-/

/-
### `from`, `have`, and `show`

* `from` is used to give a hypothesis or other proof term that closes the goal.
* `have` allows you to create an auxiliary goal. The result of the goal is added to the context.
* `show` is used to indicate what you're trying to prove.

### `apply` and mixed forward / backward proofs
The `apply` tactic permits writing mixed forward / backward proofs, depending on the number
of arguments given to the applied theorem.
-/

namespace exlean -- hide

/-
### Task

1. Prove the Lean result below. Try as many different proof methods as you can. Which method
do you like the best?
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) Give a one-line Lean proof of the result.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h : p \land (q \land r)$. Then $p \land q$ 
follows.
-/
theorem and_summary (h : p ∧ (q ∧ r)) : p ∧ q :=
begin
  cases h with hp hqr,
  cases hqr with hq hr,
  exact and.intro hp hq,








end

end exlean -- hide