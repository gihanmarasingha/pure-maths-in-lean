import data.int.basic -- hide

/-
# Logic and Proof (Or)

## Level 3: Backward or introduction
-/


/-
For a more succinct proof, we can skip the intermediate derivation of $(a=b) \lor (a=7)$.

**Proof**: The result follows by right or introduction applied to the result of
left or introduction on $h$.

This proof is shorter, but less readable. Here it is in Lean.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  from or.inr (or.inl h)
end


/-
### Backwards or introduction

A 'backwards proof' of the above result avoids the introduction of additional hypotheses while
remaining readable.

**Proof**: It suffices, by right or introduction, to prove $(a = b)\lor (a = 7)$.
This follows from left or introduction on $h$.

Recall right or introduction takes $h : q$ and gives a proof of $p \lor q$. When we use 
right or introduction backward, we replace the goal of proving $p \lor q$ with the goal of
proving $q$ (in the same context as the original goal).

In this backward proof, we write 'it suffices to prove' to indicate that the old goal is being
replaced with a new goal. 
-/


/-
Immediately after typing `split,` in the proof above, Lean creates two new goals:
```
2 goals
x y : ℤ,
h₁ : x > 0,
h₂ : x + y = 5
⊢ x > 0

x y : ℤ,
h₁ : x > 0,
h₂ : x + y = 5
⊢ x + y = 5
```

The _context_ of both goals (the list of hypotheses) is identical. The only difference is
the target. The line `from h₁,` closes the first goal, leaving only one goal.
```
1 goal
x y : ℤ,
h₁ : x > 0,
h₂ : x + y = 5
⊢ x + y = 5
```
We close this final goal with `from h₂,`
-/

/- Tactic : split

The `split` tactic splits a 'compound' target into multiple goals. 

### Examples

`split` turns the target `⊢ p ∧ q` into two goals: (1) `⊢ p` and (2)  `⊢ q`.

Equally, if the target is `⊢ p ↔ q`, split creates the goals (1) to prove
`p → q` and (2) to prove `q → p`.
-/

/-
### The `show` tactic

Proofs with many goals (espeically nested goals) can become complicated. One way to make clear
what is being proved is to use the `show` tactic.

Here's a simple proof that `q` follows from the assumptions `h₁ : p` and `h₂ : q`.
-/

example (p q: Prop) (h₁ : p) (h₂ : q) : q :=
begin
  from h₂,
end

/-
Using the `show` tactic, we make clear that the line `from h₂` is a proof of `q`.
-/

example (p q: Prop) (h₁ : p) (h₂ : q) : q :=
begin
  show q, from h₂,
end

/-
More usefully, `show` can be used to clarify the target of the goals that arise after splitting
an 'and' target.
-/

example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) :
(x > 0) ∧ (x + y = 5) :=
begin
  split,
  show x > 0, from h₁,
  show x + y = 5, from h₂, 
end

/- Tactic : show
`show` is used to clarify what is being proved.

### Example
If the target is to prove `p ∧ q` and the hypothesis `h` is a proof of `p ∧ q`, then
`show p ∧ q, from h` indicates the target to Lean (and the human reader!) and closes the goal.
-/

namespace exlean -- hide

/-
### Task

1. Replace `sorry` below with a Lean proof, adapting the proof of the example above. Your proof
should use both the `split` and the `show` tactics.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h_1 : p$, $h_2 : q$, and $h_3 : r$. Then $r \land q$ 
follows.
-/
theorem split_and1 (h₁ : p) (h₂ : q) (h₃ : r) : r ∧ q :=
begin
  split,
  show r, from h₃,
  show q, from h₂,

end

end exlean -- hide