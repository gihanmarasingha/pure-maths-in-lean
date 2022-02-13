import data.int.basic -- hide

/-
# Logic and Proof (Or)

## Level 3: Backward or introduction
-/

/-
In the last level, we saw this rather terse proof.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  from or.inr (or.inl h)
end

/-
We also so a more readable version that requires the introduction of an additional hypothesis.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  have h₁ : (a = b) ∨ (a = 7), from or.inl h,
  show (a = 5) ∨ ((a = b) ∨ (a = 7)), from or.inr h₁,
end

/-
### Backward or introduction

A 'backward proof' of the above result avoids the introduction of additional hypotheses while
remaining readable.

**Proof**: It suffices, by right or introduction, to prove $(a = b)\lor (a = 7)$.
This follows from left or introduction on $h$. ∎

Recall right or introduction takes $h : q$ and gives a proof of $p \lor q$. When we use 
right or introduction backward, we replace the goal of proving $p \lor q$ with the goal of
proving $q$ (in the same context as the original goal).

In this backward proof, we write 'it suffices to prove' to indicate that the old goal is being
replaced with a new goal.
-/

/-
### Backward or introduction in Lean

If the target is `⊢ p ∨ q`, the tactic `right` replaces the goal with one of proving `q`.
Likewise, the tactic `left` replaces the goal with that of proving `p`.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  right,
  show (a = b) ∨ (a = 7), from or.inl h,
end

/-
We can prove the same theorem entirely through backward applications of or introduction.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  right,
  show (a = b) ∨ (a = 7),
  left,
  show a = b, from h,
end

/- Tactic : left
`left` changes a goal of proving `p ∨ q` into a goal of proving `p`.
-/

/- Tactic : right
`right` changes a goal of proving `p ∨ q` into a goal or proving `q`.
-/

namespace exlean -- hide

/-
### Task

1. Replace `sorry` below with a backward Lean proof via the `left` and `right` tactics. Make your
proof more readable by using the `show` tactic each time the goal changes.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) Write a one-line proof that uses only `from` and forward or introduction.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h : q$. Then $(p \lor (q \lor r)) \lor p$
follows.
-/
theorem nested_or1 (h : q) : (p ∨ (q ∨ r)) ∨ p :=
begin
  left,
  show p ∨ (q ∨ r),
  right,
  show q ∨ r,
  left,
  from h,





end

end exlean -- hide