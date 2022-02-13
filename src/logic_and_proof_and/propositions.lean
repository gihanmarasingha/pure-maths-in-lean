import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 4: Propositions

### Propositions

In previous levels, we saw that if $x$ is an integer and if $h : (x > 0) \land (x ^ 2 = 16)$,
then $x^2 = 16$ follows. One proof is first to decompose $h$ as $h_1 : x > 0$ and
$h_2 : x ^2 = 16$ and then to apply $h_2$.

Here's another example.

**Theorem**: Let $y$ be an integer. Supose $h : (y \ne 2) \land (10 y = 5)$. Then $10y = 5$.

**Proof**: Decomposing $h$ gives $h_1 : y \ne 2$ and $h_2 : 10y = 5$. The result follows from
$h_2$. ∎
-/

/-
Other than the details of the hypotheses, the proofs are identitcal. We can generalise both
arguments by using symbols in place of particular statements. These symbols are called
_propositional variables_.

Using propositional variables to stand for arbitrary propositions is similar to the use of
variables names (such as $x$) to stand for arbitrary numbers in high school algebra.

We now give a generalisation of the above proof.

**Theorem**: Let $p$ and $q$ be propositions. Suppose $h : p \land q$. Then $q$ follows.

**Proof**: Decomposing $h$ gives $h_1 : p$ and $h_2 : q$. The result follows from $h_2$. ∎

The same thing can be written in Lean.
-/

example (p q : Prop) (h : p ∧ q) : q :=
begin
  cases h with h₁ h₂,
  from h₂,
end

/-
The same theorem can be be proved via and elimination.

**Proof**: The result follows by right and elimination on $h$. ∎
-/

example (p q : Prop) (h : p ∧ q) : q :=
begin
  from h.right,
end

namespace exlean -- hide

/-
### Task

1. Replace `sorry` below with a proof using `cases`.
2. Delete your proof and write a one-line proof using and elimination.
2. On a piece of paper, state and give handwritten proofs of this result.
-/

/- Theorem : no-side-bar
Let $r$ and $s$ be propositions. Suppose $h : s \land r$. Then $s$ follows.
-/
theorem propositions (r s : Prop) (h : s ∧ r) : s :=
begin
  cases h with h₁ h₂,
  from h₁,


end

end exlean -- hide