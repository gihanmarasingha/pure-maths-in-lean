import tactic -- hide

/-
# Variables

## Level 4: Exists introduction
-/

/-
### Exists introduction

In the last level, we saw backward proofs of 'there exist' statements. For example, in our
proof that there exists a natural number $x$ such that $x ^ 2 + x = 6$, we started by taking
$2$ for $x$. This left us with the goal of proving $2 ^ 2 + 2 = 6$.

The more fundamental principle is *exists introduction*: given (1) a term $m$ and (2) a proof
$h$ that $m$ satisfies some property, exists introduction produces a proof that there exists $x$
such that the property holds for $x$.

**Theorem**: There exists a natural number $x$ such that $x ^ 2 + x = 6$.

**Proof**: By numerical calculation, we have $h : 2 ^ 2 + x = 6$. The result follows from exists
introduction with $2$ and $h$. ∎
-/

/-
### Exists introduction in Lean

The exists introduction rule is called `exists.intro` in Lean.
-/

/- Axiom: exists.intro
  (m : α) (h : P m) : ∃ (x : α), P x
-/

example : ∃ (x : ℕ), x ^ 2 + x = 6 :=
begin
  have h : 2 ^ 2 + 2 = 6, norm_num,
  from exists.intro 2 h,
end

/-

### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof above. Use `exists.intro` instead of
`use`.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

namespace exlean -- hide

/- Theorem : no-side-bar
There exists a natural number $x$ such that $2x^2 + 5x - 30 = 22$.
-/
theorem exists_intro11 : ∃ (x : ℕ), 2 * x ^ 2 + 5 * x - 30 = 22 :=
begin
  have h : 2 * 4 ^ 2 + 5 * 4 - 30 = 22, norm_num,
  from exists.intro 4 h,




end


end exlean -- hide