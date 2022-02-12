import data.int.basic -- hide

/-
# Logic and Proof

## Level 2: Decomposing an 'and' hypothesis

### And statements

Let $p$ and $q$ be propositions (mathematical statements). The formal statement $p \land q$
corresponds to the informal statement '$p$ and $q$'.

Suppose you have given a hypothesis $h : p \land q$. Decomposing this hypothesis replaces $h$ with
two new hypotheses $h₁ : p$ and $h₂ : q$.

**Theorem**: Let $x$ be an integer. Supose $h : (x > 0) \land (x ^ 2 = 16)$. Then $x ^ 2 = 16$.

**Proof**: Decomposing $h$ gives $h_1 : x > 0$ and $h_2 : x ^2 = 16$. The result follows from $h_2$.
-/

/-
### Decomposing a hypothesis in Lean

In Lean, we use the `cases` tactic to decompose a compound hypothesis. In the example below, using
`cases h with h₁ h₂` decomposes the original hypothesis `h : x > 0 ∧ x ^ 2 = 16` into two
new hypotheses, `h₁ : x > 0` and `h₂ : x ^ 2 = 16`. The target, `⊢ x ^ 2 = 16` is proved using
hypothesis `h₂`.
-/

example (x : ℤ) (h : (x > 0) ∧ (x ^ 2 = 16)) : x ^ 2 = 16 :=
begin
  cases h with h₁ h₂,
  from h₂,
end

/- Tactic : cases
`cases` is a general-purpose elimination tactic. It it used to 'decompose' a hypothesis into
its constituent parts.

### Examples

* Given `h : ∃ (x : ℤ), x + 5 = y`, typing `cases h with m h₂` replaces `h` with `m : ℤ` and
`h₂ : m + 5 = y`.

* Given `h : p ∧ q`, typing `cases h with hp hq` replaces `h` with `hp : p` and `hq : q`.

* Given `h : p ∨ q`, typing `cases h with hp hq` replaces the current goal with two goals
(1) in which `h` is replaced with `hp : p` and (2) in which `h` is replaced with `hq : q`.

* Given `x : ℕ`, typing `cases x with k` replaces the goal with two new goals: (1) a goal in which
every occurence of `x` is replaced with `0` and (2) a goal with a new variable `k : ℕ` and in 
which every occurrence of `x` is replaced with `succ k`.
-/

/-
There is nothing special about the choice of hypothesis labels, as seen below.
-/

example (x : ℤ) (Bob : (x > 0) ∧ (x ^ 2 = 16)) : x ^ 2 = 16 :=
begin
  cases Bob with alice sameera,
  from sameera,
end

namespace exlean -- hide

/-
### Task

1. Replace `sorry` bewlow with a Lean proof, adapting the proof of the example above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Theorem : no-side-bar
Let $x$ and $y$ be integers. Suppose $h : (x + y = 3) \land (x < 0)$. Then $x + y = 3$.
-/
theorem decomposing_and1 (x y : ℤ) (h : x + y = 3 ∧ x < 0) :
x + y = 3 :=
begin
  cases h with h₁ h₂,
  from h₁,

end

end exlean -- hide