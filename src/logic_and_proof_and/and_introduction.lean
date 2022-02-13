import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 8: And introduction

### An introduction principle

The `split` tactic is useful when each of the constituents of a compound target are complicated.
Via split, we create two new goals and work on each goal separately.

An alternative approach to proving a statement of the form `p ∧ q` is to use the 'and introduction'
principle. This principle combines a proof of `p` with a proof of `q` to give a proof of `p ∧ q`.

**Theorem**: Let $x$ and $y$ be integers. Suppose $h_1 : x > 0$ and $h_2 : x + y = 5$. Then
$(x > 0) \land (x + y = 5)$.

**Proof**: The result follows by and introduction on $h_1$ and $h_2$.
-/

/-
In Lean, if `h₁ : p` and `h₂ : q` then `and.intro h₁ h₂` is a proof of `p ∧ q`.
-/

example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) : (x > 0) ∧ (x + y = 5) :=
begin
  from and.intro h₁ h₂,
end

namespace exlean -- hide

/-
### Tasks

1. Replace `sorry` below with a one-line Lean proof, adapting the proof of the example above. Your proof
should use `and.intro` and the `from` tactic.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h_1 : p$, $h_2 : q$, and $h_3 : r$. Then $r \land q$ 
follows.
-/
theorem and_intro1 (h₁ : p) (h₂ : q) (h₃ : r) : r ∧ q :=
begin
  from and.intro h₃ h₂,

end

end exlean -- hide