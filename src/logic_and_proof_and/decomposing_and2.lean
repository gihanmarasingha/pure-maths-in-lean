import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 5: Further 'and' decomposition

### Nested and

**Theorem**: Let $p$, $q$m and $r$ be propositions. Suppose $h : (p \land q) \land r$. Then $q$ follows.

**Proof**: Decomposing $h$ gives $h_{pq} : p \land q$ and $h_r : r$.
Decomposing $h_{pq}$ gives $h_p : p$ and $h_

The same proof can be written in Lean.
-/

example (p q r : Prop) (h : (p ∧ q) ∧ r) : q :=
begin
  cases h with hpq hr,
  cases hpq with hp hq,
  from hq,
end

/-
As before, note that the hypothesis names have no significance.
-/

example (p q r : Prop) (h : (p ∧ q) ∧ r) : q :=
begin
  cases h with h₁ h₂,
  cases h₁ with h₃ h₄,
  from h₄,
end

namespace exlean -- hide

/-
### Task

1. Replace `sorry` below with a Lean proof, adapting the proof of the example above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h : p \land (q \land r)$. Then $r$ follows.
-/
theorem decomposing_nested_and (h : p ∧ (q ∧ r)) : r :=
begin
  cases h with hp hqr,
  cases hqr with hq hr,
  from hr, 



end

end exlean -- hide