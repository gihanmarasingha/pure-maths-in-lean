import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 6: New hypotheses with `have`

### The `have` tactic

In a long proof, it can help to introduce new hypotheses into the context for later use.
The next example isn't long, but illustrates the concept.

**Theorem**: Let $p$ and $q$ be propositions. Suppose $h : p \land q$. Then $q$ follows.

**Proof**: We have $h_2 : q$ by right and elimination on $h$. The result follows from $h_2$. ∎
-/

/-
In Lean, we accomplish this using the `have` tactic.
-/

example (p q : Prop) (h : p ∧ q) : q :=
begin
  have h₂ : q, from h.right,
  from h₂,
end

/-
Equally, we could replace `h.right` with `and.elim_right h`.
-/

/-
For a more sophisticated example, we'll take a hypothesis that involves nesting `∧`s.
-/

example (p r q : Prop) (h : (p ∧ q) ∧ r) : q :=
begin
  have h₁ : p ∧ q, from h.left,
  from h₁.right,
end


/-
Immediately after typing `have h₁ : p ∧ q,` in the proof above, Lean would present you with 
two new goals:

```
2 goals
p r q : Prop,
h : (p ∧ q) ∧ r
⊢ p ∧ q

p r q : Prop,
h : (p ∧ q) ∧ r,
h₁ : p ∧ q
⊢ q
```


The first of these is the goal introduced by the `have` tactic, namely that of proving `p ∧ q`
in the original context. The Lean code `from h.left,` closes this goal.

The second goal is that of proving the original target, `q` in a context that includes the
result to be proved by the `have` tactic.
-/

/- Tactic : have
`have` is used to introduce a new hypothesis into the context. It opens a new goal for the proof
of the hypothesis.

### Example
`have h2 : x + y = y + x` introduces a new goal, to prove
`x + y = y + x` while adding the hypothesis `h2 : x + y = y + x` to the context of the old goal.
-/

namespace exlean -- hide

/-
### Task

1. Replace `sorry` below with a Lean proof, adapting the proof of the example above. Remember that
`∧` is typed `\and`.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) you should be able to write a one-line proof of this result, using only the `from`
tactic and elimination rules. Try this!
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h : p \land (q \land r)$. Then $q$ follows.
-/
theorem have_nested_and (h : p ∧ (q ∧ r)) : q :=
begin
  have h₁ : q ∧ r, from h.right,
  from h₁.left,


end

end exlean -- hide