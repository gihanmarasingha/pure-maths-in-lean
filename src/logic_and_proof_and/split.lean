import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 7: Splitting an 'and' target

### Splitting a goal

To prove a target $\vdash (x > 0) \land (x + y = 5)$ is to prove both
$x > 0$ and $x + y = 5$. That is, the original goal is split into two new goals.

**Theorem**: Let $x$ and $y$ be integers. Suppose $h_1 : x > 0$ and $h_2 : x + y = 5$. Then
$(x > 0) \land (x + y = 5)$.

**Proof**: It suffices to prove (1) $x > 0$ and (2) $x + y = 5$.
1. The target $x > 0$ follows from $h_1$.
2. The target $x + y = 5$ follows from $h_2$. ∎
-/


/-
The Lean tactic `split` can be used to split an 'and' goal. In the proof below, the text following
each `--` is a _comment_. Lean ignores comments. Add comments to your Lean proofs to help explain
your proof to the reader.
-/

example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) : (x > 0) ∧ (x + y = 5) :=
begin
  split,
  from h₁,  -- Proof of x > 0
  from h₂,  -- Proof of x + y = 5
end


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

example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) : (x > 0) ∧ (x + y = 5) :=
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

/-
### Focussing with braces

Dealing with many goals at once can be confusing. Braces can be used to separate goals.
If you place your cursor within a brace, only the current goal is shown. It's good practice to
create a `sorry` proof for each new goal and fill in each `sorry` in turn.

```
example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) : (x > 0) ∧ (x + y = 5) :=
begin
  split,
  { sorry, },
  { sorry, },
end
```

Filling in each `sorry` above leads to the following proof.
-/

example (x y : ℤ) (h₁ : x > 0) (h₂ : x + y = 5) :
(x > 0) ∧ (x + y = 5) :=
begin
  split,
  { show x > 0, from h₁, },
  { show x + y = 5, from h₂, },
end


namespace exlean -- hide

/-
### Task

1. Complete the Lean proof below. Use `split`, `show`, and braces, as in the example above. Start
by writing `sorry` within each brace.
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
  { show r, from h₃, },
  { show q, from h₂, },

end

end exlean -- hide