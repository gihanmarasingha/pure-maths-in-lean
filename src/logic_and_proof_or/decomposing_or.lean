import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 4: Decomposing or statements
-/



/-
Let $x$ be a natural number (a non-negative integer). Suppose you are given the hypothesis
$h : (x = 2) \lor (x = 3)$. What can you prove?

You know *either* that $x = 2$ *or* you know $x = 3$ but you don't know which one holds.
Let's label the two possibilities. Either $h_1 : x = 2$ or $h_2 : x = 3$.

* On the assumption $h_1 : x = 2$, you know $x ^ 2 + 6 = 2 ^ 2 + 6 = 10 = 5x$.
* On the assumption $h_2 : x = 3$, you know $x ^ 2 + 6 = 3 ^ 2 + 6 = 5x$.

In either case, you deduced $x ^ 2 + 6 = 5x$. Thus, it seems logical to say that
$x ^ 2 + 6 = 5x$ follows from the original assumption $h : (x = 2) \lor (x = 3)$.
-/

/-
### Or elimination

Let $p$, $q$, and $r$ be propositions. Let $h : p \lor q$. The or elimination rule applied to $h$
states that if (1) $r$ can be deduced from the assumption of $p$ and (2) if $r$ can be deduced from
the assumption of $q$, then $r$ follows.

### The `cases` tactic for decomposing an or statement

In Lean, one way to decompose an or statement is to use the `cases` tactic, as in the example below.
For the moment, you can ignore the the new tactics `rw` and `norm_num`.
-/

example (x : ℕ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 + 6 = 5 * x :=
begin
  cases h with h₁ h₂,
  { rw h₁,                            -- The case h₁ : x = 2.
    show 2 ^ 2 + 6 = 5 * 2, norm_num, }, 
  { rw h₂,                            -- The case h₂ : x = 3.
    show 3 ^ 2 + 6 = 5 * 3, norm_num, },
end

/-
In the proof above, we start with two hypotheses, `x : ℕ` and `h : (x = 2) ∨ (x = 3)`.
The target is `⊢ x ^ 2 + 6 = 5 * x`.

The effect of `cases h with h₁ h₂` here is to create two new goals. In the first goal, the original 
'or' hypothesis `h` is replaced with its left side, `h₁ : x = 2`. IN the second goal, `h` is
replaced with its right side, `h₂ : x = 3`.
```
 2 goals
 case or.inl
 x : ℤ,
 h₁ : x = 2
 ⊢ x ^ 2 - 5 * x + 6 = 0
 
 case or.inr
 x : ℤ,
 h₂ : x = 3
 ⊢ x ^ 2 - 5 * x + 6 = 0

 ```

When we prove the first goal, we use the rewrite tactic, `rw` in the form `rw h₁` to replace
`x` in the target with `2`. This leaves the goal of proving `2 ^ 2 + 6 = 5 * 2`.
We close this goal with the Lean tactic `norm_num`, suitable for proving various numerical
calculations.
-/

namespace exlean -- hide

/-

### Tasks

1. Replace `sorry` below with a Lean proof. Use the `cases` tactic to decompose the or statement `h`.
proof more readable by using the `show` tactic each time the goal changes.
2. On a piece of paper, state and give a handwritten proof of this result.

-/

variables (p q : Prop)

/- Theorem : no-side-bar
Let $p$ and $q$. Suppose $h : p \lor q$. Then $q \lor p$ follows.
-/
theorem or_elim_cases (h : p ∨ q) : q ∨ p :=
begin
  cases h with h₁ h₂,
  { from or.inr h₁, },
  { from or.inl h₂, },





end

end exlean -- hide