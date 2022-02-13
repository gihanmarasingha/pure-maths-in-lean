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
We'll soon discuss the the new tactics `rw` and `norm_num`.
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
goals.
-/

/- Tactic : rw
If `h` is an equation of the form `p = q`, `rw h` rewrites replaces `p` in the target with `q`.

If `k` is in the context, `rw h at k` performs the rewrite at `k` instead of at the target.

`rw ←h` will rewrite backward: every occurrence of `q` is replaced with `p`. Type `\l` to produce `←`.

`rw [h1, h2, h3]` rewrites with multiple hypotheses (you aren't limited to three)!
-/

/- Tactic : norm_num

The `norm_num` tactic proves numerical goals. For example, it will close the goal
`⊢ 10 * 3 + 5 = 37 - 7`
-/

/-
If you were to write the proof 'by hand', you might write the following:

> By definition, it suffices to show there exists an integer `m` such that `10 = 5 * m`.
> Take `2` for `m`. Then we must show `10 = 5 * 2`.
> This is true by arithmetic.
-/

namespace exlean -- hide


/-

### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Hint: Starting the proof
As in the example, you can use `cases h with h₁ h₂` to decompose the 'or' statement `h`.
At later steps, you'll need to use the `rw` and `norm_num` tactics.
-/

/- Hint: Dealing with 'and'
If you followed the hint above, in the second goal, you'll have an 'and' hypothesis
`h₂ : (x = 3) ∧ (x > 0)` in the second goal. You can decompose this hypothesis using something like
`cases h₂ with h₃ h₄`. Here, `h₃ : x = 3` and `h₄ : x > 0`.
-/

variable (x : ℕ)

/- Theorem : no-side-bar
Let $x$ be a natural number. Suppose
$h : (x = 1) \lor ((x= 3) \land (x > 0))$, then $x ^2 + 3 = 4 x$.
-/
theorem or_elim_cases (h : (x = 1) ∨ ((x = 3) ∧ (x > 0))) :
x ^ 2 + 3 = 4 * x :=
begin
  cases h with h₁ h₂,
  { rw h₁,
    show 1 ^ 2 + 3 = 4 * 1, norm_num, },
  { cases h₂ with h₃ h₄,
    rw h₃,
    show 3 ^ 2 + 3 = 4 * 3, norm_num, },





end


end exlean -- hide