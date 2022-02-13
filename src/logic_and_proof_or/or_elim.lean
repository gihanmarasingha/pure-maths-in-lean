import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 5: Or elimination (again)
-/

/-
### Or elimination

We'll restate the or elimination rule from a previous level.

Let $p$, $q$, and $r$ be propositions. Let $h : p \lor q$. Let $h_1$ be a proof that $p$ implies $r$.
Let $h_2$ be a proof that $q$ implies $r$.

The or elimination rule applied to $h$, $h_1$, and $h_2$ produces a proof of $r$.

### A forward or elimination proof


**Theorem**: Let $x$ be a natural number. Suppose $h : (x = 2) \lor (x = 3)$. Then
$x ^ 2 + 6 = 5x$.

**Proof**: We have $h_1 : (x = 2) \to x ^ 2 + 6 = 5x$:

> Assume $H : x = 2$. We must show $x ^ 2 + 6 = 5x$. Rewriting with $H$,
> $\vdash 2 ^ 2 + 6 = 5 \times 2$, which holds by numerical calculation.
 
We have $h_2 : (x = 3) \to x ^ 2 + 6 = 5x$:

> Assume $H : x = 3$. We must show $x ^ 2 + 6 = 5x$. Rewriting with $H$,
> $\vdash 3 ^ 2 + 6 = 5 \times 3$, which holds by numerical calculation.

The result follows by or elimination on $h$, $h_1$, and $h_2$. ∎

### Or elimination in lean

The Lean or elimination theorem is called `or.elim`. For propositions, `p`, `q`, and `r`, if
`h : p ∨ q`, `h₁ : p → r`, and `h₂ : q → r`, then `or.elim h h₁ h₂` is a proof of `r`.

-/

example (x : ℕ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 + 6 = 5 * x :=
begin
  have h₁ : (x = 2) → (x ^ 2 + 6 = 5 * x),
  { assume H : x = 2,
    show x ^ 2 + 6 = 5 * x,
    rw H,
    show 2 ^ 2 + 6 = 5 * 2, norm_num, },

  have h₂ : (x = 3) → (x ^ 2 + 6 = 5 * x),
  { assume H : x = 3,
    show x ^ 2 + 6 = 5 * x,
    rw H,
    show 3 ^ 2 + 6 = 5 * 3, norm_num, },
  from or.elim h h₁ h₂,
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

example (x : ℤ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 - 5 * x + 6 = 0 :=
begin
  apply or.elim h,
  { assume h₁ : x = 2,
    rw h₁, refl, },
  { assume h₂ : x = 3,
    rw h₂, refl, },
end


/- Comment:
example (x : ℕ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 + 6 = 5 * x :=
begin
  apply or.elim h,
  { assume h₁ : x = 2,
    rw h₁,
    show 2 ^ 2 + 6 = 5 * 2, refl, }, 
  { assume h₂ : x = 3,
    rw h₂,
    show 3 ^ 2 + 6 = 5 * 3,
    refl, }, -- The case h₂ : x = 3
end


example (x : ℕ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 + 6 = 5 * x :=
begin
  cases h with h₁ h₂,
  { rw h₁,
    show 2 ^ 2 + 6 = 5 * 2, refl, }, -- The case h₁ : x = 2
  { rw h₂, refl, }, -- The case h₂ : x = 3
end
 -/

namespace exlean -- hide

/-

### Tasks

1. Replace `sorry` below with a backward Lean proof via the `left` and `right` tactics. Make your
proof more readable by using the `show` tactic each time the goal changes.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) Write a one-line proof that uses only `from` and forward or introduction.
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