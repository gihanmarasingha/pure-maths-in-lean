import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 3: Decomposing or statements
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

example (x : ℤ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 - 5 * x + 6 = 0 :=
begin
  apply or.elim h,
  { assume h₁ : x = 2,
    rw h₁, refl, },
  { assume h₂ : x = 3,
    rw h₂, refl, },
end

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


namespace exlean -- hide

/-
# ADD MORE STUFF HERE

### Task

1. Replace `sorry` below with a backward Lean proof via the `left` and `right` tactics. Make your
proof more readable by using the `show` tactic each time the goal changes.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) Write a one-line proof that uses only `from` and forward or introduction.
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h : q$. Then $(p \lor (q \lor r)) \lor p$
follows.
-/
theorem nested_or1 (h : q) : (p ∨ (q ∨ r)) ∨ p :=
begin
  left,
  show p ∨ (q ∨ r),
  right,
  show q ∨ r,
  left,
  from h,





end

end exlean -- hide