import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 6: Or elimination (again)
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

> Assume $H_2 : x = 2$. We must show $x ^ 2 + 6 = 5x$. Rewriting with $H_2$,
> $\vdash 2 ^ 2 + 6 = 5 \times 2$, which holds by numerical calculation.
 
We have $h_2 : (x = 3) \to x ^ 2 + 6 = 5x$:

> Assume $H_3 : x = 3$. We must show $x ^ 2 + 6 = 5x$. Rewriting with $H_3$,
> $\vdash 3 ^ 2 + 6 = 5 \times 3$, which holds by numerical calculation.

The result follows by or elimination on $h$, $h_1$, and $h_2$. ∎

### Or elimination in lean

The Lean or elimination theorem is called `or.elim`. For propositions, `p`, `q`, and `r`, if
`h : p ∨ q`, `h₁ : p → r`, and `h₂ : q → r`, then `or.elim h h₁ h₂` is a proof of `r`.

-/

/- Axiom: or.elim
  (h : p ∨ q) (h₁ : p → r) (h₂ : q → r) : r
-/

example (x : ℕ) (h : (x = 2) ∨ (x = 3)) : x ^ 2 + 6 = 5 * x :=
begin
  have h₁ : (x = 2) → (x ^ 2 + 6 = 5 * x),
  { assume H₂ : x = 2,
    show x ^ 2 + 6 = 5 * x,
    rw H₂,
    show 2 ^ 2 + 6 = 5 * 2, norm_num, },

  have h₂ : (x = 3) → (x ^ 2 + 6 = 5 * x),
  { assume H₃ : x = 3,
    show x ^ 2 + 6 = 5 * x,
    rw H₃,
    show 3 ^ 2 + 6 = 5 * 3, norm_num, },
  from or.elim h h₁ h₂,
end

/-
This forward proof is somewhat long-winded and requires introducing intermediate hypotheses.
An alternative approach is to have a mixed forward / backward proof using `apply or.elim`:
-/

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

/-
After typing `apply or.elim h` in the proof above, we are left with two goals, each an implication.
```
 2 goals
 x : ℕ,
 h : x = 2 ∨ x = 3
 ⊢ x = 2 → x ^ 2 + 6 = 5 * x
 
 x : ℕ,
 h : x = 2 ∨ x = 3
 ⊢ x = 3 → x ^ 2 + 6 = 5 * x
  ```

The approach shares features with the use of `cases` to decompose an `∨` statement.
-/


namespace exlean -- hide

/-

### Tasks

1. Replace `sorry` below with a Lean proof, using `cases` to decompose `h`
2. Delete your proof and write a proof using `apply or.elim h`.
3. Delete this proof and write a forward proof that else with `from or.elim h h₁ h₂`.
4. On a piece of paper, state and give handwritten proofs of this result.
-/

variables (p q : Prop)

/- Theorem : no-side-bar
Let $p$ and $q$. Suppose $h : p \lor q$. Then $q \lor p$ follows.
-/
theorem or_elim_example (h : p ∨ q) : q ∨ p :=
begin
/-   cases h with h₁ h₂,
  { from or.inr h₁, },
  { from or.inl h₂, }, -/
  apply or.elim h,
  { assume hp : p,
    from or.inr hp, },
  { assume hq : q,
    from or.inl hq, },




end

end exlean -- hide