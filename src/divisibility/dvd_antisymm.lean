import tactic.linarith divisibility.dvd_trans  -- hide

/-
# Divisibility

## Level 9: Antisymmetry
-/

namespace exlean -- hide

open int -- hide

/-
The divisibility relation is antisymmetric.
That is, suppose `a` and `b` are non-negative integers such that `a ∣ b`, and `b ∣ a`, then `a = b`.
-/
variables {a b c d : ℤ} -- hide

/- Axiom : dvd_antisymm (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : a ∣ b) (h₄ : b ∣ a) :
a = b
-/
theorem dvd_antisymm (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=  -- hide
dvd_antisymm H1 H2                                                        -- hide


example (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : a ∣ b) (h₄ : b ∣ a) : a = b :=
begin
  exact dvd_antisymm h₁ h₂ h₃ h₄,
end

/-
In this level, we'll prove an if and only if (`↔`) statement. To split an `↔` statement into two
implications, use the `split` tactic.

In the example below, the initial goal is $\vdash a = 2b + c \iff c = a - 2b$. After using the
`split` tactic, we have two new goals: (1) $\vdash a = 2b + c \to c = a - 2b$ and 
(2) $\vdash c = a - 2b \to a = 2b + c$.
-/

example : a = 2 * b + c ↔ c = a - 2 * b :=
begin
  split, 
  { -- 1) `⊢ a = 2 * b + c → c = a - 2 * b`.
    assume h : a = 2 * b + c, -- `⊢ c = 2 * b - a`
    linarith, },
  { -- 2) `⊢ c = a - 2 * b → a = 2 * b + c`.
    assume h : c = a - 2 * b,
    linarith, },
end

/- Tactic : split

The `split` tactic splits a 'compound' target into multiple goals. 

For example, `split` turns the target `⊢ p ↔ q` into two goals: (1) to prove
`p → q` and (2)) to prove `q → p`.

Equally, if the target is `⊢ p ∧ q`, then `split` creates goals (1) `⊢ p` and (2) `⊢ q`.
-/

/- Hint : Specialzing a universally-quantified statement.

Suppose `P` is a predicate. Recall that if `h : ∀ (x : α), P(x)` and if `y : α`, then
`specialize h y` replaces `h` with `P(y)`.
-/

/- Hint : Decomposing a `↔` statement.

Suppose `h : p ↔ q`. Then the tactic `cases h with h₂ h₃` replaces `h` with `h₂ : p → q` and
`h₃ : q → p`.
-/


/- Theorem : no-side-bar
Given `d` is a common divisor of `a` and `b` and given `c ∣ d`, we have `c` is a common divisor of
`a` and `b`.
-/
lemma dvd_right_iff_eq (h₁ : 0 ≤ b) (h₂ : 0 ≤ c) :
(∀ (a : ℤ), b ∣ a ↔ c ∣ a) ↔ b = c :=
begin
  split,
  { assume h : ∀ (a : ℤ), b ∣ a ↔ c ∣ a,
    apply dvd_antisymm h₁ h₂,
    { specialize h c,
      cases h with h₃ h₄,
      apply h₄,
      apply dvd_refl, },
    { specialize h b,
      cases h with h₃ h₄,
      apply h₃,
      apply dvd_refl, }, },
  { assume h : b = c,
    assume a : ℤ,
    rw h,  },










end



end exlean -- hide