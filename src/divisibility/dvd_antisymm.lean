import tactic.linarith divisibility.dvd_trans  -- hide

/-
# Divisibility

## Level 5: Antisymmetry
-/

namespace exlean -- hide

open int -- hide

/-
The divisibility relation is antisymmetric.
That is, suppose `a` and `b` are non-negative integers such that `a ∣ b`, and `b ∣ a`, then `a = b`.
-/
variables {a b c d : ℤ} -- hide

example (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : a ∣ b) (h₄ : b ∣ a) : a = b :=
begin
  exact dvd_antisymm h₁ h₂ h₃ h₄,
end

/- Hint : Proving an `↔` statement.

Remember that the `split` tactic splits a target of `p ↔ q` into two goals: one to prove
`p → q` and one to prove `q → p`.
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
(∀ a : ℤ, b ∣ a ↔ c ∣ a) ↔ b = c :=
begin
  split,
  { intro h,
    apply dvd_antisymm h₁ h₂,
    { specialize h c,
      cases h with h₃ h₄,
      apply h₄,
      apply dvd_refl, },
    { specialize h b,
      cases h with h₃ h₄,
      apply h₃,
      apply dvd_refl, }, },
  { intro h,
    rw h,
    simp, },






end



end exlean -- hide