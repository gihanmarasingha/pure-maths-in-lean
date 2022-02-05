import tactic.linarith divisibility.dvd_mul_of_dvd_left -- hide

/-
#  Divisibility

## Level 4: A second multiplication lemma
-/

namespace exlean --hide


variables {a b c d : ℤ} -- hide

/-
### Tasks
* Adapting the Lean proof of `dvd_add` from a previous level, show that if `h₁ : a ∣ b` and `h₂ : c ∣ d`, then
`a * c ∣ b * d`.

* Write the same proof by hand.
-/

/-
### Typing subscripts

In Lean, type `h₁` as `h\1`.
-/

/- Theorem :
Let `a, b, c, d` be integers. Given `h₁ : a ∣ b` and `h₂ : c ∣ d`, we have `a * c ∣ b * d`.
-/
theorem mul_dvd_mul (h₁ : a ∣ b) (h₂ : c ∣ d) : a * c ∣ b * d :=
begin
  cases h₁ with m₁ h₁,
  cases h₂ with m₂ h₂,
  rw dvd_def,
  use (m₁ * m₂),
  rw [h₁, h₂],
  ring,




end

end exlean -- hide