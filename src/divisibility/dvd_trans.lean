import tactic.linarith divisibility.dvd_mul_add_mul-- hide

/-
#  Divisibility

## Level 8: Transtivity of divisibility
-/

namespace exlean --hide

variables {a b c : ℤ} -- hide

/- Theorem :
Let `a, b, c, d` be integers. Given `h₁ : a ∣ b` and `h₂ : c ∣ d`, we have `a * c ∣ b * d`.
-/
theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
begin
  cases h₁ with m₁ h₁,
  cases h₂ with m₂ h₂,
  rw dvd_def,
  use (m₁ * m₂),
  rw [h₂, h₁, mul_assoc],  




end

end exlean -- hide