import tactic.linarith divisibility.common_divisors  -- hide

/-
# Divisibility and Congruences

## Level 7: Common divisor results
-/

namespace exlean -- hide

/-
### Tasks

In this level, you'll *decompose* the hypothesis that `d` is a common divisor of `a` and `b` to
prove that `c` is a common divisor of `a` and `b`, under the hypothesis that `c ∣ d`.
-/

variables {d a b c : ℤ} -- hide

/- Theorem : no-side-bar
Given `d` is a common divisor of `a` and `b` and given `c ∣ d`, we have `c` is a common divisor of
`a` and `b`.
-/
theorem common_divisor_of_common_divisor_of_dvd (h₁ : common_divisor d a b) (h₂ : c ∣ d) : common_divisor c a b :=
begin
  cases h₂ with m₃ h₃,
  rw h₃ at h₁,
  rcases h₁ with ⟨⟨m₄, h₄⟩, ⟨m₅, h₅⟩⟩,
  split,
  { use m₃ * m₄,
    rw [h₄, mul_assoc], },
  { use m₃ * m₅,
    rw [h₅, mul_assoc], },

  






  
end


end exlean -- hide