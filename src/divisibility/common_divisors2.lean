import tactic.linarith divisibility.common_divisors  -- hide

/-
# Divisibility and Congruences

## Level 4: Common divisor results
-/

namespace exlean -- hide

/-
### Tasks

* Adapt the Lean proof above to show that `4` is a common divisor of `48` and `60`.

* Give a handwritten proof of the same result.

-/

variables {d a b c : ℤ}


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