import tactic.linarith divisibility.gcd_uniqueness -- hide

/-
# Divisibility

## Level 11: Greatest common divisor of zero and an integer
-/

namespace exlean -- hide

open int -- hide


/- Theorem :
`a` is a greatest common divisor of `0` and `a`, for every integer `a`.
-/
theorem greatest_common_divisor_zero (a : ℤ) :
greatest_common_divisor a 0 a :=
begin
  split,
  { split,
    { use 0,
      linarith, },
    { apply dvd_refl, },  },
  { intros e h,
    cases h with h₁ h₂,
    exact h₂, },





    
end


end exlean -- hide