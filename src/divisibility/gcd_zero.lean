import tactic.linarith divisibility.gcd_uniqueness -- hide

/-
# Divisibility

## Level 11: Greatest common divisor of an integer and zero
-/

namespace exlean -- hide

open int -- hide


/- Theorem :
`a` is a greatest common divisor of `a` and `0`, for every integer `a`.
-/
theorem greatest_common_divisor_zero (a : ℤ) :
greatest_common_divisor a a 0 :=
begin
  split,
  { split,
    { apply dvd_refl, },
    { use 0,
      linarith, }, },
  { intros e h,
    cases h with h₁ h₂,
    exact h₁, },





    
end


end exlean -- hide