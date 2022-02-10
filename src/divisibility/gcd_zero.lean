import tactic.linarith divisibility.gcd_uniqueness -- hide

/-
# Divisibility

## Level 13: Greatest common divisor of an integer and zero
-/

namespace exlean -- hide

open int -- hide



/- Hint : Starting the proof
Recall that `greatest_common_divisor d a b` is a conjunctive statement. Thus, you can
split the goal in two using the `split` tactic.
-/


/- Theorem :
`a` is a greatest common divisor of `a` and `0`, for every integer `a`.
-/
theorem greatest_common_divisor_zero (a : ℤ) :
greatest_common_divisor a a 0 :=
begin
  split,
  { split,
    { apply dvd_refl, },
    { apply dvd_zero, }, },
  { assume e : ℤ,
    assume h : common_divisor e a 0,
    cases h with hea he0,
    exact hea, },




    
end


end exlean -- hide