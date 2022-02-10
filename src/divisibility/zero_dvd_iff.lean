import tactic.linarith divisibility.dvd_mul_of_dvd_left -- hide

/-
#  Divisibility

## Level 5: Numbers divisible by zero
-/

namespace exlean --hide

/-
Which numbers are divisible by zero? You'll prove that a number is divisible by zero if and only 
if that number is itself zero.
-/


/-
### Tasks
* By applying some of the results above, prove that if `a ∣ b` and `a ∣ c`, then `a` divides any
linear combination of `b` and `c`. That is, `a ∣ b * s + c * t`, for all integers `s` and `t`. 

* Write the same proof by hand.
-/

/-
If you were writing this proof by hand, you might start by saying that it suffices (by `dvd_add`)
to prove `a ∣ b * s` and `a ∣ c * t`. To do this in Lean, type `apply dvd_add`. Here's an
example of this kind of reasoning.
-/

variables {a : ℤ} -- hide

lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { assume h : 0 ∣ a,
    cases h with m h,
    linarith, },
  { assume h : a = 0,
    rw h, },
end

end exlean -- hide