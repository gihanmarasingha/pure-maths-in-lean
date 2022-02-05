import tactic.linarith divisibility.mul_dvd_mul -- hide

/-
#  Divisibility

## Level 5: Divisibility of linear combinations
-/

namespace exlean --hide

/-
Here are some of the properties of the divisibility relation that you've seen so far:

* [Definition] `a ∣ b` means `∃ (m : ℤ), b = a * m`.

* [Reflexivity] `dvd_refl : a ∣ a`.

* `dvd_add` given `h₁ : a ∣ b` and `h₂ : a ∣ c`, we have `a ∣ b + c`.

* `dvd_mul_of_dvd_left` given `h : a ∣ b`, we have `a ∣ b * c`, for any `c : ℤ`.

-/


/-
### Tasks
* By applying some of the results above, prove that if `a ∣ b` and `a ∣ c`, then `a` divides any
linear combination of `b` and `c`. That is, `a ∣ b * s + c * t`, for all integers `s` and `t`. 

* Write the same proof by hand.
-/

/- Hint : Writing a backward proof
If you were writing this proof by hand, you might start by saying that is suffices (by `dvd_add`)
to prove `a ∣ b * s` and `a ∣ c * t`. To do this in Lean, type `apply dvd_add`.
-/

variables {a b c s t : ℤ} -- hide

/- Theorem :
Given `h₁ : a ∣ b` and `h₂ : a ∣ c`, we have `a ∣ b * s + c * t`, for all integers `s` and `t`.
-/
theorem dvd_mul_add_mul (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b * s + c * t :=
begin
  apply dvd_add,
  { apply dvd_mul_of_dvd_left h₁, },
  { apply dvd_mul_of_dvd_left h₂, },






end

end exlean -- hide