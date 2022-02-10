import tactic.linarith divisibility.mul_dvd_mul -- hide

/-
#  Divisibility

## Level 7: Divisibility of linear combinations
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

/-
If you were writing this proof by hand, you might start by saying that it suffices (by `dvd_add`)
to prove `a ∣ b * s` and `a ∣ c * t`. To do this in Lean, type `apply dvd_add`. Here's an
example of this kind of reasoning.
-/

variables {a b c d s t : ℤ} -- hide

example (h₁ : a ∣ b) (h₂ : a ∣ c) (h₃ : a ∣ d) : a ∣ (b + c) + d :=
begin
  apply dvd_add, -- 2 goals `⊢ a ∣ b + c` and `⊢ a ∣ d`
  { -- 1) `⊢ a ∣ b + c` 
    apply dvd_add, -- 2 goals `⊢ a ∣ b` and `⊢ a ∣ c`
    { -- 1.1) `⊢ a ∣ b`
      exact h₁, }, -- This follows from `h₁`.
    { -- 1.2) `⊢ a ∣ c`
      exact h₂, }, }, -- This follows from `h₂`.
  { -- 2) `⊢ a ∣ d`.
    exact h₃, }, -- This follows from `h₃`.
end

/- Tactic : apply
Most theorems have conditions under which they hold. For example, `dvd_add` states that
`a ∣ b + c` given the conditions `a ∣ b` and `a ∣ c`. If the target is `⊢ a ∣ b + c`, then
typing `apply dvd_add` creates two new goals: (1) to prove `a ∣ b` and (2) to prove `a ∣ c`.

The use of `apply` can be shortened. If the hypotheses `h₁ : a ∣ b` and `h₂ : a ∣ c` are in the
context, then the target `a ∣ b + c` can be proved with `apply h₁ h₂`.
-/

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