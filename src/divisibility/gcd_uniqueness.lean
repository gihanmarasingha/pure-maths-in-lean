import tactic.linarith divisibility.common_divisors2  -- hide

/-
# Divisibility

## Level 12: Greatest common divisors
-/

namespace exlean -- hide

open int -- hide

/-
Recall that for `d` to be a common divisor of `a` and `b` means that `d ∣ a` and `d ∣ b`.

For `d` to be a _greatest common divisor_ of `m` and `n` means that
* `d` is a common divisor of `m` and `n` and
* if `e` is a common divisor of `m` and `n`, then `e ∣ d`.
-/

def greatest_common_divisor (d m n : ℤ) := (common_divisor d m n) ∧ 
  (∀ (e : ℤ), common_divisor e m n → e ∣ d)

/-
### Task

Show that if the non-negative integers `d` and `e` are both greatest common divisors of `m` and `n`,
then `d = e`.
-/

variables {d e m n : ℤ} -- hide

/- Hint : Proving an equality
Recall that `apply dvd_antisymm k₁ k₂,` will reduce the goal to two goals (1) `⊢ d ∣ e` and
(2) `⊢ e ∣ d`.
-/

/- Theorem :
If the non-negative integers `d` and `e` are both greatest common divisors of `m` and `n`,
then `d = e`.
-/
theorem uniqueness_of_greatest_common_divisor (k₁ : 0 ≤ d) (k₂ : 0 ≤ e)
(h₁ : greatest_common_divisor d m n )
(h₂ : greatest_common_divisor e m n) : d = e :=
begin
  cases h₁ with hdcomm hdgreat,
  cases h₂ with hecomm hegreat,
  apply dvd_antisymm k₁ k₂,
  { specialize hegreat d,
    apply hegreat hdcomm, },
  { specialize hdgreat e,
    apply hdgreat hecomm, },












end


end exlean -- hide