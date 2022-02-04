import tactic.linarith divisibility.divisibility_mul_dvd_mul  -- hide

/-
# Divisibility and Congruences

## Level XX: Greatest common divisors

-/

namespace exlean -- hide


/-
Let `m, n, and d` be integers. For `d` to be a _common divisor_ of `m` and `n` means that
`d ∣ m` and `d ∣ n`.
-/

def common_divisor (d m n : ℤ) := (d ∣ m) ∧ (d ∣ n)

/-
Using the above definition, we'll show that `5` is a commond divisor of `20` and `30`.
-/
example : common_divisor 5 20 30 :=
begin
  split, -- We'll show 1) `5 ∣ 20` and 2) `5 ∣ 30`.
  { use 4, -- 1) `⊢ 5 ∣ 20`, it suffices to show `20 = 5 * 4`.
    norm_num, }, -- This holds by arithmetic.
  { use 6,      -- 2) `⊢ 30 = 5 * 6`, it suffices to show `⊢ 30 = 5 * 6`.
    norm_num, }, -- This holds by arithmetic.
end


/-
With notation as above, for `d` to be a _greatest common divisor_ of `m` and `n` means that
* `d` is a common divisor of `m` and `n` and
* if `e` is a common divisor of `m` and `n`, then `e ∣ d`.
-/

def greatest_common_divisor (d m n : ℤ) := (common_divisor d m n) ∧ 
  (∀ (e : ℤ), common_divisor e m n → e ∣ d)

/-
We'll show that a greatest common divisor (if it exists) is unique.
-/

lemma uniqueness_of_greatest_common_divisor (d e m n : ℤ) (k₁ : 0 ≤ d) (k₂ : 0 ≤ e)
(h₁ : greatest_common_divisor d m n ) (h₂ : greatest_common_divisor e m n) : d = e :=
begin
  have h₃ : d ∣ e,
  { exact h₂.right d h₁.left, },
  have h₄ : e ∣ d,
  { exact h₁.right e h₂.left, },
  apply int.dvd_antisymm k₁ k₂ h₃ h₄,
end


end exlean -- hide