import tactic.linarith divisibility.gcd_comm  -- hide

/-
# Divisibility

## Level 15: Division
-/

namespace exlean -- hide

open int -- hide

/-
The division lemma states that if `a` and `b` are integers with `b ≠ 0`, then there exist integers
`q` and `r` for which `a = b * q + r` and `0 ≤ r < |b|`.

The quantity `q` is called the quotient and `r` is called the remainder.
-/

variables (a b : ℤ) -- hide

lemma division (h : b ≠ 0) : ∃ (q r : ℤ), a = b * q + r ∧ (0 ≤ r ∧ r < abs b) :=     -- hide
⟨a/b, a % b, by rw [add_comm, mod_add_div a b], mod_nonneg a h, mod_lt a h⟩  -- hide

example (h : b ≠ 0) : ∃ (q r : ℤ), 700 = b * q + r ∧ (0 ≤ r ∧ r < abs b) :=
begin
  apply division 700 b h,
end

variables {q₁ r₁ q₂ r₂ : ℤ} -- hide

/-
In this (somewhat tricky) level, your task is to show uniquness of the quotient and remainder.
You may freely use the following lemma.
-/

lemma abs_sub_lt {x y c : ℤ} (h₁ : 0 ≤ x ∧ x < c) (h₂ : 0 ≤ y ∧ y < c) : abs (x - y) < c :=
begin
  rw abs_sub_lt_iff,
  split;
  linarith,
end

/-
Other useful results include:

* `abs_mul : abs (a * b) = (abs a) * (abs b)`
* `abs_nonneg : 0 ≤ abs a`
* `le_mul_of_one_le_right : 0 ≤ b → 1 ≤ a → b ≤ b * a`.
-/

/- Hint : Proof by cases
At some point in your proof, you'll need to consider separately the cases `q₁ = q₂` and `q₁ ≠ q₂`.
You can do this with `by_cases h : q₁ = q₂` (replacing `h` with whatever name you like).
-/


/- Theorem :
Let $a, b$ be integers with $b ≠ 0$. If $a = b q_1 + r_1 = b q_2  + r_2$, where
$0 \le r_1 < |b|$ and $0 \le r_2 < |b|$, then $q_1 = q_2$ and $r_1 = r_2$.
-/
lemma division_unique (h : b ≠ 0)
(h₁ : a = b * q₁ + r₁ ∧ (0 ≤ r₁ ∧ r₁ < abs b)) 
(h₂ : a = b * q₂ + r₂ ∧ (0 ≤ r₂ ∧ r₂ < abs b)) : q₁ = q₂ ∧ r₁ = r₂ :=
begin
  cases h₁ with hx₁ hx₂,
  cases h₂ with hy₁ hy₂,
  rw hx₁ at hy₁,
  have h₄ : r₁ - r₂ = b * (q₂ - q₁), linarith,
  by_cases h₅ : q₁ = q₂,
  { split,
    { exact h₅, },
    { rw [h₅.symm, show q₁ - q₁ = 0, by linarith, mul_zero] at h₄,
      linarith, }, },
  { exfalso,
    have p₁ : abs (r₁ - r₂) = abs b * abs (q₂ - q₁), rw [h₄, abs_mul],
    have p₂ : 0 < abs (q₂ - q₁),
    { rw abs_pos,
      intro p₃,
      apply h₅,
      linarith, },
    have p₃ : abs b ≤ abs (r₁ - r₂),
    { rw p₁, 
      exact le_mul_of_one_le_right (abs_nonneg _) p₂, },
    have p₄ := abs_sub_lt hx₂ hy₂,
    linarith, },










    
end


end exlean -- hide