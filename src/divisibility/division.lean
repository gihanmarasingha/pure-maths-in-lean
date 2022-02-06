import tactic.linarith divisibility.gcd_comm  -- hide

/-
# Divisibility

## Level 13: Division
-/

namespace exlean -- hide

open int -- hide

/-
The division lemma states that if `a` and `b` are integers with `b ≠ 0`, then there exist integers
`q` and `r` for which `a = q * b + r` and `0 ≤ r < |b|`.

The quantity `q` is called the quotient and `r` is called the remainder.
-/

variables (a b : ℤ) -- hide

lemma division (h : b ≠ 0) : ∃ (q r : ℤ), a = q * b + r ∧ (0 ≤ r ∧ r < abs b) :=     -- hide
⟨a/b, a % b, by rw [add_comm, mul_comm, mod_add_div a b], mod_nonneg a h, mod_lt a h⟩  -- hide

example (h : b ≠ 0) : ∃ (q r : ℤ), 700 = q * b + r ∧ (0 ≤ r ∧ r < abs b) :=
begin
  apply division 700 b h,
end

variables {q₁ r₁ q₂ r₂ : ℤ} -- help

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
* `le_mul_of_one_le_left : 0 ≤ b → 1 ≤ a → b ≤ a * b`.
-/

/- Hint : Proof by cases
At some point in your proof, you'll need to consider separately the cases `q₂ = q₁` and `q₂ ≠ q₁`.
You can do this with `by_cases h : q₂ = q₁` (replacing `h` with whatever name you like).
-/


/- Theorem :
Let $a, b$ be integers with $b ≠ 0$. If $a = q_1 * b + r_1 = q_2 * b + r_2$, where
$0 \le r_1 < |b|$ and $0 \le r_2 < |b|$, then $q_1 = q_2$ and $r_1 = r_2$.
-/
lemma division_unique (h : b ≠ 0)
(h₁ : a = q₁ * b + r₁ ∧ (0 ≤ r₁ ∧ r₁ < abs b)) 
(h₂ : a = q₂ * b + r₂ ∧ (0 ≤ r₂ ∧ r₂ < abs b)) : q₁ = q₂ ∧ r₁ = r₂ :=
begin
  cases h₁ with hx₁ hx₂,
  cases h₂ with hy₁ hy₂,
  rw hx₁ at hy₁,
  have h₄ : r₁ - r₂ = (q₂ - q₁) * b , linarith,
  by_cases h₅ : q₂ = q₁,
  { split,
    { exact h₅.symm, },
    { rw [h₅, show q₁ - q₁ = 0, by linarith, zero_mul] at h₄,
      linarith, }, },
  { exfalso,
    have p₁ : abs (r₁ - r₂) = abs (q₂ - q₁) * abs b, rw [h₄, abs_mul],
    have p₂ : 0 < abs (q₂ - q₁),
    { rw abs_pos,
      intro p₃,
      apply h₅,
      linarith, },
    have p₃ : abs b ≤ abs (r₁ - r₂),
    { rw p₁, 
      exact le_mul_of_one_le_left (abs_nonneg _) p₂, },
    have p₄ := abs_sub_lt hx₂ hy₂,
    linarith, },










    
end


end exlean -- hide