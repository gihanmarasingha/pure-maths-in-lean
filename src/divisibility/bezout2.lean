import tactic.linarith divisibility.gcd_neg -- hide
/-
# Divisibility

## Level 19: Bézout's lemma (version 2)
-/

namespace exlean -- hide

/-
You'll show that for all integers $a$ and $b$, there exists a non-negative integer $d$ such that
$d$ is a greatest common divisor of $a$ and $b$.
-/

open int -- hide

variables (a b : ℤ) -- hide

/-
The lemma `nonneg_or_nonneg_neg'` will be useful.
-/

example : 0 ≤ a ∨ 0 ≤ -a := nonneg_or_nonneg_neg' a

/- Theorem :
For all integers $a$ and $b$, there exists a non-negative integer $d$ such that
$d$ is a greatest common divisor of $a$ and $b$.
-/
lemma bezout (a b : ℤ) :
∃ (d s t : ℤ), greatest_common_divisor d a b ∧ 0 ≤ d ∧ (d = a * s + b * t) :=
begin
  rcases bezout1 a b with ⟨e, u, v, hgcd, heq⟩,
  cases (nonneg_or_nonneg_neg' e) with ha hna,
  { use [e, u, v],
    exact ⟨hgcd, ha, heq⟩ },
  { use [-e, -u, -v],
    have h₂ : greatest_common_divisor (-e) a b, from gcd_neg hgcd,
    exact ⟨h₂, hna, by linarith⟩, },





















end






end exlean -- hide