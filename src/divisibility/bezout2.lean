import tactic.linarith divisibility.gcd_neg -- hide
/-
# Divisibility

## Level 16: Bézout's lemma (version 2)
-/

namespace exlean -- hide

/-
You'll show that for all integers $a$ and $b$, there exists a non-negative integer $d$ such that
$d$ is a greatest common divisor of $a$ and $b$.
-/

open int

variables (a b : ℤ) -- hide

/-
The lemma `nonneg_or_nonneg_neg'` will be useful.
-/

example : 0 ≤ a ∨ 0 ≤ -a := nonneg_or_nonneg_neg' a

/- Theorem :
For all integers $a$ and $b$, there exists a non-negative integer $d$ such that
$d$ is a greatest common divisor of $a$ and $b$.
-/
lemma bezout : ∃ d, (greatest_common_divisor d a b ∧ 0 ≤ d) :=
begin
  cases (bezout1 a b) with d hd,
  cases (nonneg_or_nonneg_neg' d) with ha hna,
  { use d,
    cc, },
  { use -d,
    have h₂ : greatest_common_divisor (-d) a b, from gcd_neg hd,
    cc, }











end






end exlean -- hide