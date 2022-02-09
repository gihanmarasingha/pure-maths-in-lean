import tactic.linarith divisibility.bezout2  -- hide

/-
# Divisibility

## Level 17: The Euclidean algorithm - basic step
-/

namespace exlean -- hide

/-
As a result of Bézout's lemma, we can define a function `gcd` such that `gcd a b` is
the greatest common divisor of `a` and `b`.
-/

noncomputable theory -- hide

-- begin hide
lemma gcd_exists (a b : ℤ) : ∃ (d : ℤ), (greatest_common_divisor d a b ∧ 0 ≤ d) :=
begin
  rcases bezout a b with ⟨d, s, t, h, h₂, h₃⟩,
  exact ⟨d, h, h₂⟩,
end
-- end hide

noncomputable def gcd (a b : ℤ) := classical.some (gcd_exists a b) -- hide

noncomputable def egcd (a b : ℤ) := classical.some (bezout a b) -- hide

/- Axiom : greatest_common_divisor_gcd (a b : ℤ) :
(greatest_common_divisor (gcd a b) a b) ∧ (0 ≤ gcd a b)
-/
lemma greatest_common_divisor_gcd (a b : ℤ) : (greatest_common_divisor (gcd a b) a b) ∧ (0 ≤ gcd a b) := -- hide
begin -- hide
  apply @classical.some_spec _ (λ d, (greatest_common_divisor d a b) ∧ (0 ≤ d)), -- hide
end -- hide

example (a b : ℤ) : ∃ (s t : ℤ), (greatest_common_divisor (egcd a b) a b) ∧ (0 ≤ egcd a b) ∧ (egcd a b = a * s + b * t):= -- hide
begin -- hide
  apply @classical.some_spec _ (λ d, ∃ s t, (greatest_common_divisor d a b) ∧ (0 ≤ d) ∧ d = a * s + b * t), -- hide
end -- hide


/-
The lemma `greatest_common_divisor_gcd` asserts that `gcd a b` is a greatest common divisor of `a`
and `b` and that `0 ≤ gcd a b`
-/

example (a b : ℤ) : (greatest_common_divisor (gcd a b) a b) ∧ (0 ≤ gcd a b)
:= greatest_common_divisor_gcd a b

open int -- hide


variables {a : ℤ}  -- hide

/- Theorem :
Suppose $a$, $b$, $q$, $r$ are integers and that $a = qb + r$.

Then $\gcd(a, b) = \gcd(b, r)$.
-/
lemma euclid_basic (q b r : ℤ) : gcd (q * b + r) b = gcd b r:=
begin
  /- hint
  set a := q * b + r with h,
  rcases (greatest_common_divisor_gcd a b) with ⟨⟨⟨hxa, hxb⟩, hxgreat⟩, hxnn⟩,
  -/
  set a := q * b + r with h,
  rcases (greatest_common_divisor_gcd a b) with ⟨⟨⟨hxa, hxb⟩, hxgreat⟩, hxnn⟩,
  rcases (greatest_common_divisor_gcd b r) with ⟨⟨⟨hyb, hyr⟩, hygreat⟩, hynn⟩,
  apply dvd_antisymm,
  { exact hxnn, },
  { exact hynn, },
  { specialize hygreat (gcd a b),
    apply hygreat,
    split,
    { exact hxb, },
    { rw (show r = a + (b * (-q)), by linarith),
      apply dvd_add hxa,
      apply dvd_mul_of_dvd_left hxb, }, },
  { specialize hxgreat (gcd b r),
    apply hxgreat,
    split,
    { rw [h, mul_comm],
      apply dvd_add (dvd_mul_of_dvd_left hyb _) hyr, },
    { exact hyb, }, },















end


end exlean -- hide