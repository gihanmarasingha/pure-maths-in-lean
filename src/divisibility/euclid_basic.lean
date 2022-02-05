import tactic.linarith divisibility.bezout  -- hide

/-
# Divisibility

## Level 14: The Euclidean algorithm - basic step
-/

namespace exlean -- hide

/-
The fundamental step in Euclid's algorithm is the proof that if $a = bq + r$, then 
$\gcd(a,b) = \gcd(b,r)$.
-/

open int -- hide

/- Theorem :
Suppose $a$, $b$, $q$, $r$ are integers and that $a = bq + r$.

Suppose $x$ and $y$ are non-negative integers, that $x$ is a greatest common divisor of $a$ and $b$,
and that $y$ is a greatest common divisor of $b$ and $r. Then $x = y$.
-/
lemma euclid_basic (a b q r x y: ℤ) (h : a = b * q + r) (h₁ : greatest_common_divisor x a b)
(h₂ : greatest_common_divisor y b r) (h₃ : 0 ≤ x) (h₄ : 0 ≤ y) : x = y :=
begin
  rcases h₁ with ⟨⟨hxa, hxb⟩, hxgreat⟩,
  rcases h₂ with ⟨⟨hyb, hyr⟩, hygreat⟩,
  apply dvd_antisymm,
  { exact h₃, },
  { exact h₄, },
  { specialize hygreat x,
    apply hygreat,
    split,
    { exact hxb, },
    { rw (show r = a + (b * (-q)), by linarith),
      apply dvd_add hxa,
      apply dvd_mul_of_dvd_left hxb, }, },
  { specialize hxgreat y,
    apply hxgreat,
    split,
    { rw h,
      apply dvd_add (dvd_mul_of_dvd_left hyb _) hyr, },
    { exact hyb, }, },










end






end exlean -- hide