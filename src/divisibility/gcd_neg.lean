import tactic.linarith divisibility.bezout -- hide
/-
# Divisibility

## Level 15: The negative of a greatest common divisor
-/

namespace exlean -- hide

/-
Suppose $d$ is a greatest common divisor of $a$ and $b$. Then $-d$ is also a greatest common
divisor of $a$ and $b$.

The following results on divisibility will be useful.
-/

open int -- hide

variables {a b d : ℤ} -- hide

/- Axiom : neg_dvd_of_dvd
Given d ∣ a, -d ∣ a follows.
-/
lemma neg_dvd_of_dvd (h : d ∣ a) : -d ∣ a :=
begin
  cases h with m h₂, -- `h₂ : a = d * m`
  use -m, -- `⊢ a = -d * -m`,
  rw h₂, -- `⊢ d * m = -d * -m`,
  ring, -- This follows by algebra.
end

/- Axiom : neg_dvd
-d ∣ a ↔ d ∣ a
-/
lemma neg_dvd : -d ∣ a ↔ d ∣ a :=
begin
  split,
  { assume h : -d ∣ a,
    rw ←neg_neg d,
    exact neg_dvd_of_dvd h, },
  { assume h : d ∣ a,
    exact neg_dvd_of_dvd h, },
end

/- Axiom : dvd_neg_of_dvd
Given d ∣ a, d ∣ -a follows.
-/
lemma dvd_neg_of_dvd (h : d ∣ a) : d ∣ -a :=
begin
  cases h with m h₂, -- `h₂ : a = d * m`
  use -m, -- `⊢ - a = d * -m`,
  rw h₂, -- `⊢ -(d * m) = d * -m`,
  ring, -- This follows by algebra.
end

/- Theorem :
Suppose $d$ is a greatest common divisor of $a$ and $b$. Then $-d$ is also a greatest common
divisor of $a$ and $b$.
-/
lemma gcd_neg (h : greatest_common_divisor d a b) :
greatest_common_divisor (-d) a b :=
begin
  rcases h with ⟨⟨ha, hb⟩, hmin⟩,
  split,
  { split,
    { exact neg_dvd_of_dvd ha, },
    { exact neg_dvd_of_dvd hb, }, },
  { assume e : ℤ,
    rintro ⟨hea, heb⟩,
    specialize hmin (-e),
    apply dvd_neg_of_dvd,
    rw ←neg_dvd_iff_dvd,
    apply hmin,
    split,
    { exact neg_dvd_of_dvd hea, },
    { exact neg_dvd_of_dvd heb, }, },













end






end exlean -- hide