import tactic.linarith divisibility.euclid_basic  -- hide

/-
# Divisibility

## Level 18: The Euclidean algorithm
-/

namespace exlean -- hide

/-
Using the result `euclid_basic` from our previous level, we can compute greatest common divisors.
-/

open int -- hide

variables (a b d q r x y: ℤ)  -- hide

/-
As an example, we'll compute $\gcd(100,7)$. As a first step, we'll use `euclid_basic` to justify
the assertion that $\gcd(100,7) = \gcd(7, 2)$. The reason for this is that 
$100 = 14 \times 7 + 2$, so $\gcd(14\times 7 + 2, 7) = \gcd(7, 2)$, by `euclid_basic`.

Here ia a proof in Lean.
-/

example : gcd 100 7 = gcd 7 2 := euclid_basic 14 7 2

/-
In the above proof, note that the arguemnts $14$, $7$, and $2$ correspond to the calculation
$100 = 14 \times 7 + 2$.
-/

/- Axiom : gcd_eq_greatest_common_divisor
If d is a greatest common divisor of a and b and if 0 ≤ d, then gcd a b = d.
-/
-- begin hide
lemma gcd_eq_greatest_common_divisor (h₁ : greatest_common_divisor d a b) (h₂ : 0 ≤ d) : gcd a b = d :=
begin
  rcases (greatest_common_divisor_gcd a b) with ⟨hxgreat, hxnn⟩,
  exact uniqueness_of_greatest_common_divisor hxnn h₂ hxgreat h₁,
end
-- end hide

/- Axiom : gcd_zero
gcd a 0 = abs a
-/
-- begin hide
lemma gcd_zero : gcd a 0 = abs (a) :=
begin
  refine gcd_eq_greatest_common_divisor _ _ _ _ (abs_nonneg a),
  rcases abs_cases a with ⟨habs, hineq⟩ | ⟨habs, hineq⟩; rw habs,
  { apply greatest_common_divisor_zero, },
  { split,
    { split,
      { rw neg_dvd, },
      { use 0,
        rw mul_zero, }, },
    { rintros e ⟨ha, _⟩,
      apply dvd_neg_of_dvd ha, }, },
end
-- end hide

/-
We'll apply this process repeatedly until we reach $\gcd(a, 0)$, for some integer $a$. We then
use the lemma `gcd_zero`.
-/

example : gcd a 0 = abs a := gcd_zero a

/-
Below is a Lean proof that 1 is a greatest common divisor of 7 and 100.
-/

example : gcd 100 7 = 1 :=
begin
  calc gcd 100 7
      = gcd 7 2 : euclid_basic 14 7 2
  ... = gcd 2 1 : euclid_basic 3 2 1
  ... = gcd 1 0 : euclid_basic 2 1 0
  ... = 1       : gcd_zero 1,
end

/-
### Task

Adapt the proof above to show that $\gcd(340, 23) = 1$.
-/

#eval 240 / 23

/- Lemma : no-side-bar
$\gcd(340, 23) = 1$
-/
lemma three_forty_gcd_23 : gcd 240 23 = 1 :=
begin
  calc gcd 240 23
      = gcd 23 10 : euclid_basic 10 23 10
  ... = gcd 10  3 : euclid_basic 2 10 3
  ... = gcd  3  1 : euclid_basic 3 3 1
  ... = gcd  1  0 : euclid_basic 3 1 0
  ... = 1         : gcd_zero 1,
end


end exlean -- hide