import congruences.linear_congruences_no_soln-- hide

/-
#  Congruences

## Level 13: Solving a linear congruence
-/

namespace exlean -- hide

variables {a n x : ℤ} -- hide

/-
We've seen a necessary condition for a linear congruence to have a solution. You'll now prove a
sufficient condition.

Specifically, you'll show that if $1$ is a greatest common divisor of $a$ and $n$, then the 
congruence $ax \equiv 1 \pmod n$ has a solution for $x$.
-/


/-
### Task

Prove the result above, both by hand and in Lean.
-/

/- Lemma :
If $1$ is a greatest common divisor of $a$ and $n$, then there exists an integer $x$ such that
$a x \equiv 1 \pmod n$.
-/
lemma modeq_mul_eq_one_of_coprime (h : greatest_common_divisor 1 a n) : ∃ (x : ℤ), a * x ≡ 1 [MOD n] :=
begin
  rcases (bezout a n) with ⟨d, s, t, hgcd, hdnn, heq⟩,
  have h₂ : d = 1, from uniqueness_of_greatest_common_divisor hdnn zero_le_one hgcd h,
  subst h₂,
  use s,
  rw heq,
  use t,
  linarith,









end

end exlean -- hide