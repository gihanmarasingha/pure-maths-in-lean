import congruences.mod_def -- hide

/-
#  Congruences

## Level 2: Reduction of a congruence
-/

namespace exlean -- hide

/-
Let $x$ and $n$ be integers with $n \ne 0$. One can find an integer $a$ in the range $0 \le a < |n|$
such that $x \equiv a \pmod n$.

This is sometimes called _reduction_ of $x$ modulo $n$.
-/

variables {x a n : ℤ} -- hide

/-
We'll find a number $a$ such that $321 \equiv a \pmod{12}$ and such that $0 \le a < |12|$

For $a$, I'll take the remainder on dividing $321$ by $12$. Note that
$321 = q \times 12 + r$, where $q = 26$ and $r = 9$.
-/

example : ∃ (a : ℤ), 321 ≡ a [MOD 12] ∧ (0 ≤ a) ∧ (a < abs (12)) :=
begin
  use 9,  -- `⊢ 321 ≡ 9 [MOD 12] ∧ (0 ≤ 9) ∧ (9 < abs(12))`
  split,
  { rw [mod_def, dvd_def], -- `⊢ ∃ m, 9 - 321 = 12 * m`
    use -26, -- `9 - 321 = 12 * (-26)`
    norm_num, },
  tidy, -- `tidy` proves `(0 ≤ 9) ∧ (9 < abs(12))`


end

/- Lemma :
There is an integer $a$ such that $500 \equiv a \pmod{63}$ with
$0 \le a < |63|$.
-/
lemma reduction_of_500_mod_63 :
∃ a, 500 ≡ a [MOD 63] ∧ (0 ≤ a) ∧ (a < abs (63)) :=
begin
  use 59,
  split,
  { use -7,
    norm_num, },
  tidy,





end


end exlean -- hide