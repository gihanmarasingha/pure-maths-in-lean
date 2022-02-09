import congruences.mod_mul_right -- hide

/-
#  Congruences

## Level 7: Multiplying congruences
-/

namespace exlean -- hide

variables {a b c d n : ℤ} -- hide

/-
### Tasks
* Given `a ≡ b [MOD n]` and `c ≡ d [MOD n]`, show `a * c ≡ b * d [MOD n]`.

* Write the same proof by hand.

The nicest way to do this is by using two different divisibility results.
-/

/- Hint: Starting the proof
As before, start by converging the congruences to divisibility statements using `rw mod_def at *`.
-/

/- Hint: A cunning rewrite
Your next task is to rewrite the goal from `n ∣ b * d - a * c` to something of the form
`n ∣ p + q`, for appropriate `p` and `q`. You can then use `apply dvd_add`.

You should then `apply` another of the divisibility results to each of the
resulting goals.
-/


/- Theorem :
Given `a ≡ b [MOD n]` and `c ≡ d [MOD n]`, the congruence `a * c ≡ b * d [MOD n]` follows.
-/
lemma mod_add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) :
a * c ≡ b * d [MOD n] :=
begin
  rw mod_def at *,
  rw (show b * d - (a * c) = (b - a) * d + (d - c) * a, by linarith),
  apply dvd_add,
  { apply dvd_mul_of_dvd_left h₁, },
  { apply dvd_mul_of_dvd_left h₂, },








end

end exlean -- hide