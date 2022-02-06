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