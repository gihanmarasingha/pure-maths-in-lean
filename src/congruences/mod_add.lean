import congruences.mod_mul_right -- hide

/-
#  Congruences

## Level 7: Adding congruences
-/

namespace exlean -- hide

variables {a b c d n : ℤ} -- hide

/-
### Tasks
* Given `a ≡ b [MOD n]` and `c ≡ d [MOD n]`, show `a + c ≡ b + d [MOD n]`. As before, you can prove
this using an appropriate divisibilty lemma.

* Write the same proof by hand.
-/

/- Theorem :
Given `a ≡ b [MOD n]` and `c ≡ d [MOD n]`, the congruence `a + c ≡ b + d [MOD n]` follows.
-/
lemma mod_add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) :
a + c ≡ b + d [MOD n] :=
begin
  rw mod_def at *,
  rw (show b + d - (a + c) = (b - a) + (d - c), by linarith),
  apply dvd_add h₁ h₂,








end

end exlean -- hide