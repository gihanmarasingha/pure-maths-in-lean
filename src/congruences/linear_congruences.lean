import congruences.mod_mul -- hide

/-
#  Congruences

## Level 8: Linear congruences
-/

namespace exlean -- hide

variables {a b c d n : ℤ} -- hide




/- Theorem :
Given `a ≡ b [MOD n]` and `c ≡ d [MOD n]`, the congruence `a * c ≡ b * d [MOD n]` follows.
-/
lemma moddf (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) :
a * c ≡ b * d [MOD n] :=
begin
  rw mod_def at *,
  rw (show b * d - (a * c) = (b - a) * d + (d - c) * a, by linarith),
  apply dvd_add,
  { apply dvd_mul_of_dvd_left h₁, },
  { apply dvd_mul_of_dvd_left h₂, },








end

end exlean -- hide