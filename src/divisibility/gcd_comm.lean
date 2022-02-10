import tactic.linarith divisibility.gcd_zero -- hide

/-
# Divisibility

## Level 14: Commutativity of greatest common divisor
-/

namespace exlean -- hide

open int -- hide

variables {a b d : ℤ} -- hide

/- Theorem :
If $d$ is a greatest common divisor of $a$ and $b$, then $d$ is a greatest common divisor of
$b$ and $a$.
-/
theorem greatest_common_divisor_comm (h : greatest_common_divisor d a b) :
greatest_common_divisor d b a :=
begin
  rcases h with ⟨⟨hda, hdb⟩, hcomm⟩,
  split,
  { exact ⟨hdb, hda⟩ },
  { intros e h,
    cases h with h₁ h₂,
    apply (hcomm e),
    exact ⟨h₂, h₁⟩, },







    
end


end exlean -- hide