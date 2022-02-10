import tactic.linarith divisibility.dvd_refl -- hide

/-
#  Divisibility

## Level 3: Every number is a factor of zero
-/

namespace exlean --hide



/-
### Task
Prove that every number is a factor of zero.
-/

/- Theorem :
Let `a` be an integer. Then `a ∣ 0`.
-/
theorem dvd_zero (a : ℤ) : a ∣ 0 :=
begin
  rw dvd_def,
  use 0,
  norm_num,




end

end exlean -- hide