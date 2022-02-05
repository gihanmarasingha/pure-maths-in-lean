import tactic.linarith divisibility.dvd_definition -- hide

/-
#  Divisibility

## Level 2: Reflexivity of divisibility
-/

namespace exlean --hide

/-
In this short level, your task is to prove reflexvity of the divisiblity relation.
-/

/- Hint : Using the definition of divisibility
You can use `rw dvd_def` to replace `x ∣ y` with its definition.
-/


/- Theorem :
`a ∣ a`, for every integer `a`.
-/
theorem dvd_refl (a : ℤ) : a ∣ a :=
begin
  use 1,
  norm_num,




end

end exlean -- hide