import myint.basic equations.unique_additive_inverse -- hide

/-
# Equations

## Level 15: The simplifier

This level introduces a powerful new tactic, `simp`, Lean's simplifier. It rewrites 
repeatedly using either supplied theorems & hypotheses or theorems that it 'knows'.

To suggest theorems and hypotheses for use with `simp`, provide them as a comma-separated list.
In the example below, we supply `simp` with `add_assoc` and `add_comm y x`.

Without `simp`, you'd need several applications of `rw add_assoc`. 
-/

namespace exlean -- hide

open_locale mynum -- hide

namespace pre_group -- hide

open myint -- hide

example (x y z : ℤ) : x + ((y + z) + x) = (y + x) + (z + x) :=
begin
  simp [add_assoc, add_comm y x],
end

/-
### Tasks

* Prove the result below using only `simp` with supplied theorems, as in the example above. You should
only need to supply four theorems.

* For fun (!) try proving this result using `rw`. Which proof do you prefer?
-/

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. Then `(y + x) + (0 + z + 0) + (0 + x + 0) = y + (z + (x + x))`
-/
theorem ymca (x y z : ℤ)
  : (y + x) + (0 + z + 0) + (0 + x + 0) = y + (z + (x + x)) :=
begin
  --simp [add_assoc, add_comm x z, add_zero, zero_add],
  rw [add_zero, add_zero, zero_add, zero_add, add_assoc y x z, add_assoc,
    add_right_comm, add_comm _ z],






end

/- Tactic : simp
The `simp` tactic rewrites repeatedly using either supplied theorems & hypotheses or theorems
that it 'knows'.

To suggest theorems and hypotheses for use with `simp`, provide them as a comma-separated list.
For example `simp [h, add_comm]` rewrites repeatedly with hypotheses `h` and theorem `add_comm`.
-/

end pre_group -- hide

end exlean -- hide