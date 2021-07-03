import myint.basic equations.associativity -- hide

/-
# Equations

## Level 7: Multiple rewrites

Rather than writing, for example `rw add_assoc x y z, rw add_comm`, you can write
`rw [add_assoc x y z, add_comm]`. Use this technique, together with `have`, to write a structured
proof below.

Now write a proof using a long chain of rewrites followed by `refl`. Which proof do you prefer? Why?
-/

namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x y z : ℤ) -- hide

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. Then `x + (y + (x + z)) = (z + (x + y)) + x`.
-/
theorem add_right_comm_adele : x + (y + (x + z)) = (z + (x + y)) + x :=
begin [pure_maths]
  have h : y + (x + z) = z + (x + y),
    rw add_comm, rw add_comm x, rw add_assoc, refl,
  rw h, rw add_comm, refl,
end

end exlean -- hide