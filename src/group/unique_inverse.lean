import  group.mul_right_inv -- hide

/-
# Groups

## Level 3: Uniqueness of inverse
-/


namespace exlean -- hide

open group -- hide

variables {G : Type*} [group G] {a b c : G} -- hide


/-
In the first level of this world, you saw the 'uniqueness of identity' result. In this level,
you'll prove an equivalent 'uniqueness of inverse' result.


### Tasks

* By hand, write a proof that if $a, b$ are elements of a group $G$ and if $a \ast b = 1$, then
$a^{-1}$ equals $b$. You will only need the group axioms.

* Complete the Lean 'proof by calculation' below, using only the group axioms.
-/

/- Theorem : 
If $a \ast b = 1$, then $a^{-1} = b$.
-/
lemma inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
begin
/- hint
  calc a⁻¹ = sorry      : by sorry
  ... = b               : by sorry
-/
  calc a⁻¹ = a⁻¹ * 1    : by rw mul_one
  ... = a⁻¹ * (a * b)   : by rw h
  ... = (a⁻¹ * a) * b   : by rw mul_assoc
  ... = 1 * b           : by rw mul_left_inv
  ... = b               : by rw one_mul
end 

end exlean -- hide