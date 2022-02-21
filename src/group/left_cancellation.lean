import  group.mul_inv_rev -- hide

/-
# Groups

## Level 5: Left cancellation
-/


namespace exlean -- hide

open group -- hide

variables {G: Type* } [group G] {a b c : G}  -- hide

/-
Just as with 'ordinary' multiplication, we can cancel the same factor on the left of
both sides of an equation.

### Tasks

* Give a handwritten proof that if $a \ast b = a \ast c$, then $b = c$.

* Give a Lean 'proof by calculation' below.
-/


/- Lemma :
If $a \ast b = a \ast c$, then $b = c$.
-/
lemma mul_left_cancel (h : a * b = a * c) : b = c:=
begin
  calc b = 1 * b      : by rw one_mul
  ... = (a⁻¹ * a) * b : by rw mul_left_inv
  ... = a⁻¹ * (a * b) : by rw mul_assoc
  ... = a⁻¹ * (a * c) : by rw h
  ... = (a⁻¹ * a) * c : by rw mul_assoc
  ... = 1 * c         : by rw mul_left_inv
  ... = c             : by rw one_mul
end

end exlean -- hide