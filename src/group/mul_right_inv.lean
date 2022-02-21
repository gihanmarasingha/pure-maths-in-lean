import  group.inv_inv -- hide

/-
# Groups

## Level 2: Right inverse
-/



namespace exlean -- hide

open group -- hide

variables {G : Type*} [group G] (a b c : G) -- hide


/-
In the previous level, we introduced the left inverse axiom for groups. In this level, you'll
*prove* that the right inverse property follows from the other group axioms.


### Tasks

* By hand, write a proof that if $b$ is an element of a group $G$, then $b * b^{-1} = 1$. You may
use any axioms or theorems proved in the previous level.

* Complete the Lean 'proof by calculation' below.
-/

/- Theorem : 
$b \ast b^{-1} = 1$.
-/
theorem mul_right_inv : b * b⁻¹ = 1 :=
begin
/- hint
  calc b * b⁻¹ = sorry : by sorry
  ... = 1              : by sorry
-/
  calc b * b⁻¹ = (b⁻¹)⁻¹ * b⁻¹ : by rw inv_inv
  ... = 1                      : by rw mul_left_inv
end

end exlean -- hide