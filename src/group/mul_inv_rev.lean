import group.unique_inverse -- hide

/-
# Groups

## Level 4: The inverse of a product
-/


namespace exlean -- hide

open group -- hide

variables {G : Type*} [group G] (a b c : G) -- hide


/-
### Tasks

* By hand, write a proof that if $a, b$ are elements of a group $G$, then
$(a \ast b)^{-1} = b^{-1} \ast a^{-1}$.

* Complete the Lean proof below.
-/

/- Hint : A helpful result
You've seen `inv_eq_of_mul_eq_one`. This result states that if `s * t = 1`, then `s⁻¹ = t`.
Here, you can apply this result, via `apply inv_eq_of_mul_eq_one` to change the
goal to one of proving `(a * b) * (b⁻¹ * a⁻¹) = 1`.

This latter goal can be proved by calculation.
-/

/- Theorem : 
$(a \ast b)^{-1} = b^{-1} \ast a^{-1}$.
-/
theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc (a * b) * (b⁻¹ * a⁻¹)
      = a * (b * (b⁻¹ * a⁻¹))   : by rw mul_assoc
  ... = a * ((b * b⁻¹) * a⁻¹)   : by rw mul_assoc
  ... = a * (1 * a⁻¹)           : by rw mul_right_inv
  ... = a * a⁻¹                 : by rw one_mul
  ... = 1                       : by rw mul_right_inv
end 

end exlean -- hide