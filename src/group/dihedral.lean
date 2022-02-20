import  group.mul_inv_rev -- hide

/-
# Groups

## Level 6: Dihedral groups
-/


namespace exlean -- hide

open group -- hide

namespace dihedral

variables {D12 : Type* } [group D12] -- hide

variables {r s : D12} -- hide

variables (hr : r ^ 6 = 1) (hs : s ^ 2 = 1) (h : s * r = r⁻¹ * s)

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

/- Theorem : no-side-bar
$(a \ast b)^{-1} = b^{-1} \ast a^{-1}$.
-/
include hr hs -- hide

lemma mul_inv_revd : ∃ (i j : ℕ), s ^ 3 * r ^ 8 = r ^ i * s ^ j  :=
begin
  use [4,1],
  calc s ^ 3 * r ^ 8 = s ^ (2 + 1) * r ^ 8 : by refl
  ... = (s ^ 2 * s ^ 1) * r ^ 8 : by rw pow_add
  ... = (1 * s ^ 1) * r ^ 8 : by rw hs
  ... = (1 * s) * r ^ 8 : by rw pow_one
  ... = s * r ^ 8     : by rw one_mul
  ... = r ^ 4 * s ^ 1 : sorry
end 

end dihedral

end exlean -- hide