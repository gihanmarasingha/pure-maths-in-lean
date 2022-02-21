import  group.left_cancellation -- hide

/-
# Groups

## Level 6: Injectivity of inverse
-/


namespace exlean -- hide

open group -- hide

variables {G: Type* } [group G] (a b c : G)  -- hide

/-
One way to prove two group elements are equal is to show that their inverses are equal.

### Tasks

* Give a handwritten proof that if $a$ and $b$ are group elements, then
$a^{-1} = b^{-1} \leftrightarrow a = b$.

* Give a Lean proof of this result.
-/


/- Lemma :
Let $a$ and $b$ be elements of a group $G$. We have
$a^{-1} = b^{-1} \leftrightarrow a = b$.
-/
lemma inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
begin
  split,
  { assume h : a⁻¹ = b⁻¹,
    calc a = a⁻¹⁻¹  : by rw inv_inv
    ... = b⁻¹⁻¹     : by rw h
    ... = b         : by rw inv_inv },
  { assume h : a = b,
    show a⁻¹ = b⁻¹, rw h,}
end

end exlean -- hide