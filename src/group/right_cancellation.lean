import  group.injectivity_of_inverse -- hide

/-
# Groups

## Level 7: Right cancellation
-/


namespace exlean -- hide

open group -- hide

variables {G: Type* } [group G] (a b c : G)  -- hide

/-
From the left cancellation result, we cheaply prove an iff result.
-/

/- Axiom : mul_left_cancel_iff
(a b c : G) : a * b = a * c ↔ a = b
-/
lemma mul_left_cancel_iff : a * b = a * c ↔ b = c :=
begin
  split,
  { assume h : a * b = a * c,
    show b = c, exact mul_left_cancel h, },
  { assume h : b = c,
    show a * b = a * c, rw h,
  }
end

/-
### Tasks

* Give a handwritten proof of the right cancellation result, that
$b \ast a = c \ast a \leftrightarrow b = c$. 

* Give a Lean proof of this result.
-/


/- Hint : A one-line proof
You can prove this result in a single line of `rw`s. Start with
`rw [←inv_inj]`.
-/

/- Lemma :
Let $a$ and $b$ be elements of a group $G$. We have
$b \ast a = c \ast a \leftrightarrow b = c$.
-/
lemma mul_right_cancel_iff : b * a = c * a ↔ b = c :=
begin
  rw [←inv_inj, mul_inv_rev, mul_inv_rev, mul_left_cancel_iff, inv_inj],












end

end exlean -- hide