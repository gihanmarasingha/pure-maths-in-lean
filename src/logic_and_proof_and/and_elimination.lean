import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 3: And elimination

What I've called 'decomposition' of a hypothesis `h : p ∧ q` is actually a combination of two
more fundamental principles: _left and elimination_ and _right and elimination_

**Theorem**: Let $x$ be an integer. Supose $h : (x > 0) \land (x ^ 2 = 16)$. Then $x ^ 2 = 16$.

**Proof**: The result follows from right and elimination on $h$.
-/

/- Axiom: and.elim_right (h : p ∧ q) : q
-/


/- Axiom: and.elim_left (h : p ∧ q) : p
-/


/-
In Lean, if `h : p ∧ q`, then `and.elim_right h` (also written `h.right`) is a proof of `q`.
Likwise `and.elim_left h` (or `h.left`) is a proof of `p`.
-/

example (x : ℤ) (h : (x > 0) ∧ (x * x = 16)) : x * x = 16 :=
begin
  exact and.elim_right h,
end

/-
The same proof can be given using an alternative notation.
-/
example (x : ℤ) (h : (x > 0) ∧ (x * x = 16)) : x * x = 16 :=
begin
  exact h.right,
end

namespace exlean -- hide

/-
### Tasks

1. Replace `sorry` below with a one-line Lean proof, adapting either of the proofs above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Theorem : no-side-bar
Let $x$ and $y$ be integers. Suppose $h : (x + y = 3) \land (x < 0)$. Then $x + y = 3$.
-/
theorem and_elim1 (x y : ℤ) (h : x + y = 3 ∧ x < 0) :
x + y = 3 :=
begin
  exact h.left,
end

end exlean -- hide