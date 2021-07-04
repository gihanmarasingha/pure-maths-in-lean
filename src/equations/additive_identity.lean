import myint.basic equations.backward_rewrite -- hide

/-
# Equations

## Level 9: Additive identity

The Lean theorem `add_zero` states that `x + 0 = x` for every integer `x`. In mathematics, this
property is called (right) additive identity. Note `add_zero` should appear as a 'Theorem statement'
in the left-hand pane. 
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

/- Axiom : add_zero (a : ℤ) :
a + 0 = a
-/
theorem add_zero (a : ℤ) : a + 0 = a := myint.add_zero' a -- hide

/- 
Your goal is to prove `zero_add`, the right additive identity property, using `add_zero`.
Once you've done this, `zero_add` will be available to you in future levels.

You can use a series of rewrites and a `refl` or you can use a `rw` and the `exact` tactic, as
descrbed in the drop-down box below.

As always, construct a hand-written proof **before** writing your Lean proof.
-/

/- Tactic : exact
If `h` an expression (or the name of a hypothesis or theorem) that exactly matches the target,
then `exact h` will close the current goal.
-/

/- Hint : The `exact` tactic.
The `exact` tactic can be used in place of `rw` where a hypothesis or theorem *exactly*
matches the target.

Thus, the goal `⊢ (x + y) + z = x + (y + z)` is closed with `exact add_assoc x y z`.

Likewise, if `h : x + y + 5 = 10`, then `⊢ x + y + 5 = 10` is closed with `exact h`.
-/

/- Theorem :
`0 + a = a` for every integer `a`.
-/
theorem zero_add (a : ℤ) : 0 + a = a :=
begin [pure_maths]
  rw add_comm,
  exact add_zero a,

  
end

end pre_group -- hide

end exlean -- hide