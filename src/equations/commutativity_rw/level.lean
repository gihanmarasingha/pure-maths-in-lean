import tactic.structure_helper tactic.pure_maths

--import myint.basic

--open MyInt --hide

--variables {myint : Type} [MyInt myint] -- hide

--local notation `ℤ` := myint -- hide

/-
# Equations

## Level 2: Commutativity of addition

Now we'll prove something (slighlty) more interesting, that `x + y = y + x` for all integers `x`
and `y`. Try the `refl` tactic below (remember to put a comma after `refl`) and see what happens.

You'll get an error message:
```
invalid apply tactic, failed to unify
  x + y = y + x
with
  ?m_2 = ?m_2
```

Lean tells you that you're trying to use `refl` to prove `x + y = y + x`, but it expects a target
of the form `?m_2 = ?m_2`. There's no special meaning to the underscores here. It's the same as
writing `?X = ?X` as in the previous level.

The problem: even though we 'know' the left and right sides are equal, they are not
*identically equal*.
Fortunately, Lean comes with a *theorem* of just the right kind. It's called `add_comm`.
The result `add_comm a b` states that `a + b = b + a`, where `a` and `b` are integers.

To apply this theorem, we'll use the `rw` (short for `rewrite`) tactic.

Replace 
-/


namespace exlean -- hide

variables (x y : ℤ) -- Declare `x` and `y` to be integers.

/- Axiom : `add_comm`
`a + b = b + a`, for all integers `a` and `b`.
-/
theorem add_comm (a b : int) : a + b = b + a := int.add_comm a b


--theorem add_comm (a b : myint) : a + b = b + a := MyInt.add_comm a b

/- Theorem : no-side-bar
`x + y = y + x`, for all integers `x` and `y`.
-/
theorem x_plus_y_eq_y_plus_x : x + y = y + x :=
begin [nat_num_game]
  rw add_comm x y,
  refl,
end

end exlean -- hide
