import myint.basic equations.simplifier -- hide

-- This import contains the definitions of the algebraic structures `add_monoid`, `add_comm_group`, etc.
import algebra.group.basic

/-
# Equations

## Level 16: Algebraic structures and advanced tactics

In this level, we'll show how to unleash `simp`'s power using 'type classes'. We'll introduce
algebraic structures (such as additive monoid and additive commutative group) that you'll explore
in greater detail later.

In the last level, I mentioned that `simp` can use theorems that it knows, but we still had to
supply every theorem explicitly.

The reason is that `simp` doesn't (yet) know anything about
the integer type we've been using. That's because we aren't actually using Lean's built-in integer
type, but our own copy, called `myint`.

The result I've called `zero_add` is short for `exlean.pre_group.zero_add`.
Here `exlean` and `pre_group` are
<a href="https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html#namespaces",
target = "blank">namespaces</a> I've created to hide the messy details. You don't need to
understand namespaces at the moment, beyond the fact that they permit the same name to be used
for different functions.

### Monoids and groups

The simplifier does know a *different* theorem called `zero_add`, outside of any namespace.
This theorem isn't restricted to a particular type (such as integers, natural numbers, vectors of
length 2, etc.). Rather, it holds for any type belong to the `add_monoid` *type class*.

A type class is merely a mechanism for dealing coherently with a collection of types that satsify
certain properties. To be an *instance* of the `add_monoid` type class, a type `G` must have a 'zero'
element and an operation called addition and denoted `+` which satisfiy the properties
of additive associativity and additive identity (both left and right).
-/

namespace exlean -- hide

open_locale mynum -- hide

namespace pre_group -- hide

open myint -- hide

/-
Here, we show that `myint` is an intance of the `add_monoid` (short for 'additive monoid' type class.
To do this, we merely need to provide the apprioate 'fields' of the `add_monoid` structure.

For example, the line `zero_add := exlean.pre_group.zero_add,` fulfills the `zero_add`
constraint of the `add_monoid` type class by supplying our theorem `exlean.pre_group.zero_add`.

In fact, there are fields other than those shown, but Lean can generate these automatically from
the specified fields. This is what the `..` notation asks Lean to do.
-/

instance : add_monoid myint :=
{ add_assoc := exlean.pre_group.myint.add_assoc,
  zero_add := exlean.pre_group.zero_add,
  add_zero := exlean.pre_group.add_zero,
  .. }

/-
An instance of `add_comm_monoid` is an `add_monoid` for which the `+` operation is commutative.
We only need supply the `add_comm` field and let Lean generate the other fields by providing the
instance `myint.add_monoid`. Again, we use the `..` notation to do this.
-/

instance : add_comm_monoid myint :=
{ add_comm := exlean.myint.add_comm,
  .. myint.add_monoid }

/-
An `add_group` (addtive group) is an `add_monoid` that has an additive negation operator which
satisfies the `add_left_neg` property, namely that `(-a) + a = 0` for every `a`.
-/

instance : add_group myint :=
{ neg := exlean.myint.neg,
  add_left_neg := exlean.pre_group.add_left_neg,
  .. myint.add_monoid }


/-
Finally an `add_comm_group` (additive commutative group) is an additive group that is also
an additive commutative monoid. All we need do is provide the required instances.
-/

instance : add_comm_group myint :=
{ .. myint.add_group, .. myint.add_comm_monoid }

end pre_group -- hide

/-
### Levelled-up `simp`

Now `simp` will automatically use `zero_add`, `add_zero`, `add_left_neg`, `add_right_comm`, etc.
Here's an example.
-/

example (x y : ℤ) : x + (-y) + y = x + 0 :=
begin
  simp
end

/-
Note that `add_assoc` and `add_comm` are *not* automatically applied by `simp`. Can you think why?
-/

example (x y z : ℤ) : (y + x) + (0 + z + 0) + (0 + x + 0) = y + (z + (x + x)) :=
begin
  simp [add_assoc, add_comm x z],
end


/-
In the example below, an ordinary `simp` would be useless as the target `⊢ x = y` cannot be
simplified further. However, using `simp at h` will simplify the hypothesis `h` using the 
`sub_right_inj` theorem. You haven't seen this theorem yet: suffice it to say that it does the 
obvious thing and `simp` finds it for you.

-/
example (x y z : ℤ) (h : z - x = z - y) : x = y :=
begin
  simp at h,
  exact h,
end

/-
### Congruence closure

Congruence closure, or `cc`, is another powerful tactic. Don't worry about what the words
'congruence' and 'closure' mean here—they refer to concepts in computer science.

Roughly speaking, `cc` can be used to prove equations where the proof depends on associativity,
commutativity, and (optionally) the use of hypotheses in the local context. Here's an example.
-/

example (x y z : ℤ) (h : (z + x) + y = y + z * x) : y + z * x = y + (z + x) :=
begin
  cc,
end

/- Tactic : cc
`cc` can be used to prove equations where the proof depends on associativity,
commutativity, and (optionally) the use of hypotheses in the local context.
-/

/-
Use `simp` (and whatever else you need) to prove the following result.
This *statement* is similar to a hard result you proved in a previous level, but the
*proof* can be written in no more than two lines.
-/

/- Theorem : no-side-bar
If `y + x = x`, then `y = 0`.
-/
theorem eq_zero_of_add_left_eq_self (x y z : ℤ) (h : y + x = x)
  : y = 0 :=
begin [pure_maths]
  simp at h,
  exact h,

end

end exlean -- hide
