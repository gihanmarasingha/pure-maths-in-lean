import myint.basic equations.additive_identity -- hide

/-
# Equations

## Level 10: Universal statements

So far, our hypotheses have made reference to specific variables. The hypothesis `h : x + 3 = 5`
states `x + 3 = 5` for the particular variable `x`.

If we want a statement that holds *for every* value of a variable, we use the *universal quantifier*
`∀`. This is read, "for all" or "for every" and is typed `\all`.

For example, `∀ (x : ℤ), x + 5 = 10` states that `x + 5 = 10` *for every* integer `x`. Of course,
this is a false statement! A statement that begins with `∀` is called a
*universally quantified statement*.

Here's how to *use* a universally quantified statement. Given the hypothesis
`h : ∀ (x : ℤ), x + 5 = 10`, the expression `h 3` corresponds to `3 + 5 = 10`.
It's what we get by replacing `x` with `3` in the body of the statement.

If `3 + 5` appears in the target, then `rw h 3` replaces `3 + 5` with `10`.

### The specialize tactic

The `specialize` tactic specializes a universally quantified statement. For example if
`h : ∀ (x : ℤ), x + 5 = 10`, then `specialize h 20` *replaces* `h` with
`h : 20 + 5 = 10`. However, after using `specialize`, you can't go back to the more general
version of `h`.
-/

namespace exlean -- hide

namespace pre_group -- hide

open_locale mynum -- hide

open myint -- hide

variable (x : ℤ) -- hide

/-

### Tasks

Here, you'll prove the unusual result `2 + 5 = 8 + 5` on the assumption `∀ x, x + 5 = 10`.


* Write a proof using `rw`.

* Write another proof where you use one `rw` and one application of `specialize`.

* Think about how you'd write this proof by hand. Compare with my suggested translation at the bottom
of the page.
-/

/- Tactic : specialize
Let the hypothesis `h` be a universally-quantified statement. For example,
`h : ∀ (x : ℤ), x + 5 = 10`.
Then `specialize h 8` replaces `x` with `8` in the body of `h`. Thus `h` becomes `8 + 5 = 10`.

You can specialize on more than one variable at a time. If `k : ∀ (x y : ℤ), x + y = y * x`, then
`specialize k 2 3` replaces `h` with `h : 2 + 3 = 3 * 2`.
-/

/- Theorem : no-side-bar
`2 + 5 = 8 + 5` on the assumption `∀ x, x + 5 = 10`.
-/
theorem two_add_five_eq_eight_add_five_of (h : ∀ x, x + 5 = 10)
  : 2 + 5 = 8 + 5 :=
begin [pure_maths]
  rw [h 2, h 8],
  refl,

  
end

/-
## Translation to a hand-written proof

> Using `h` with `2` in space of `x`, we must show `10 = 8 + 5`.
> But this follows on taking `x` to be `8` in `h`.
-/

end pre_group -- hide

end exlean -- hide