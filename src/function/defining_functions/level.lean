import mynat.basic -- hide

open_locale mynum -- hide

/-
# Functions

## Level 1: Defining functions

A function is a map from one set, called the domain, to another set, called the codomain.

The notation `f : S → T` is read, "`f` is a function with domain `S` and codomain `T`" or "`f` is a
function from `S` to `T`".

To specify that `f` maps each `x` to some expression `y`, we write `f : x ↦ y` or
`f(x) = y`, when doing mathematics by hand.

In Lean, we combine all the above information into:
```
def f : S → T := λ x, y
```
where `y` is an expression that depends on `x`. Here `λ` is a Greek letter called lambda.
Its only significance is to indicate that the following quantity `x` is a variable.

Below is the definition of a function `my_f` from the set `ℕ` of natural numbers (the non-negative)
integers to itself. It takes each `x` to `3 * x + 5`.
-/

namespace exlean -- hide

/- Axiom : `my_f`
The function `my_f` is defined so that `my_f (x) = 3 * x + 5` for every 
natural number `x`.
-/
def my_f : ℕ → ℕ := λ x, 3 * x + 5

/-
Your task is to prove `my_f 10 = 35`. By definition of `my_f`, you must prove `3 * 10 + 5 = 35`.
It may come as a surprise to learn that Lean can prove this using `refl`.
The reason is that when Lean uses `refl`, it applies definitions until no further simplification is
possible. For reasons that will become apparent later, the definitions of addition and
multiplication can be applied to reduce any 'sum' into a natural number.
-/


/- Theorem : no-side-bar
The function `my_f` takes `10` to `35`.
-/
theorem my_fun : my_f 10 = 35 :=
begin
  refl,
end

end exlean -- hide
