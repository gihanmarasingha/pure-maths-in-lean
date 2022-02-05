import tactic.linarith tactic.ring_exp strong_induction.basic -- hide

/-
# Strong Induction

## Level 1: Strong induction

-/

namespace exlean -- hide

open_locale classical -- hide

open nat -- hide

/-
Strong induction is used to prove that a predicate $P$ holds for every natural number $n$.
To apply strong induction you need to prove:
* [Base case] $P(0)$
* [Inductive step] For all $k : ℕ$, $P(k + 1)$ follows from the inductive hypothesis
that for all $m : ℕ$, if $m \le k$, then $P(m)$ holds.
-/

/-
### Strong induction example

A sequence $f : ℕ → ℤ$ is defined by $f(0) ≔ 2$, $f(1) ≔ 8$, and
$f (n + 2) ≔ 8 f(n + 1) - 15 f(n)$.
-/

namespace strong_sequence -- hide

def f : ℕ → ℤ 
| 0 := 2
| 1 := 8
| (n + 2) := 8 * f(n + 1) - 15 * f(n)

/-
By strong induction, we'll prove that $f(n) = 3^n + 5^n$, for every natural number $n$.
-/

example (n : ℕ) : f(n) = 3 ^ n + 5 ^ n :=
begin
  let P := λ x, f(x) = 3 ^ x + 5 ^ x, -- The predicate.
  have base : P 0,
  { dsimp [P, f], -- Use the definitions of `P` and `f`.
    norm_num, },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  { dsimp [P],
    assume k : ℕ,
    assume ih : ∀ (m : ℕ), m ≤ k → P m,
    cases k with p,
    { refl, },
    { dsimp [f], -- use the recursive definition of `f`.
      simp only [succ_eq_add_one] at *, -- replace `succ p` with `p + 1` everywhere.
      rw ih (p + 1) (by linarith),
      rw ih p (by linarith),
      ring_exp, }, }, -- the `ring_exp` proves equations involving variable exponents.
  apply strong_induction base ind_step,
end

/-
In the proof above, we start by definining the predicate `P` as an anonymous (or 'lambda') function.
For example `λ x, x ^ 2` is the function that sends `x` to `x ^ 2`. We define `P` to be the predicate
that takes `x` to the proposition `f(x) = 3 ^ x + 5 ^ x`. Note `λ` is typed `\la` in Lean.

Having defined `P`, we prove both the base case (which I've called `base`) and the inductive step
(which I've called `ind_step`). To conlude, we apply strong induction to these two hypotheses.

In the inductive step, we introduce the induction variable `k` and the induction hypothesis `ih`.
Next, in a procedure common to proofs by induction, we consider cases for `k`.

As `k` is a natural number, either `k = 0` or `k` is the successor of some natural number `p`.
In the later case, we make things easy for ourselves by replacing `succ p` with `p + 1`.

Note that we apply the induction hypothesis twice: once to `p + 1` and again to `p`.
-/


/-
### Task

A sequence $g : \mathbb{N} \to \mathbb{Z}$ is defined by $g(0) ≔ 11$, $g(1) ≔ 26$, and
$g(n + 2) ≔ 5g(n + 1) - 6g(n)$.

* By adapting the proof above, prove that $g(n) = 4 \times 3 ^ n + 7 \times 2 ^ n$, for each natural number $n$.
* Do the same thing by hand.
-/

def g : ℕ → ℤ 
| 0 := 11
| 1 := 26
| (n + 2) := 5 * g(n + 1) - 6 * g(n)


/- Theorem : no-side-bar
$g(n) = 4 \times 3 ^ n + 7 \times 2 ^ n$, for each natural number $n$.
-/
theorem formula_for_g (n : ℕ) : g(n) = 4 * 3 ^ n + 7 * 2 ^ n :=
begin
  let P := λ x, g(x) = 4 * 3 ^ x + 7 * 2 ^ x,
  have base : P 0,
  { dsimp [P],
    refl, },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  { dsimp [P],
    assume k : ℕ,
    assume ih : ∀ (m : ℕ), m ≤ k → P m,
    cases k with p,
    { refl, },
    { dsimp [g],
      simp only [succ_eq_add_one] at *,
      rw ih (p + 1) (by linarith),
      rw ih p (by linarith),
      ring_exp, }, },
  apply strong_induction base ind_step,









end

end strong_sequence -- hide



end exlean