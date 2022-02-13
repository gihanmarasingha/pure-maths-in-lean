import data.int.basic tactic -- hide

/-
# Variables

## Level 1: Introduction to variables; for all elimination
-/



/-
Let $x$ be an integer variable. Consider the following equations:

* $(x - 1) ^ 2 = x ^2 - 2x + 1$,
* $x ^ 2 + x - 6 = 0$,
* $x ^ 2 + 1 = 0$.

One of them holds for every $x$, one only for certain $x$, and one for no $x$.

None of the equations, by itself, is a full mathematical statement. The following *are* complete
mathematical statements, each of which can be proved.

* For every $x : \mathbb Z$, we have $(x - 1)^2 = x^2 - 2x + 1$.
* It's not the case that for every $x : \mathbb Z$, we have $x^2 + x - 6 = 0$.
* There exists an $x : \mathbb Z$ such that $x ^ 2 + x - 6 = 0$.
* There does not exist and $x : \mathbb Z$ such that $x^2 + 1 = 0$.
-/

/-
### For all statements

The symbol $\forall$ is read 'for all' or 'for every'. Thus,
$\forall (x : \mathbb Z), (x - 1) ^ 2 = x ^2 - 2x + 1$ is a short way of writing, 'for every
integer $x$, $(x-1)^2 = x^2 - 2x + 1$'.

In Lean, we write `∀` as `\all`, so the mathematical statement above is written in Lean as
```
∀ (x : ℤ), (x - 1) ^ 2 = x ^ 2 - 2x + 1
```

### For all elimination

Let $h$ be a proof of $\forall (x : \mathbb Z), (x - 1) ^ 2 = x ^2 - 2x + 1$. Part of the meaning
of $h$ is that $(x - 1) ^ 2 = x ^2 - 2x + 1$ holds no matter what *particular* integer value is
subsituted for $x$.

With the above definitions, for all elimination with $h$ and $3$ gives a proof of
$(3-1)^2 = 3 ^ 2 - 2 \times 3 + 1$.


### For all elimination in Lean

Let `h` be a proof of a 'for all' statement (such as `∀ (x : ℕ), x ^ 2 ≥ 0`) and let `a` be a
particular quantity (such as `4`). Then `h a` is a proof of the specialised statement
(in this case, `4 ^ 2 ≥ 0`).
-/

example (h : ∀ (x : ℕ), x ^ 2 ≥ 0) : 4 ^ 2 ≥ 0 :=
begin
  from h 4,
end

/-
### A fun example

**Theorem**: Let $f$ be a function from the natural numbers to the
natural numbers. Let $h$ be the assumption that for every $x$, $f(x) > x^2$. Then
$f(2) > 4$ and $f(3) > 9$.

This theorem can be stated more formally.

**Theorem**: Let $f : \mathbb N \to \mathbb N$, let $h : \forall x, f(x) > x ^2$. Then 
$(f(2) > 4) \land (f(3) > 9)$.

**Proof**: By and introduction, it suffices to prove (1) $f(2) > 4$ and (2) $f(3) > 9$.
1. We show $f(2) > 4$ by for all elimination with $h$ and $2$.
2. We show $f(3) > 9$ by for all elimination with $h$ and $3$.

The same result is proved in Lean as follows.
-/

variable (f : ℕ → ℕ)

example (h : ∀ (x : ℕ), f(x) > x ^ 2) : (f(2) > 4) ∧ (f(3) > 9) :=
begin
  split,
  { show f(2) > 4, from h 2, },
  { show f(3) > 9, from h 3, },
end


/-

### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Hint: Starting the proof
As in the example, you can use `cases h with h₁ h₂` to decompose the 'or' statement `h`.
At later steps, you'll need to use the `rw` and `norm_num` tactics.
-/

/- Hint: Dealing with 'and'
If you followed the hint above, in the second goal, you'll have an 'and' hypothesis
`h₂ : (x = 3) ∧ (x > 0)` in the second goal. You can decompose this hypothesis using something like
`cases h₂ with h₃ h₄`. Here, `h₃ : x = 3` and `h₄ : x > 0`.
-/

namespace exlean


/- Theorem : no-side-bar
Let $f : \mathbb N \to \mathbb N$ be a function. Let $h$ be the assumption that 
$\forall x, f(x + 2) = f(x)$. Then $f(2) = f(0)$ and $f(5) = f(1)$.
-/
theorem all_elim1 (h : ∀ x, f(x + 2) = f(x)) :
(f(2) = f(0)) ∧ (f(5) = f(1)) :=
begin
  split,
  { show f(2) = f(0), from h 0 },
  { have h₂ : f(5) = f(3), from h 3,
    rw h₂,
    from h 1, }  







end


end exlean -- hide