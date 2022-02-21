import  group.right_cancellation -- hide

/-
# Groups

## Level 8: Powers
-/


namespace exlean -- hide

open group -- hide

variables {G: Type* } [group G] {a b c : G} {n m : ℕ} -- hide

/-
Exponentiation is defined to be repeated multiplication. That is, if $a$ is an element of a group
$G$, then $a^0 := 1$ and $a^{n + 1} := a \ast a^n$, for a natural number $n$.

The normal 'laws of indices' apply. That is, if $a : G$ and $n, m : \mathbb N$, then:
* $a ^ 0 = 1$,
* $a ^ 1 = a$,
* $1 ^ n = 1$,
* $a ^{n + m} = a ^ n \ast a*m$,
* $a^{nm} = (a ^ n) ^ m$.
-/

/-
### Laws of indices in Lean

Here are the laws of indices in Lean.
* `pow_zero a : a ^ 0 = 1`
* `pow_one a : a ^ 1 = a`
* `one_pow n : 1 ^ n = 1`
* `pow_add a n m : a ^ (n + m) = (a ^ n) * (a ^ m)`
* `pow_mul a n m : a ^ (n * m) = (a ^ n) ^ m`

They can be applied as follows.
-/

/- Axiom : pow_zero
(a : G) : a ^ 0 = 1
-/

/- Axiom : pow_one
(a : G) : a ^ 1 = a
-/

/- Axiom : one_pow
(n : ℕ) : 1 ^ n = 1
-/

/- Axiom : pow_add
(a : G) (n m : ℕ) : a ^ (n + m) = a ^ n * a ^ m
-/

/- Axiom : pow_mul
(a : G) (n m : ℕ) : a ^ (n * m) = (a ^ n) ^ m
-/



example : a ^ 0 = 1 := pow_zero a

example : a ^ 1 = a := pow_one a

example : (1 : G) ^ n = 1 := one_pow n

example : a ^ (n + m) = a ^ n * a ^ m := pow_add a n m

example : a ^ (n * m) = (a ^ n) ^ m := pow_mul a n m


/-
As an example, we'll suppose $a^7 = 1$ and find $q$ and $r$ such that $a^26 = a^{7q + r}$ and
such that $0 \le r < 7$.

**Theorem**: Let $a$ be an element of a group $G$. Suppose $h : a ^ 7 = 1$. Then there exist
natural numbers $q$ and $r$ such that $a ^ {26} = a ^r$, where $0 \le r < 7$.

**Proof**: Take $q$ to be 3 and $r$ to be $5$. We must show both that $a^{26} = a^{7\times 3 + 5}$
and that $0 \le 5 < 7$.

The first part is proved by calculation.
$$
\begin{align}
a^{26} &= a ^ {7 \times 3 + 5} && \text{[trivially]} \\\\
&= (a ^ 7) ^ 3 \ast a ^ 5 && \text{[by laws of indices]} \\\\
&= 1 ^ 3 \ast a ^ 5  && \text{[by $h$]} \\\\
& = a ^ 5. && \text{[by laws of indices and the identity axiom]}
\end{align}
$$
The second part is easily proved.


The same argument can be written in Lean. The `tidy` tactic here proves `0 ≤ 5 ∧ 5 < 7`.
-/

example (h : a ^ 7 = 1) :
∃ (q r : ℕ), a ^ 26 = a ^ r ∧ (0 ≤ r) ∧ (r < 7) :=
begin
  use [3, 5],
  split,
  { calc a ^ 26
        = a ^ (7 * 3 + 5)     : by trivial
    ... = (a ^ 7) ^ 3 * a ^ 5 : by rw [pow_add, pow_mul]
    ... = (1 ^ 3) * a ^ 5     : by rw h 
    ... = a ^ 5               : by rw [one_pow, one_mul] },
  { tidy, },
end

/-
### Tasks

* Complete the Lean proof below, closely following the proof above.

* Write a proof of the same result by hand.

-/


/- Lemma : no-side-bar
If $a ^ 8 = 1$, then there exist natural numbers $q$ and $r$ such that $a ^ {39} = a ^ r$ and
$0 \le r < 8$.
-/
lemma exists_pow_eq_of_poq_eq_one (h : a ^ 8 = 1) :
∃ (q r : ℕ), a ^ 39 = a ^ r ∧ (0 ≤ r) ∧ (r < 8) :=
begin
  use [4, 7],
  split,
  { calc a ^ 39 = a ^ (8 * 4 + 7) : by trivial
    ... = (a ^ 8) ^ 4 * a ^ 7     : by rw [pow_add, pow_mul]
    ... = 1 ^ 4 * a ^ 7           : by rw [h]
    ... = a ^ 7                   : by rw [one_pow, one_mul]  },
  { tidy, },
end 

end exlean -- hide