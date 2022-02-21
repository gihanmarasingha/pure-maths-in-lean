import group.powers -- hide

/-
# Groups

## Level 9: Negative powers
-/


namespace exlean -- hide

open group -- hide

variables {G: Type* } [group G] {a b c : G} {n m : ℤ} -- hide

/-
We've seen how to define $a ^ n$ where $a$ is a group element and $n$ is a natural number.
We can extend the definition to consider $a ^ m$, where $m$ is an integer.

There are two possibilities:
* $m = n$ for a natural number $n$. We then take $a ^ m := a ^ n$.
* $m = -(n + 1)$ for a natural number $n$. We define $a ^ m = (a ^ (n + 1))^{-1}$.


### Laws of indices in Lean

The laws of indices for integers powers are virtually the same as laws of indices for natural
number powers. Only the names of the results are different.

Taking `n` and `m` to be integers, the laws of indices in Lean are as follows.
* `one_gpow n : 1 ^ n = 1`
* `gpow_add a n m : a ^ (n + m) = (a ^ n) * (a ^ m)`
* `gpow_mul a n m : a ^ (n * m) = (a ^ n) ^ m`

Here they are in action!
-/

/- Axiom : one_gpow
(n : ℤ) : 1 ^ n = 1
-/

/- Axiom : gpow_add
(a : G) (n m : ℤ) : a ^ (n + m) = a ^ n * a ^ m
-/

/- Axiom : gpow_mul
(a : G) (n m : ℤ) : a ^ (n * m) = (a ^ n) ^ m
-/

example : (1 : G) ^ n = 1 := one_gpow n

example : a ^ (n + m) = a ^ n * a ^ m := gpow_add a n m

example : a ^ (n * m) = (a ^ n) ^ m := gpow_mul a n m



/-
As an example, we'll suppose $a^7 = 1$ and find $q$ and $r$ such that $a^{-22} = a^{7q + r}$ and
such that $0 \le r < 7$.

**Theorem**: Let $a$ be an element of a group $G$. Suppose $h : a ^ 7 = 1$. Then there exist
integers $q$ and $r$ such that $a ^ {-20} = a^ {7q + r}$, where $0 \le r < 7$.

**Proof**: Take $q$ to be $-4$ and $r$ to be $6$. We must show both that $a^{-20} = a^{7\times (-4) + 6}$
and that $0 \le 6 < 7$.

The first part is proved by calculation.
$$
\begin{align}
a^{-22} &= a ^ {7 \times (-4) + 6} && \text{[trivially]} \\\\
&= (a ^ 7) ^ (-4) \ast a ^ 6 && \text{[by laws of indices]} \\\\
& = a ^ 6. && \text{[by laws of indices, $h$, and the identity axiom]}
\end{align}
$$
The second part is easily proved.


The same argument can be written in Lean. The `tidy` tactic here proves `0 ≤ 5 ∧ 5 < 7`.
-/

example (h : a ^ (7 : ℤ) = 1) :
∃ (q r : ℤ), a ^ (-22 : ℤ) = a ^ r ∧ (0 ≤ r) ∧ (r < 7) :=
begin
  use [-4, 6],
  split,
  { calc a ^ (-22 : ℤ) = a ^ ((7 : ℤ) * -4 + 6) : by trivial
    ... = a ^ ((7 : ℤ) * -4) * a ^ (6 : ℤ) : by rw gpow_add
    ... = a ^ (6 : ℤ) : by rw [gpow_mul, h, one_gpow, one_mul], },
  { tidy, },
end


/-
In the proof above, note that we need to specify, on occassion, that the quantities we are
presenting to Lean are integers, not natural numbers. We do this with a type annotation. 
For example, `(-22 : ℤ)` is the integer `-22`. If you just type `-22`, Lean will complain that
you can't take negatives of natural numbers!
-/


/-
### Tasks

* Complete the Lean proof below, closely following the proof above. I suggest you copy-and-paste
the proof and make adjustments as necessary.

* Write a proof of the same result by hand.

-/


/- Lemma : no-side-bar
If $a ^ 8 = 1$, then there exist natural numbers $q$ and $r$ such that $a ^ {39} = a ^ r$ and
$0 \le r < 8$.
-/
lemma exists_pow_eq_of_poq_eq_one2 (h : a ^ (8 : ℤ) = 1) :
∃ (q r : ℤ), a ^ (-70 : ℤ) = a ^ r ∧ (0 ≤ r) ∧ (r < 8) :=
begin
  use [-9, 2],
  split,
  { calc a ^ (-70 : ℤ) = a ^ ((8 : ℤ) * (-9) + 2) : by trivial
    ... = a ^ ((8 : ℤ) * -9) * a ^ (2 : ℤ) : by rw gpow_add
    ... = a ^ (2 : ℤ) : by rw [gpow_mul, h, one_gpow, one_mul],  },
  { tidy, },
end 

end exlean -- hide