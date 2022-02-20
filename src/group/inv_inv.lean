import  group.basic -- hide

/-
# Groups

## Level 1: The group axioms; the inverse of an inverse
-/

/-
A group $(G, \ast)$ is a type (or set) $G$ together with a binary operation $\ast : G \times G \to G$
and a special element $e_G \in G$ satisfying the following properties (called the _group axioms_):
* [identity] for every $a : G$, $a \ast e_G = a$ and $e_G \ast a = a$.
* [associativity] for all $a, b, c : G$, $(a \ast b) \ast c = a \ast (b \ast c)$
* [inverse] for every $a : G$, there exists $b : G$ such that $a \ast b = e_G$ and $b \ast a = e_G$.
-/

/-
### Groups in Lean

In Lean, we write $1$ for the identity element $e_G$ of a group. The symbol `1` here isn't 
(necessarily) the same as the ordinary number $1$.

The group axioms in Lean are the following:
* `mul_one : ∀ (a : G), a * 1 = a`
* `one_mul : ∀ (a : G), 1 * a`
* `mul_assoc : ∀ (a b c : G), (a * b) * c = a * (b * c)`
* `mul_left_inv : ∀ (a : G), a⁻¹ * a = 1` (note `a⁻¹` is typed `a\-1`)

If you forget them, you can refresh your memory using the 'Groups' drop-down in the
'Theorem statements' drop-down menu on the left 

Here are the group axioms in practice.
-/

namespace exlean -- hide

open group -- hide

variables {G : Type*} [group G] {a b c : G} -- hide

/- Axiom : mul_one
(a : G) : a * 1 = a
-/

/- Axiom : one_mul
(a : G) : 1 * a = a
-/

/- Axiom : mul_assoc
(a b c : G) : a * (b * c) = (a * b) * c
-/

/- Axiom : mul_left_inv
(a : G) : a⁻¹ * a = 1
-/

example : a * 1 = a := mul_one a

example : 1 * a = a := one_mul a

example : (a * b) * c = a * (b * c) := mul_assoc a b c

example : a⁻¹ * a = 1 := mul_left_inv a

/-
Together, `mul_one` and `one_mul` are equivalent to the 'normal' group identity axiom; `mul_assoc`
is the same as the normal associativity axiom. The odd-one-out is `mul_left_inv`.

Rather than merely asserting the existence of an inverse of `g`, we name the inverse `g⁻¹`.
Moreover, the `mul_left_inv` axiom only seems to suggest that `g⁻¹` is a left inverse of `g`.
As we'll soon see, the right inverse property can be proved from the other properties.

-/

/-
### Uniqueness of identity

**Theorem**:
Suppose $b$ is an element of $G$ such that for every $a : G, b \ast a = a$,
then $b = 1$.

We'll give a proof 'by calculation'. This is a series of equations, each with its own proof, 
starting with the left-side and ending with the right-side of the desired equation $b = 1$.

**Proof**:
$$
\begin{align}
b &= b \ast 1 && \text{[by identity axiom (mul one)]}\\\\
&= b \ast (b^{-1} \ast b) && \text{[by left inverse]} \\\\
& = (b \ast b^{-1}) \ast b && \text{[by associativity]} \\\\
& = b^{-1} \ast b && \text{[by the hypothesis]} \\\\
& = 1. && \text{[by left inverse]}
\end{align}
$$
∎
-/

/-
The Lean proof of this result is remarkably similar to the handwritten proof:
-/

/- Axiom : eq_one_of_self_mul_eq
(h : ∀ (a : G), b * a = a) : b = 1
-/
lemma eq_one_of_self_mul_eq (h : ∀ (a : G), b * a = a) : b = 1 :=
begin
  calc b = b * 1      : by rw mul_one
  ... = b * (b⁻¹ * b) : by rw mul_left_inv
  ... = (b * b⁻¹) * b : by rw mul_assoc
  ... = b⁻¹ * b       : by rw h
  ... = 1             : by rw mul_left_inv
end

/-
Above, `calc` indicates that we are starting a proof by calculation. The
proof for each line of calculation is shown after the colon.

Consider the following two lines from the proof.
```
  ... = b * (b⁻¹ * b) : by rw mul_left_inv
  ... = (b * b⁻¹) * b : by rw mul_assoc
```
The second line asserts `b = (b⁻¹ * b) = (b * b⁻¹) * b`, the proof of which is: `by rw mul_assoc`
-/

/-
### Tasks

* By hand, write a proof that if $a$ is an element of a group $G$, then $(a^{-1})^{-1} = a$. Use
only the group axoims from Lean (in particular, you may not use the 'right inverse' property).

* Complete the Lean 'proof by calculation' below. I've started you off with a suggested first
line of the proof. You'll need to add intermediate lines and replace all
`sorry`s with proofs. I suggest working from top to bottom, one line at a time. That way, you
can check if your proof is 'structurally correct' as you'll have only a `sorry` warning rather
than an error message after each line.
-/

/- Theorem : 
The inverse of the inverse of $a$ is $a$.
-/
theorem inv_inv : (a⁻¹)⁻¹ = a :=
begin
/- hint
  calc (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1  : by sorry
  ... = a                     : by sorry
-/
  calc (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1  : by rw mul_one
  ... = (a⁻¹)⁻¹ * (a⁻¹ * a)   : by rw mul_left_inv
  ... = ((a⁻¹)⁻¹ * a⁻¹) * a   : by rw mul_assoc
  ... = 1 * a                 : by rw mul_left_inv
  ... = a                     : by rw one_mul
end

end exlean -- hide