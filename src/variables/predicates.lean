import tactic -- hide

/-
# Variables

## Level 6: Predicates
-/

/-
We've informally described 'for all' elimination. We said that if a property holds for every $x$,
then that property holds if a particular value is substituted for $x$.

More concisely, we can use notation to describe the dependence of a property on a variable.

### Predicates
A *predicate* is a function that returns a proposition. 
For example, let $P$ be the predicate on the integers defined by $P(x) := x > 5$. Then $P(10)$ is the proposition
$10 > 5$. Likewise, $P(2)$ is the proposition $2 > 5$.

As another example let $S$ be the predicate on people defined by
$S(x) := x \text{ has red hair}$. Then $S(\text{Prince Harry})$ states that
Prince Harry has red hair.

By using predicate notation, we can state general results about proof.

### For all statements and predicates

Let $Q$ be the predicate defined by $Q(x) := (x - 1) ^ 2 = x ^2 - 2x + 1$.
The statement $\forall (x : \mathbb Z), (x - 1) ^ 2 = x ^2 - 2x + 1$ can be written
concisely as $\forall (x : \mathbb Z), Q(x)$. Suppose $h$ is a proof of
$\forall (x : \mathbb Z), Q(x)$. For all elimination on $h$ and $3$ gives a proof of $Q(3)$, namely
the statement $(3 - 1) ^ 2 = 3 ^ 2 - 2\times3 + 1$.

### For all elimination

More generally, let $X$ be any type of quantity, let $P$ be a predicate on $X$. Let $h$ be a
proof of $\forall (x : X), P(x)$. Let $a$ be a term of type $X$. For all elimination on $h$ and $a$
gives a proof of $P(a)$.

### Predicates and for all elimination in Lean

In Lean `P : X → Prop` indicates that `P` is a predicate on a type `X`.
Given the 'for all' statement `h : ∀ (x : X), P(x)`, given that `a` is a term of type `X`,
we deduce `P(a)`. The proof of this in Lean is simply `h a`.
-/

namespace exlean -- hide

variables (X : Type*) (P Q : X → Prop)

example (h : ∀ (x : X), P(x)) (a : X) : P(a) :=
begin
  from h a,
end

/-
### For all introduction

Let $X$ be a type and let $P$ be a predicate on $X$. The 'for all introduction' rule asserts that
to prove $\forall (x : X), P(x)$ is to assume $x : X$ and derive $P(x)$.

### Combining for all introduction and for all elimination

**Theorem**: Let $P$ and $Q$ be predicates on a type $X$.
Let $h$ be the assumption $\forall (x : X), P(x) \land Q(x)$.
Then $\forall (y : X), Q(y) \land P(y)$.

**Proof**: Assume $y$ : X$. We must show $Q(y) \land P(y)$.
By for all elimination on $h$ and $y$, we have $P(y) \land Q(y)$.
Decomposing this gives $h_1 : P(y)$ and $h_2 : Q(y)$.

We show $Q(y) \land P(y)$ by and introduction on $h_2$ and $h_1$. ∎

Let's do this in Lean.

The line `have : P(y) ∧ Q(y), from h y` introduces a hypothesis
called `this` into the context, where `this : P(y) ∧ Q(y)`.
-/

example (h : ∀ (x : X), P(x) ∧ Q(x)) : ∀ (y : X), Q(y) ∧ P(y) :=
begin
  assume y : X,
  have : P(y) ∧ Q(y), from h y,
  cases this with h₁ h₂,
  show Q(y) ∧ P(y), from and.intro h₂ h₁,
end

/-

### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof above. 
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Theorem : no-side-bar
-/
theorem all_intro_elim2 (h : ∀ (x : X), P(x)) :
∀ (z : X), Q(z) ∨ P(z) :=
begin
  assume z : X,
  have : P(z), from h z,
  from or.inr this,






end


end exlean -- hide