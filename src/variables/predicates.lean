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


-/

example (X : Type) (P : X → Prop) (h : ∀ (x : X), P(x)) (a : X) :
P(a) :=
begin
  from h a,
end



/-
Previously, you saw how to decompose an exists statement via the cases tactic. If `h` is the 
and if `⊢ r` is the target, then `cases h with h₁ h₂` creates two new goals
(1) to prove `r` under the assumption `h₁ : p` and (2) to prove `r` under the assumption `h₂ : q`.

The `cases` tactic is a simple interface to the more fundamental exists elimination rule.

### Exists elimination

Let $p$, $q$, and $r$ be propositions. Let $h : p ∨ q$, $H_1 : p \to r$, and $H_2 : q \to r$.
Exists elimination on $h$, $H_1$, and $H_2$ gives a proof of $r$


In the last level, we saw how to *prove* an exists statment. What if you're given an 
exists statement? What can you *do* with it?

**Theorem**: Let $f : \mathbb Z \to \mathbb Z$. Let $h$ be the assumption that there exists
an integer $x$ such that $f(x + 2) > 5$. Then there exists an integer $y$ such that $f(y) > 5$.

**Proof**: Decomposing $h$ gives an integer $m$ and the hypothesis $h_2 : f(m + 2) > 5$. 
Take $m + 2$ for $y$. We must show $f(m + 2) > 5$. This follows from $h_2$. ∎

More formally, the statement of the theorem is: suppose $f : \mathbb Z \to \mathbb Z$ and suppose
$h : \exists (x : \mathbb Z), f(x) > 5$. Then $\exists (y : \mathbb Z), f(y + 2) > 5$.

An important observation about the proof above is that the assumption
$h : \exists (x : \mathbb Z), f(x) > 5$ is *not the same* as asserting that $x$ *is* an integer
for which $f(x) > 5$.

The $x$ in the statement $h$ is to be thought of as a 'potential' quantity. We can replace it with
any other variable name. Thus $h$ is *the same* as the assumption 
$\exists (t : \mathbb Z), f(t) > 5$.

When we decompose $h$, we commit to a name for this potential variable (in the proof above, $m$) and
we commit to assertion about $m$ (in the proof above, $h_2 : f(m) > 5$).
-/

/-
### The `cases` tactic

The `cases` tactic performs this decomposition in Lean. Below, `cases h with m h₂` 
replaces `h : ∃ (x : ℤ), f(x + 2) > 5` with `m : ℤ` and `h₂ : f(m + 2) > 5`.
-/

variable (f : ℤ → ℤ)

example (h : ∃ (x : ℤ), f(x + 2) > 5) : ∃ (y : ℤ), f(y) > 5 :=
begin
  cases h with m h₂,
  use m + 2,
  show f(m + 2) > 5, from h₂,
end


/-
### Doing linear arithmetic in Lean

**Theorem**: Let $f : \mathbb Z \to \mathbb Z$. Let $z$ be an integer. Let $h$ be the assumption
that there exists an integer $x$ such that $f(x) > 5$. Then there exists an integer $y$ such that
$f(y + z) > 5$.

**Proof**: Decomposing $h$ gives an integer $m$ and the hypothesis $h_2 : f(m) > 5$. 
Take $m - z$ for $y$. We must show $f((m - z) + z) > 5$. We rewrite this goal, by arithmetic,
to one of showing $f(m) > 5$. This follows from $h_2$.

Note that though one can prove $f((m-z) + z) > 5$ is equivalent to $f(m) > 5$, these two statements
are not identical. It's for this reason that we need to perform arithmetic to show the former
statement can be rewritten as the former.

Lean proves arithmetic results using the tactic `linarith`.
-/

/- Tactic: linarith
`linarith` can prove linear equations and inequalities.
-/

variable (z : ℤ)

example (h : ∃ (x : ℤ), f(x) > 5) : ∃ (y : ℤ), f(y + z) > 5 :=
begin
  cases h with m h₂,
  use m - z,
  rw (show (m - z) + z = m, by linarith),
  from h₂,
end
/-

### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof above. 
2. On a piece of paper, state and give a handwritten proof of this result.
-/

namespace exlean -- hide

/- Theorem : no-side-bar
-/
theorem exists_elim1 (h : ∃ (x : ℤ), f(2 * x) > 5) :
∃ (y : ℤ), f(2 * y - 10) > 5 :=
begin
  cases h with m h₂,
  use m + 5,
  rw (show 2 * (m + 5) - 10 = 2 * m, by linarith),
  from h₂,






end


end exlean -- hide