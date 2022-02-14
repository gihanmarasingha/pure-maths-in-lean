import tactic -- hide

/-
# Variables

## Level 5: Decomposing an exists statement with `cases`
-/

/-
### Decomposing exists statements

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
theorem exists_elim1 (h : ∃ (x : ℤ), f(2 * x) > 5) : ∃ (y : ℤ), f(2 * y - 10) > 5 :=
begin
  cases h with m h₂,
  use m + 5,
  rw (show 2 * (m + 5) - 10 = 2 * m, by linarith),
  from h₂,






end


end exlean -- hide