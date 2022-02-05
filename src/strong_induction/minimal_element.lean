import data.set.basic strong_induction.different_base_case -- hide

/-
# Strong Induction

## Level 3: Minimal elements
-/

namespace exlean -- hide

/-
Let $S$ be a set of natural numbers. A natural number $n$ is said to be a _minimal element_ of $S$
if $n \in S$ and for every every $m \in S$, $n \le m$.
-/

def min_element (n : ℕ) (S : set ℕ) := n ∈ S ∧ (∀ (m : ℕ), m ∈ S → n ≤ m)

namespace min_element_example -- hide

/-
Let the function $f : \mathbb N \to \mathbb N$ be given by $f(x) = 5 x + 7$ and let $T$ be the set
of natural numbers $x$ for which $f(x) \ge 400$.
-/

def f (x : ℕ) := 5 * x + 7

def T : set ℕ := {x : ℕ | f x ≥ 400}

/-
We'll show that $79$ is a minimal element of $T$. To do this, we split the target into two goals:
1. to prove $79 \in T$ and
2. to prove that every element of $T$ is at least $79$.
-/

example : min_element 79 T :=
begin
  split, 
  { dsimp [T, f], -- We must show `5 * 79 + 7 ≥ 400`.
    norm_num, }, -- This follows by arithmetic.
  { dsimp [T, f], -- `⊢ ∀ (m : ℕ), 5 * m + 5 ≥ 400 → 79 ≤ m`.
    assume m : ℕ,
    assume h : m ∈ T,
    linarith, },
end

end min_element_example -- hide

variables {S : set ℕ} {x y : ℕ} -- hide

/-
### Task

Prove uniquenss of minimal element. For this level, you won't need induction.
-/

/- Hint : A useful lemma on inequalities
The Lean lemma `le_antisymm` asserts that `x = y` follows given `x ≤ y` and `y ≤ x`.
-/

/- Theorem : 
If a set $S$ of natural numbers has a minimal element, then that element is unique.
-/
lemma min_element_unique (h₁ : min_element x S) (h₂ : min_element y S) : x = y :=
begin
  cases h₁ with hxin hxmin,
  cases h₂ with hyin hymin,
  apply le_antisymm,
  { exact hxmin y hyin, },
  { exact hymin x hxin, },









end



end exlean -- hide