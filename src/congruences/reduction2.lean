import congruences.mod_reduction -- hide
/-
#  Congruences

## Level 10: Reduction of integers in general
-/

namespace exlean -- hide

/-
We now return to the other meaning of reduction. You will show that for all integers $x$ and $n$
with $n \ne 0$, there exists an integer $a$ in the range $0 \le a < |n|$ such that
$x \equiv a \pmod n$.

The statement above has some similarity with the `division` lemma, as seen in Divisibility World.
-/

variables {x a n : ℤ} -- hide

/- Theorem :
For every non-zero integer $n$, there exists an integer $a$ such that $x \equiv a \pmod n$ with
$0 \le a < |n|$.
-/
lemma reduction (h : n ≠ 0) : ∃ (a : ℤ), (x ≡ a [MOD n]) ∧ (0 ≤ a) ∧ (a < abs n) :=
begin
  rcases (division x n h) with ⟨m, r, hn, hrange⟩,
  use r,
  split,
  { rw hn,
    have h₂ : n * m + r ≡ 0 + r [MOD n],
    { apply mod_add,
      { use -m,
        linarith, },
      { apply mod_refl, }, },
    rwa zero_add at h₂, },
  exact hrange,










end

end exlean -- hide