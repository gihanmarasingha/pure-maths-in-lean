import congruences.mod_add-- hide
/-
#  Congruences

## Level 2: Reduction of a congruence
-/

namespace exlean -- hide

/-
Let $x$ and $n$ be integers with $n \ne 0$. One can find an integer $a$ in the range $0 \le a < |n|$ such that $x \equiv a \pmod n$.
This is sometimes called _reduction_ of $x$ modulo $n$.

The statement above has some similarity with the division lemma (see the )
-/

variables {x a n : ℤ} -- hide

/- Theorem :
The relation `≡` is symmetric.
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