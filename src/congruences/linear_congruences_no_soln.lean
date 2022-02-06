import congruences.mod_mul -- hide

/-
#  Congruences

## Level 8: Linear congruences without solutions
-/

namespace exlean -- hide

variables {a b c d n x : ℤ} -- hide

/-
Given $a$, $b$, and $n$, how do you _solve_ the congruence $ax \equiv b \pmod n$? 

First, note it's easy to check that a given value $x$ _is_ a solution.
-/

example (h : x = 5) : 7 * x ≡ 3 [MOD 4] :=
begin
  rw h, -- `⊢ 7 * 5 ≡ 3 [MOD 4]`
  use -8, -- `⊢ 3 - 7 * 5 = 4 * -8`
  norm_num,
end

/-
It's harder to show that a value $x$ is _not_ a solution of a congruence. This boils down to showing
that a number doesn't divide another number. 

Here, we'll show $5 \nmid 62$. To do this by hand, let's assume that $5 \mid 62$. Thus,
$62 = 5m$, for some integer $m$. We write $62 = m \times 5 + 0$ and $62 = 12 \times 5 + 2$.

From the uniqueness of division theorem theorem, the quotients and remainders in this expression
must be equal. That is, $m = 12$ and $0 = 2$. This is a contradiction, as $0 \ne 2$.

Below, we give the same proof in Lean.
-/

example : ¬ ((5 : ℤ) ∣ 62) :=
begin
  assume h : (5 : ℤ) ∣ 62,
  cases h with m hm,
  have h₁ : 62 = m * 5 + 0, linarith,
  have h₂ : (62 : ℤ) = 12 * 5 + 2, norm_num,
  
  have k₁ : m = 12 ∧ (0 : ℤ) = 2,
  { apply division_unique 62 5;
    tidy, },
  linarith,
end




/- Lemma : no-side-bar
The congruence $12 x \equiv 10 \pmod {60}$ has no solution for $x$
-/
lemma no_soln_12_x_cong_10_mod_60 (x : ℤ) : ¬ (12 * x ≡ 10 [MOD 60]) :=
begin
  rw [mod_def, dvd_def],
  assume h,
  cases h with m hm,
  have h : 10 = 60 * m + 12 * x, linarith,
  rcases (bezout 60 12) with ⟨d, s, t, h₁, h₂⟩,
  sorry,







end

end exlean -- hide