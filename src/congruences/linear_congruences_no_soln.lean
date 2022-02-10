import congruences.mod_mul -- hide

/-
#  Congruences

## Level 8: Linear congruences without solutions
-/

namespace exlean -- hide

variables {x : ℤ} -- hide

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
that a number doesn't divide another number, a topic we covered in Division World.
-/

/-
### Task

Using the ideas above and any other lemmas you've seen, show that
there is no $x$ for which  $12 x \equiv 10 \pmod {60}$.
-/

/- Lemma : no-side-bar
The congruence $12 x \equiv 10 \pmod {60}$ has no solution for $x$
-/
lemma no_soln_12_x_cong_10_mod_60 : ¬ (12 * x ≡ 10 [MOD 60]) :=
begin
  assume h : 12 * x ≡ 10 [MOD 60],
  cases h with m h,
  have h₁ : 10 = 60 * m + 12 * x, linarith,
  have h₂ : (12 : ℤ) ∣ 10,
  { rw h₁,
    apply dvd_mul_add_mul;
    norm_num, },
  cases h₂  with k h₂,
  suffices h₅ : (k = 0) ∧ ((0 : ℤ) = 10), linarith, 
  apply division_unique 10 12;
  tidy,



















end

end exlean -- hide