import congruences.condition_for_linear_congruence -- hide

/-
#  Congruences

## Level 12: A linear congruence without a solution
-/

namespace exlean -- hide

variables {x : ℤ} -- hide

/-
It's easy to check that a given value $x$ _is_ a solution of a linear congruence.
-/

example (h : x = 5) : 7 * x ≡ 3 [MOD 4] :=
begin
  rw h, -- `⊢ 7 * 5 ≡ 3 [MOD 4]`
  use -8, -- `⊢ 3 - 7 * 5 = 4 * -8`
  norm_num,
end


/-
It's significantly more difficuult to show that a congruence doesn't have a solution.

In the previous level, you showed that the congruence $ax \equiv \pmod n$ has a solution only if
$d \mid b$, where $d$ is a common divisor of $a$ and $n$.

In this level, you'll use this to show that a certain linear congruence has no solutions.
This boils down to showing that a number doesn't divide another number, a topic we covered in
Division World.
-/

/-
### Task

Using the ideas above and any other lemmas you've seen, show that
there is no $x$ for which  $12 x \equiv 10 \pmod {60}$.
-/

/- Lemma : no-side-bar
The congruence $12 x \equiv 10 \pmod {60}$ has no solution for $x$.
-/
lemma no_soln_12_x_cong_10_mod_60 : ¬ (12 * x ≡ 10 [MOD 60]) :=
begin
  assume h : 12 * x ≡ 10 [MOD 60],
  have h₂ : common_divisor 12 12 60,
  { split; norm_num, },
  have h₃ : 12 * x ≡ 10 [MOD 12], from modeq_of_dvd_of_modeq h₂.2 h,
  have h₄ : (12 : ℤ) ∣ 10,
  { rw ←modeq_zero_iff',
    apply mod_trans,
    swap,
    exact h₃,
    use x,
    linarith, },
  cases h₄ with k h₄,
  suffices h₅ : (k = 0) ∧ ((0 : ℤ) = 10), linarith,
  apply division_unique 10 12;
  tidy,


/-   assume h : 12 * x ≡ 10 [MOD 60],
  cases h with m h,
  have h₁ : 10 = 60 * m + 12 * x, linarith,
  have h₂ : (12 : ℤ) ∣ 10,
  { rw h₁,
    apply dvd_mul_add_mul;
    norm_num, },
  cases h₂ with k h₂,
  suffices h₅ : (k = 0) ∧ ((0 : ℤ) = 10), linarith, 
  apply division_unique 10 12;
  tidy, -/






end

end exlean -- hide