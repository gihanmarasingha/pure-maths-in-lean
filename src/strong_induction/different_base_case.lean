import tactic.linarith tactic.ring_exp strong_induction.introduction-- hide

/-
# Strong Induction

## Level 2: Strong induction with a different base case

-/

namespace exlean -- hide

open_locale classical -- hide

open nat -- hide

/-
Often we want to prove that a predicate holds for all sufficiently large natural numbers. Here,
we'll demonstrate that every natural number $n \ge 2$ can be expressed in the form $n = 2 s + 3 t$
for natural numbers $s$ and $t$.

One approach to this is to think of the proof as involving strong induction with a base case of 2.
This approach requires creating a new and more general version of strong induction.

Instead, our approach is to use the ordinary version of strong induction, but where the predicate
asserts $n + 2 = 2 s + 3 t$. Clearly, to prove the result is to prove that this predicate holds
for *every* natural number.

To translate between the original formulation and the new one, we use the result `le_iff_exists_add`.
This asserts `a ≤ n` if and only if `∃ (c : ℕ), n = a + c`.
-/

example (n a: ℕ) : a ≤ n ↔ ∃ (c : ℕ), n = a + c := le_iff_exists_add


/- 
Combining these ideas gives our proof.
-/
example (n : ℕ) (h : 2 ≤ n) : ∃ (s t : ℕ), n = 2 * s + 3 * t :=
begin
  rw le_iff_exists_add at h, -- These two lines adjust the predicate
  rcases h with ⟨c, rfl⟩,     -- for the different base case.
  
  let P := λ x, ∃ (s t : ℕ), 2 + x = 2 * s + 3 * t,
  have base : P 0,
  { use [1, 0],
    norm_num, },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  { assume k : ℕ,
    assume ih : ∀ (m : ℕ), m ≤ k → P m,

    cases k with p,
    { use [0, 1],
      norm_num, },
    have hPp : P p,
    { apply ih p,
      simp only [succ_eq_add_one], 
      linarith, },
    rcases hPp with ⟨s, t, hst⟩,
    use [s + 1, t],
    simp only [succ_eq_add_one, ←add_assoc, hst],
    ring, },
  apply strong_induction base ind_step,
end

/- Theorem : no-side-bar
Every natural number $n$ at least 8 can be expressed as $n = 3s + 5t$ for natural numbers $s$
and $t$.
-/
theorem three_mul_add_five_mul (n : ℕ) (h : 8 ≤ n) : ∃ (s t : ℕ), n = 3 * s + 5 * t :=
begin
  rw le_iff_exists_add at h, -- These two lines adjust for
  rcases h with ⟨c, rfl⟩,     -- the different base case.

  let P := λ x, ∃ (s t : ℕ), 8 + x = 3 * s + 5 * t,
  have base : P 0,
  { use [1, 1],
    norm_num, },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  { assume k : ℕ,
    assume ih : ∀ (m : ℕ), m ≤ k → P m,

    cases k with p,
    { use [3, 0],
      norm_num, },
    cases p with y,
    { use [0, 2],
      norm_num, },
    have hPy : P y,
    { apply ih y,
      simp only [succ_eq_add_one],
      linarith, },
    rcases hPy with ⟨s, t, hst⟩,
    use [s + 1, t],
    simp only [succ_eq_add_one, ←add_assoc, hst],
    ring, },
  apply strong_induction base ind_step,
end


end exlean -- hide