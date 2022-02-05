import tactic.linarith divisibility.basic_bezout strong_induction.well_ordering_principle -- hide

/-
# Divisibility

## Level 13: Bézout's lemma
-/

namespace exlean -- hide

open int gcd_set -- hide

variables {a b : ℤ} {k : ℕ} -- hide

open gcd_set -- hide


/-
Let `a` and `b` be integers. Bézout's lemma asserts that there exists an integer `d` such that
`d` is a greatest common divisor of `a` and `b`.

In this level, you'll proof Bézout's lemma via the well-ordering principle. If you haven't already
done so, please try the level on the well-ordering principle from the 'Strong Induction' world.

The proof contains several components. First, we need to consider the set
$\\{y : \mathbb N \mid (0 < y) \land (\exists (s\ t\ : \mathbb Z),\, |a s + b t|  = y)\\}$.

We call this set `set_T a b`. You'll need to use the following lemmas concerning this set.
* `lin_combo_of_min_element`
* `dvd_of_min_element`
* `set_T_nonempty`

The use of these lemmas is shown below.
-/

example (h : min_element k (set_T a b)) : ∃ (x y : ℤ), a * x + b * y = k :=
begin
  exact lin_combo_of_min_element h,
end

/-

-/

example (h : min_element k (set_T a b)) : ↑k ∣ a :=
begin
  exact dvd_of_min_element a b k h,
end


/-

-/
example (h : a ≠ 0) : (set_T a b).nonempty :=
begin
  exact set_T_nonempty h,
end

/-
Over to you!
-/

/- Theorem :
Bézout's lemma. Every pair of integers has a greatest common divisor.
-/
lemma bezout : ∃ (d : ℤ),  greatest_common_divisor d a b :=
begin
  by_cases hzeroa : a = 0,
  { use b,
    rw hzeroa,
    apply greatest_common_divisor_zero, },
  have h : (set_T a b).nonempty := set_T_nonempty hzeroa,
  rcases well_ordering_principle h with ⟨k, hkmin⟩,
  use k,
  split,
  { split,
    { apply dvd_of_min_element a b k hkmin, },
    { apply dvd_of_min_element b a k,
      suffices h₃ : set_T b a = set_T a b,
      { rwa h₃, },
      have h₂ : ∀ (m n : ℤ), set_T m n ⊆ set_T n m,
      { intros m n x hmn,
        rcases hmn with ⟨hxpos, u, v, huv⟩,
        split,
        { exact hxpos },
        { use [v, u],
          rw ←huv,
          congr' 1,
          linarith, }, },
      ext,
      split,
      { apply h₂ b a, },
      { apply h₂ a b, },  },  },
  { intros e hcd,
    rcases lin_combo_of_min_element hkmin with ⟨x, y, hxy⟩,
    rw ←hxy,
    cases hcd with hedvda hedvdb,
    apply dvd_add,
    { apply dvd_mul_of_dvd_left hedvda, },
    { apply dvd_mul_of_dvd_left hedvdb, }, },





















end






end exlean -- hide