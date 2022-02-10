import divisibility.division strong_induction.minimal_element

namespace exlean 

open int 

variables {a b : ℤ} {k : ℕ}

namespace gcd_set 

def set_T (a b : ℤ) := {y : ℕ | 0 < y ∧ ∃ (s t : ℤ), nat_abs (a * s + b * t)  = y}

lemma lin_combo_of_min_element (h : min_element k (set_T a b)) : ∃ (x y : ℤ), a * x + b * y = k :=
begin
  rcases h with ⟨⟨hkpos, s, t, hst⟩, hkmin⟩,
  rw nat_abs_eq_iff at hst,
  cases hst,
  { use [s, t],
    exact hst, },
  { use [-s, -t],
    linarith, },
end

lemma dvd_of_min_element (a b : ℤ) (k : ℕ) (h : min_element k (set_T a b)) : ↑k ∣ a :=
begin
  rcases lin_combo_of_min_element h with ⟨x, y, hxy⟩,
  rcases h with ⟨⟨hkpos, hst⟩, hkmin⟩,
  clear hst,
  rcases division a k (show (k : ℤ) ≠ 0, by linarith) with ⟨q, r, hqr, hrnonneg, hrlt⟩,
  by_cases hrzero : r = 0,
  { use q,
    rw [hqr, hrzero, add_zero], },
  exfalso,
  have hrinT : r.nat_abs ∈ set_T a b,
  { rw [set_T, set.mem_set_of_eq],
    split,
    { apply nat_abs_pos_of_ne_zero hrzero,  },
    { use [1 - x * q, - y * q],
      congr,
      rw [(show r = a - k * q, by linarith), ←hxy],
      linarith, }, },
  specialize hkmin (nat_abs r) hrinT,
  have : nat_abs r < k,
  { rw ←nat_abs_of_nat k, 
    apply nat_abs_lt_nat_abs_of_nonneg_of_lt hrnonneg, 
    rwa coe_nat_abs at hrlt, },
  linarith, 
end

lemma set_T_nonempty (h : a ≠ 0) : (set_T a b).nonempty :=
begin
  use nat_abs a,
  rw [set_T, set.mem_set_of_eq],
  split,
  { apply nat_abs_pos_of_ne_zero h, },
  use [1, 0],
  rw [mul_one, mul_zero, add_zero],
end

end gcd_set

lemma nonneg_or_nonneg_neg' (a : ℤ) : (0 ≤ a) ∨ (0 ≤ -a) :=
begin
  by_cases h : 0 ≤ a,
  { left, exact h, },
  { right,
    linarith, },
end

end exlean 