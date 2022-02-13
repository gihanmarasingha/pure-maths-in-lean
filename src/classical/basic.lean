import tactic

open_locale classical

lemma even_iff_not_odd {n : ℤ} : even n ↔ ¬(odd n) :=
begin
  split,
  { rintro ⟨m, hm⟩,
    rintro ⟨k, hk⟩,
    rw hm at hk,
    suffices h : (2 : ℤ) ∣ 1,
    { linarith [int.eq_one_of_dvd_one (show (0 : ℤ) ≤ 2, by linarith) h] },
    use m - k,
    linarith, },
  { dsimp [even, odd],
    intro hnodd,
    push_neg at hnodd,
    have h := int.mod_add_div n 2,
    use n / 2,
    cases (int.mod_two_eq_zero_or_one n) with h₂ h₂,
    { rw [h₂, zero_add] at h, rw h, },
    { exfalso, 
      rw [h₂, add_comm] at h, 
      apply hnodd (n/2),
      rw h, }, },
end

lemma odd_iff_not_even {n : ℤ} : odd n ↔ ¬(even n) := by rw [even_iff_not_odd, not_not]

lemma odd_sq_of_odd {x : ℤ} : (odd x) → (odd (x ^ 2)) :=
begin
  dsimp [odd],
  rintro ⟨m, h⟩,
  use (2 * m ^ 2 + 2 * m),
  rw h,
  ring,
end

example (x : ℤ) : (even (x ^ 2)) → even x :=
begin
  contrapose,
  rw [←odd_iff_not_even, ←odd_iff_not_even],
  apply odd_sq_of_odd,
end

example (x : ℤ) : (even (x ^ 2)) → even x :=
begin
  intro h,
  by_contra h₂,
  simp only [even_iff_not_odd, not_not] at h h₂,
  from h (odd_sq_of_odd h₂),
end

example {x : ℤ} : even (x ^ 2) → even x :=
begin
  intro h,
  by_cases h₂ : even x,
  { from h₂, },
  { exfalso,
    simp only [even_iff_not_odd, not_not] at h h₂,
    from h (odd_sq_of_odd h₂), }
end