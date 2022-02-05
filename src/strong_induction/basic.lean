import data.nat.basic

namespace exlean

lemma strong_induction {P : ℕ → Prop} (h₁ : P 0)
  (h₂ : ∀ (k : ℕ), (∀ m : ℕ, m ≤ k → P m) → P (nat.succ k)) : ∀ (n : ℕ), P n := λ n,
begin
  apply @nat.strong_induction_on P,
  intro n,
  cases n with x,
  { exact imp_intro h₁, },
  { intro h,
    apply h₂ x,
    simpa [←nat.lt_succ_iff], },
end

end exlean