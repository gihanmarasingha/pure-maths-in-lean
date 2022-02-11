namespace exlean

lemma strong_induction {P : ℕ → Prop} (h₁ : P 0)
  (h₂ : ∀ (k : ℕ), (∀ m : ℕ, m ≤ k → P m) → P (nat.succ k)) : ∀ (n : ℕ), P n := λ n,
begin
  apply @nat.strong_induction_on P,
  intro n,
  cases n with x,
  { exact λ x, h₁, },
  { intro h,
    apply h₂ x,
    intros m h₃,
    apply h m (nat.succ_le_succ h₃), },
end

def min_element (n : ℕ) (S : set ℕ) := n ∈ S ∧ (∀ (m : ℕ), m ∈ S → n ≤ m)

end exlean