import tactic.linarith data.set.basic -- hide

/-
# Strong Induction

## Level 1: The Well Ordering Principle

-/

namespace exlean

def min_element (n : ℕ) (S : set ℕ) := n ∈ S ∧ (∀ (m : ℕ), m ∈ S → n ≤ m)

open_locale classical

open set

lemma strong_induction {P : ℕ → Prop} : (∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n) → (∀ k, P k)
:= λ h k, nat.strong_induction_on k h

example (m x : ℕ) : m < x.succ → m ≤ x := nat.lt_succ_iff.mp

lemma strong_induction' {P : ℕ → Prop} (h₁ : P 0)
  (h₂ : ∀ (n : ℕ), (∀ m : ℕ, m ≤ n → P m) → P (nat.succ n)) : ∀ (k : ℕ), P k := λ k,
begin
  apply @nat.strong_induction_on P,
  intro n,
  cases n with x,
  { exact imp_intro h₁, },
  { intro h,
    apply h₂ x,
    simpa [←nat.lt_succ_iff], },
end

example (S : set ℕ) (h : S.nonempty ) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices hs : ∀ (x : ℕ), x ∉ S,
  { cases h with m hm,
    specialize hs m,
    contradiction, },
  apply @strong_induction' (λ x, x ∉ S),
  { intro h₃,
    apply h₁ 0,
    tidy, },
  { dsimp [min_element] at h₁,
    push_neg at h₁, 
    intros k h₂ h₃,
    rcases (h₁ k.succ) h₃ with ⟨m, h₄, h₅⟩,
    exact h₂ m (nat.lt_succ_iff.mp h₅) h₄, },
end

example (S : set ℕ) (h : S.nonempty ) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices hs : ∀ (x : ℕ), x ∉ S,
  { cases h with m hm,
    specialize hs m,
    contradiction, },
  suffices hst : ∀ (n : ℕ), (∀ (m : ℕ), m < n → m ∉ S) → n ∉ S, from strong_induction hst,
  intros y h₂,
  cases y with k,
  { intro h₃,
    apply h₁ 0,
    tidy, },
  { dsimp [min_element] at h₁,
    push_neg at h₁, 
    intro h₃,
    rcases (h₁ k.succ) h₃ with ⟨m, h₄, h₅⟩,
    exact h₂ m h₅ h₄, },
end

example (S : set ℕ) (h : S.nonempty ) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices hs : ∀ (x : ℕ), x ∉ S,
  { cases h with m hm,
    specialize hs m,
    contradiction, },
  suffices hst : ∀ (n : ℕ), (∀ (m : ℕ), m < n → m ∉ S) → n ∉ S, from strong_induction hst,
  intros y h₂,
  cases y with k,
  { intro h₃,
    apply h₁ 0,
    tidy, },
  { specialize h₁ k.succ, 
    rw min_element at h₁,
    push_neg at h₁, 
    intro h₃,
    rcases h₁ h₃ with ⟨m, h₄, h₅⟩,
    exact h₂ m h₅ h₄, },
end

example (S : set ℕ) (h : S.nonempty ) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices h₂ : ∀ (x : ℕ), x ∈ Sᶜ,
  { cases h with m hm,
    specialize h₂ m,
    contradiction, },
  suffices hst : ∀ (n : ℕ), (∀ (m : ℕ), m < n → m ∈ Sᶜ) → n ∈ Sᶜ, from strong_induction hst,
  intros y h₃,
  cases y with k,
  { apply mem_compl,
    intro h₄,
    apply h₁ 0,
    tidy, },
  { apply mem_compl,
    specialize h₁ k.succ,
    rw min_element at h₁,
    push_neg at h₁,
    intro h₂,
    specialize h₁ h₂,
    rcases h₁ with ⟨m, h₄, h₅⟩, 
    specialize h₃ m h₅, 
    contradiction, },
end

example (S : set ℕ) (h : S.nonempty ) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices h₂ : ∀ (x : ℕ), x ∈ Sᶜ,
  { cases h with m hm,
    specialize h₂ m,
    contradiction, },
  apply @strong_induction (λ y, y ∈ Sᶜ),
  intros y h₃,
  cases y with k,
  { apply mem_compl,
    intro h₄,
    apply h₁ 0,
    tidy, },
  { apply mem_compl,
    specialize h₁ k.succ,
    rw min_element at h₁,
    push_neg at h₁,
    intro h₂,
    specialize h₁ h₂,
    rcases h₁ with ⟨m, h₄, h₅⟩, 
    specialize h₃ m h₅, 
    contradiction, },
end

end exlean