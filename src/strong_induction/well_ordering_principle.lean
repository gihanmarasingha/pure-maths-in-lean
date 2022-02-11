import data.set.basic strong_induction.basic -- hide

/-
# Strong Induction

## Level 4: The Well Ordering Principle
-/

namespace exlean -- hide

open_locale classical -- hide

open set nat --hide

/-
In the previous level, we show that if a set $S$ of natural numbers has a minimal element, then
that element is unique.

In this level, you'll show that every non-empty set of natural numbers has a minimal element. The
(challenging) proof requires strong induction.
-/

/-
### Nonempty sets

In Lean, a set `S` is nonempty if `∃ x, x ∈ S`.

As an example, consider the set $\\{x : \mathbb N \mid x ^ 2 + 2x + 15 = 0\\}$. We'll show this set
is nonempty.
-/


example : set.nonempty {x : ℕ | x * x + 2 * x = 15} :=
begin
  use 3,  -- `⊢ 3 ∈ {x : ℕ | x ^ 2 + 2 * x = 15}`
  rw mem_set_of_eq, -- `⊢ 3 ^ 2 + 2 * 3 = 15`
  refl,
end


/- Hint : How to start!
Start with proof by contradiction. Type `by_contra h₁`.
Then push the negation through the quantifiers with `push_neg at h₁`.
-/

/- Hint : How to introduce strong induction
If you've taken the hint above, your goal now will be to prove `false`. This isn't evidently 
something amenable to strong induction!

However, you can show that it suffices to prove `∀ (x : ℕ), x ∉ S` by filling in the sorry below.
```
suffices hs : ∀ (x : ℕ), x ∉ S,
{ sorry, },
```
This leaves you with the goal of proving, by strong induction, that `∀ (x : ℕ), x ∉ S`.
-/

/- Tactic: `tidy`
If a goal can be proved in a fairly straightforward manner from the assumptions, the `tidy` tactic
can sometimes find a proof.
-/

/- Hint : A crucial inequality result
At some point in your proof you may need to use the fact that `m < (succ n) ↔ m ≤ n`. This result
is called `lt_succ_iff`.
-/

/- Theorem :
Every nonempty set of natural numbers has a minimal element.
-/
lemma well_ordering_principle {S : set ℕ} (h : S.nonempty) : ∃ (n : ℕ), min_element n S :=
begin
  by_contra h₁,
  push_neg at h₁,
  suffices hs : ∀ (x : ℕ), x ∉ S,
  { cases h with m hm,
    specialize hs m,
    contradiction, },
  let P := λ x, x ∉ S,
  have base : P 0,
  { intro h₂,
    apply h₁ 0,
    tidy, },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  { assume k : ℕ,
    assume ih : ∀ (m : ℕ), m ≤ k → P m,
    dsimp [min_element] at h₁,
    push_neg at h₁, 
    assume h₂ : k + 1 ∈ S,
    rcases (h₁ (k.succ)) h₂ with ⟨m, h₃, h₄⟩,
    specialize ih m (nat.le_of_succ_le_succ h₄),
    contradiction, },
  apply strong_induction base ind_step,










end


end exlean -- hide