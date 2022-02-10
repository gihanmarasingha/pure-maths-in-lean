import tactic.linarith divisibility.common_divisors  -- hide

/-
# Divisibility

## Level 11: Common divisor results
-/

namespace exlean -- hide

/-
### Tasks

In this level, you'll *decompose* the hypothesis that `d` is a common divisor of `a` and `b` to
prove that `c` is a common divisor of `a` and `b`, under the hypothesis that `c ∣ d`.

As `common_divisor d a b` is a conjunctive (an 'and') statement, it can be decomposed into
its constituent parts using the `cases` tactic. See the example below.
-/

variables {d a b c s t : ℤ} -- hide


example (h₁ : common_divisor d a b) : common_divisor d a (a * s + b * t) :=
begin
  rw common_divisor at h₁, -- `h₁ : (d ∣ a) ∧ (d ∣ b)`
  cases h₁ with hda hdb, -- `hda : d ∣ a`, `hdb : d ∣ b`.
  rw common_divisor, -- `⊢ (d ∣ a) ∧ (d ∣ a * s + b * t)`
  split, -- 2 goals: (1) `⊢ d ∣ a` and (2) `⊢ d ∣ a * s + b * t`.
  { exact hda, }, -- (1) follows from `hda`
  { apply dvd_mul_add_mul hda hdb, }, -- (2) follows from
  -- our previous result on divisibility of linear combinations.
end

/- Theorem : no-side-bar
Given `d` is a common divisor of `a` and `b` and given `c ∣ d`, we have `c` is a common divisor of
`a` and `b`.
-/
theorem common_divisor_of_common_divisor_of_dvd
(h₁ : common_divisor d a b) (h₂ : c ∣ d) : common_divisor c a b :=
begin
  cases h₁ with hda hdb,
  split,
  { apply dvd_trans h₂ hda, },
  { apply dvd_trans h₂ hdb },  

  






  
end


end exlean -- hide