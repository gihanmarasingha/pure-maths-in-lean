import tactic.linarith divisibility.dvd_antisymm  -- hide

/-
# Divisibility

## Level 6: Common divisor basics
-/

namespace exlean -- hide

/-
Let `m, n, and d` be integers. For `d` to be a _common divisor_ of `m` and `n` means that
`d ∣ m` and `d ∣ n`.
-/

def common_divisor (d m n : ℤ) := (d ∣ m) ∧ (d ∣ n)

/-
Using the above definition, we'll show that `5` is a common divisor of `20` and `30`.
-/
example : common_divisor 5 20 30 :=
begin
  split, -- We'll show 1) `5 ∣ 20` and 2) `5 ∣ 30`.
  { use 4,  -- 1) `⊢ 5 ∣ 20`, it suffices to show `20 = 5 * 4`.
    norm_num, }, -- This holds by arithmetic.
  { use 6,  -- 2) `⊢ 30 = 5 * 6`, it suffices to show `⊢ 30 = 5 * 6`.
    norm_num, }, -- This holds by arithmetic.
end

/-
### Tasks

* Adapt the Lean proof above to show that `4` is a common divisor of `48` and `60`.

* Give a handwritten proof of the same result.

-/


/- Theorem : no-side-bar
`4` is a common divisor of `48` and `60`.
-/
theorem four_common_divisor_48_60 : common_divisor 4 48 60 :=
begin
  split,
  { use 12,
    norm_num, },
  { use 15,
    norm_num, },


  
end


end exlean -- hide