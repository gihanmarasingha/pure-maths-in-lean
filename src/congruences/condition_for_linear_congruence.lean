import congruences.reduction2  -- hide

/-
#  Congruences

## Level 11: A necessary condition for solving a linear congruence
-/

namespace exlean -- hide

variables {n d a b x : ℤ} -- hide

/-
Suppose $d$ is a common divisor of integers $a$ and $n$. The linear congruence
$a x \equiv b \pmod n$ has a solution only if $d \mid b$.
-/

/-
### Task
Prove the reduction result mentioned above, first by hand and then in Lean.
-/

/- Hint : A useful result
Recall that if $d \mid n$, and $s \equiv t \pmod n$, then $s \equiv t \pmod d$. We called this result
`modeq_of_dvd_of_modeq`.
-/

/- Lemma : 
Suppose $d$ is a common divisor of integers $a$ and $n$. The linear congruence
$a x \equiv b \pmod n$ has a solution only if $d \mid b$.
-/
lemma dvd_of_modeq_mul_of_common_divisor (h₁ : a * x ≡ b [MOD n]) (h₂ : common_divisor d a n) : 
d ∣ b :=
begin
  rcases h₂ with ⟨hda, hdn⟩,
  have h₃ : a * x ≡ b [MOD d], from modeq_of_dvd_of_modeq hdn h₁,
  rw ←modeq_zero_iff',
  have h₄ : 0 ≡ a * x [MOD d],
  { rw modeq_zero_iff', 
    apply dvd_mul_of_dvd_left hda, },
  apply mod_trans h₄ h₃,













end

end exlean -- hide