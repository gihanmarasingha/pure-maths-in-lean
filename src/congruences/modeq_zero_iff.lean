import congruences.mod_trans -- hide

/-
#  Congruences

## Level 5: A condition for an integer to be congruent to zero
-/


namespace exlean -- hide


variables {a n : ℤ} -- hide

/-
### Tasks
* Let $a$ and $n$ be integers. Prove, by hand, that $0 \equiv a \pmod n$ if and only if $n \mid a$.


* Write the same proof in Lean.
-/


/- Lemma :
Let $a$ be an integer. Then $0 \equiv a \pmod n \iff n \mid a$.
-/
lemma modeq_zero_iff' : 0 ≡ a [MOD n] ↔ n ∣ a :=
begin
  rw [mod_def, sub_zero],










end

end exlean -- hide