import congruences.modeq_zero_iff   -- hide

/-
#  Congruences

## Level 6: Multiplying a congruence on the right
-/


namespace exlean -- hide


variables {a b c n : ℤ} -- hide

/-
### Tasks
* Given `a ≡ b [MOD n]`, show `a * c ≡ b * c [MOD n]`. As in the previous level, you can prove
this using an appropriate divisibilty lemma.

* Write the same proof by hand.
-/

/- Hint : Starting the problem
Start by rewriting the target and hypotheses with the definition of congruence. Do this with
`rw mod_def at *`.
-/

/- Hint : Factoring
The expression `b * c - a * c` in the target can be factored to `(b - a) * c` using the technique
shown in the previous level, namely,
```
rw (show b * c - a * c = (b - a) * c, by linarith),
```

In fact, this factoring result is built in to Lean's mathematical library as the lemma `sub_mul`.
So you could, alternatively, use `rw ←sub_mul`.

After rewriting (by either method), you can use one of the divisibility lemmas (see the sidebar)
to finish the proof.
-/

/- Theorem :
Given `a ≡ b [MOD n]`, the congruence `a * c ≡ b * c [MOD n]` follows.
-/
lemma mod_mul_right (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] :=
begin
  rw mod_def at *,
  rw ←sub_mul,
  apply dvd_mul_of_dvd_left h,







end

end exlean -- hide