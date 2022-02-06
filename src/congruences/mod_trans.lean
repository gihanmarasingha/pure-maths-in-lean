import congruences.mod_refl_symm -- hide

/-
#  Congruences

## Level 3: Transitivity of mod
-/


namespace exlean -- hide


variables {a b c n : ℤ} -- hide

/-
Your next task is to prove that `≡` is transitive. That is, assuming `a ≡ b [mod n]` and
`b ≡ c [mod n]` to prove `a ≡ c [mod n]`. The clever way to do this is to invoke an appropriate
result you've already seen concerning divisibility. 
-/


/-
### Tasks
* Show that `≡` is a transitive relation.

* Write the same proof by hand.
-/

/- Hint : Starting the problem
Start by rewriting the target and hypotheses with the definition of congruence. Do this with
`rw mod_def at *`.
-/

/- Hint : A clever rewriting
If you took the hint above, the target will be `⊢ n ∣ c - a`. A clever idea is to write
`c - a` as `(c - b) + (b - a)`.

One way to do this is via,
```
have h₃ : c - a = (c - b) + (b - a), by linarith,
rw h₃,
```

Alternatively,
```
rw (show c - a = (c - b) + (b - a), by linarith),
```
The latter approach obviates the need for an additional hypothesis.

After rewriting (by either method), you can use one of the divisibility lemmas (see the sidebar)
to finish the proof.
-/

/- Theorem :
The relation `≡` is transitive.
-/
lemma mod_trans (h₁ : a ≡ b [mod n]) (h₂ : b ≡ c [mod n]) : a ≡ c [mod n] :=
begin
  rw mod_def at *,
  rw (show c - a = (c - b) + (b - a), by linarith),
  apply dvd_add h₂ h₁,




end

end exlean -- hide