import congruences.mod_refl_symm -- hide

/-
#  Congruences

## Level 4: Transitivity of mod
-/


namespace exlean -- hide


variables {a b c d n : ℤ} -- hide

/-
Your next task is to prove that `≡` is transitive. That is, assuming `a ≡ b [MOD n]` and
`b ≡ c [MOD n]` to prove `a ≡ c [MOD n]`. The clever way to do this is to invoke an appropriate
result you've already seen concerning divisibility. 
-/

/-
As an example of the kind of technique you'll need, we'll show a proof that $a \mid b + 2c + d$
given $h_1 : a \mid b + c$ and $h_2 : a \mid c + d$.

First we note $h_3 : b + 2c + d = (b + c) + (c + d)$. Rewriting with $h_3$, the goal becomes
$\vdash a \mid (b + c) + (c + d)$. Applying the 'addition of divisibility' result, it suffices
to prove two new goals (1) $a \mid b + c$ and (2) $a \mid c + d$. The first of these goals follows
from $h_1$ and the second from $h_2$.

Note the use of the `apply` tactic to construct new goals from the conditions of the `dvd_add`
theorem.
-/

/- Tactic : apply
Most theorems have conditions under which they hold. For example, `dvd_add` states that
`a ∣ b + c` given the conditions `a ∣ b` and `a ∣ c`. If the target is `⊢ a ∣ b + c`, then
typing `apply dvd_add` creates two new goals: (1) to prove `a ∣ b` and (2) to prove `a ∣ c`.

The use of `apply` can be shortened. If the hypotheses `h₁ : a ∣ b` and `h₂ : a ∣ c` are in the
context, then the target `a ∣ b + c` can be proved with `apply h₁ h₂`.
-/

example (h₁ : a ∣ b + c) (h₂ : a ∣ c + d) : a ∣ b + 2 * c + d :=
begin
  have h₃ : b + 2 * c + d = (b + c) + (c + d), linarith,
  rw h₃,
  apply dvd_add,
  { exact h₁ },
  { exact h₂ },
end

/-
We can prove the same result more briefly by (a) dispensing with additional hypothesis `h₃` and
rewriting 'in place' via 'show' and (b) giving `apply` the desired conditions without the need
to introduce additional goals.
-/

example (h₁ : a ∣ b + c) (h₂ : a ∣ c + d) : a ∣ b + 2 * c + d :=
begin
  rw (show b + 2 * c + d = (b + c) + (c + d), by linarith),
  apply dvd_add h₁ h₂,
end



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

One way to do this is via:
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
lemma mod_trans (h₁ : a ≡ b [MOD n]) (h₂ : b ≡ c [MOD n]) :
a ≡ c [MOD n] :=
begin
  rw mod_def at *,
  rw (show c - a = (c - b) + (b - a), by linarith),
  apply dvd_add h₂ h₁,




end

end exlean -- hide