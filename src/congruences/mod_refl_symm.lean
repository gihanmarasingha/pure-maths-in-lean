import congruences.mod_def -- hide

/-
#  Congruences

## Level 3: Reflexivity and symmetry of mod
-/


namespace exlean -- hide


/-
As a first proper theorem on congruences, we'll show that `≡` is a reflexive relation.
-/

variables {a b n : ℤ} -- hide

/- Axiom : mod_refl {a : ℤ} :
a ≡ a [mod n]
-/
lemma mod_refl : a ≡ a [mod n] :=
begin
  rw mod_def, -- `⊢ n ∣ a - a`
  rw dvd_def, -- `⊢ ∃ (m : ℤ), a - a = n * m`
  use 0,      -- `⊢ a - a = n * 0`
  linarith,   -- Follows by algebra.

end

/-
A handwritten proof might be:

> By definition of congruence, it suffices to prove $n \mid a - a$.
> By definition of divisibility, it suffices to prove $a - a = nm$, for some integer $m$.
> Take $m = 0$. Then $a - a = n \times 0$ holds by algebra.
-/

/-
### Tasks
* Show that `≡` is a symmetric relation.

* Write the same proof by hand.
-/

/- Hint : Decomposing a congruence
In the problem below, you are _given_ a congruence `h : a ≡ b [mod n]`. To extract information
from this statement, use the `cases` tactic. 

For example, write `cases h with m h₂` to produce an integer `m` and the hypothesis
`h₂ : b - a = n * m`.
-/

/- Theorem :
The relation `≡` is symmetric.
-/
lemma mod_symm (h : a ≡ b [mod n]) : b ≡ a [mod n] :=
begin
  cases h with m h₂,
  use -m,
  linarith,


end

end exlean -- hide