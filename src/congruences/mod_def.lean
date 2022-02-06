import divisibility.euclid_basic -- hide

/-
#  Congruences

## Level 1: The definition of congruence

The notation `a ≡ b [mod n]`, read '`a` is congruent to `b` modulo `n`' means `n ∣ b - a`. 

Type `≡` as `\==`.
-/


namespace exlean -- hide

def modeq (n a b : ℤ) := n ∣ b - a  -- hide

notation a ` ≡ `:50 b ` [mod `:50 n `]`:0 := modeq n a b -- hide

/-
If you forget this definition or ever want to replace `a ≡ b [mod n]` with the definition in a proof, use
the result `mod_def`.
-/

variables {a b n : ℤ} -- hide

/- Axiom : mod_def (x y : ℤ) :
a ≡ b [mod n] ↔ n ∣ b - a
-/
lemma mod_def : a ≡ b [mod n] ↔ n ∣ b - a := by refl -- hide

/-
For example, we will prove that `45 ≡ 17 [mod 7]`. The first two lines of the proof are
unnecessary but may be helpful in understanding how to apply definitions.#check

In the first line, we rewrite `⊢ 45 ≡ 17 [mod 7]` using the definition of congruence to give
`⊢ 7 ∣ 45 - 17`. Using the definition of divisibility, this becomes `⊢ ∃ (m : ℤ), 45 - 17 = 7 * m`.

To prove this existentially-quantified statement, we take `m` to be `4`. The result follows by
arithmetic.
-/

example : 17 ≡ 45 [mod 7] :=
begin
  rw mod_def, -- `⊢ 7 ∣ 45 - 17`
  rw dvd_def, -- `⊢ ∃ (m : ℤ), 45 - 17 = 7 * m`
  use 4,      -- `⊢ 45 - 17 = 7 * 4`
  norm_num,   -- This holds by arithmetic.
end

/-
If you were to write the proof 'by hand', you might write the following:

> By definition, we must prove `7 ∣ 45 - 17`. That is, that `45 - 17 = 7 * m`, for some `m`.
> This holds if one takes `m` to be `4`.
-/

/-
### Tasks
* By making a minor variation to the proof above, show that `60 ≡ 38 [mod 11] `.

* Write the same proof by hand.
-/

/- Theorem : no-side-bar
`60 ≡ 38 [mod 11]` 
-/
theorem sixty_cong_37_mod_11 : 60 ≡ 38 [mod 11] :=
begin
  use (-2),
  norm_num,



  
end

end exlean -- hide