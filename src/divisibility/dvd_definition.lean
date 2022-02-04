import tactic.ring -- hide

/-
#  Divisibility and Congruences

## Level 1: The definition of divisibility

The notation `x ∣ y` means `∃ (m : ℤ), y = x * m`. Here, the symbol, `∣` is typed `\|` or `\mid`.
-/


namespace exlean -- hide

def myint_dvd : ℤ → ℤ → Prop := λ (x y : ℤ), ∃ (m : ℤ), y = x * m -- hide

/-
If you forget this definition or ever want to replace `x ∣ y` with the definition in a proof, use
the result `dvd_def`.
-/


/- Axiom : dvd_def (x y : ℤ) :
x ∣ y ↔ ∃ (m : ℤ), y = x * m
-/
lemma dvd_def {x y : ℤ} : x ∣ y ↔ ∃ (m : ℤ), y = x * m := by refl -- hide

/-
For example, we will prove that `5 ∣ 10`. In the (unecessary) first line of the proof, we rewrite
`5 ∣ 10` using the definition of divisibility to give `∃ (m : ℤ), 10 = 5 * m`. 

It remains to *find* an `m` that works. Let's use `2`. After that, we must prove `10 = 5 * 2`. But
this follows by definition of multiplication. A `norm_num` proof works.
-/

example : (5 : ℤ) ∣ 10 :=
begin
  rw dvd_def,
  use 2,
  norm_num,
end

/-
If you were to write the proof 'by hand', you might write the following:

> By definition, it suffices to show there exists an integer `m` such that `10 = 5 * m`.
> Take `2` for `m`. Then we must show `10 = 5 * 2`.
> This is true by arithmetic.
-/


/-
### Tasks
* By making a minor variation to the proof above, show that `6 ∣ 72`.

* Write the same proof by hand.
-/


/- Theorem : no-side-bar
`6 divides 72`
-/
theorem six_dvd_seventy_two : (6 : ℤ) ∣ 72 :=
begin
  rw dvd_def,
  use 12,
  norm_num,

  
end

end exlean -- hide