import tactic.linarith .dvd_definition -- hide

/-
#  Divisibility and Congruences

## Level 2: A multiplication lemma

-/

namespace exlean --hide

/-
In the last level, you *proved* a divisibility statement. In this level, you'll *decompose* given
divisibility statements.

To prove a statement of the form `x ∣ y` is to prove an existentially-quantified statement, by
exists introduction (the `use` tactic in Lean).

On the other hand, a given divisibility statement `h : a ∣ b` represents the
existentially-quantified statement `h : ∃ (m : ℤ), b = a * m`. We decompose this to an integer `k`
and a hypothesis `h₂ : b = a * k` via `cases h with m h₂`. In handwritten mathematics, this
is exists elimination.
-/


/-
### An addition result

Below, I present a proof that given `h₁ : a ∣ b` and `h₂ : a ∣ c`, then `a ∣ b + c` follows.
-/

/- Axiom : dvd_add (a b c : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) :
a ∣ b + c
-/
theorem dvd_add (a b c : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
begin
  cases h₁ with m₁ h₃, -- We have `m₁ : ℤ` and `h₃ : b = a * m₁`.
  cases h₂ with m₂ h₄, -- We have `m₂ : ℤ` and `h₄ : c = a * m₂`.
  rw dvd_def, -- `⊢ ∃ (m : ℤ), b + c = a * m`.
  use (m₁ + m₂), -- Take `m₁ + m₂` for `m`.
  rw [h₃, h₄], -- From `h₃` & `h₄`, `⊢ a * m₁ + a * m₂ = a * (m₁ + m₂)`.
  linarith, -- This holds by algebra.
end


/-
Extracing the comments from the above gives a handwritten proof:

> We have `m₁ : ℤ` and `h₃ : b = a * m₁`.
>
> We have `m₂ : ℤ` and `h₄ : c = a * m₂`.
>
> We must show `∃ (m : ℤ), b + c = a * m`.
>
> Take `m₁ + m₂` for `m`. We must show `b + c = a * (m₁ + m₂)`.
>
> From `h₃` and `h₄`, we must show `a * m₁ + a * m₂ = a * (m₁ + m₂)`.
>
> This holds by algebra.
-/

/-
### Tasks
* Adapting the Lean proof above, show that if `h₁ : a ∣ b` and `h₂ : c ∣ d`, then
`a * c ∣ b * d`.

* Write the same proof by hand.
-/


/- Theorem :
Let `a, b, c, d` be integers. Given `h₁ : a ∣ b` and `h₂ : c ∣ d`, we have `a * c ∣ b * d`.
-/
theorem mul_dvd_mul {a b c d : ℤ} (h₁ : a ∣ b) (h₂ : c ∣ d) : a * c ∣ b * d :=
begin
  cases h₁ with m₁ h₁,
  cases h₂ with m₂ h₂,
  rw dvd_def,
  use (m₁ * m₂),
  rw [h₁, h₂],
  ring,




end

end exlean -- hide