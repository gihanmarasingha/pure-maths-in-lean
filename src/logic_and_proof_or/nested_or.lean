import data.int.basic -- hide

/-
# Logic and Proof (Or)

## Level 2: Nested or introduction
-/

/-
**Theorem**: Let $a$ and $b$ be integers. Suppose $h : a = b$. Then
$(a = 5) \lor ((a=b) \lor (a=7))$.

**Proof**: We have $h_2 : (a=b)\lor (a=7)$ from left or introduction on $h$.
We show $(a = 5) \lor ((a=b) \lor (a=7))$ from right or introduction on $h_2$.
-/

/-
The same proof is represented in Lean below.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  have h₂ : (a = b) ∨ (a = 7), from or.inl h,
  show (a = 5) ∨ ((a = b) ∨ (a = 7)), from or.inr h₂,
end

/-
For a more succinct proof, we can skip the intermediate derivation of $(a=b) \lor (a=7)$.

**Proof**: The result follows by right or introduction applied to the result of
left or introduction on $h$.

This proof is shorter, but less readable. Here it is in Lean.
-/

example (a b : ℤ) (h : a = b) : (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  from or.inr (or.inl h)
end



namespace exlean -- hide

/-
### Tasks

1. Replace `sorry` below with a Lean proof, using `have` to produce an intermediate proof. Recall
that `∨` is typed `\or`.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) Give a one-line proof of the result.
-/

variables (p q : Prop)

/- Theorem : no-side-bar
Let $p$ and $q$ be propostions. Suppose $h : q$. Then $(p \lor q) \lor p$ follows.
-/
theorem nested_or1 (h : q) : (p ∨ q) ∨ p :=
begin
  have h₁ : p ∨ q, from or.inr h,
  from or.inl h₁,


end

end exlean -- hide