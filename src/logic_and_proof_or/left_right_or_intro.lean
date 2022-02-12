import data.int.basic -- hide

/-
# Logic and Proof (Or)

## Level 1: Proving or statements

### Left and right or introduction
-/

/-
Let $p$ and $q$ be propositions. The formal statement $p \lor q$
corresponds to the informal statement '$p$ or $q$'.

Thus, $(x > y) \lor (x + y = 5)$ corresponds to '$x > y$ or $x + y = 5$'.

To *prove* an or statement $p \lor q$ is either (1) to prove $p$ or (2) to prove $q$.

These are the two _introduction rules_ for $\lor$. They can be stated more formally.

Let $p$ and $q$ be propositions.
1. Let $h : p$. 'Left or introduction' on $h$ gives a proof of $p \lor q$.
2. Let $h : q$. 'Right or introduction' on $h$ gives a proof of $p \lor q$.

**Theorem**: Let $x$ and $y$ be integers. Suppose $h : x + y = 5$. Then $(x > y) \lor (x + y = 5)$.

**Proof**: The result follows by right or introduction on $h$.
-/

/-
### Or introduction in Lean

The Lean names for left and right or introduction are `or.inl` and `or.inr` respectively.

Suppose `p` and `q` are propositions.
1. Let `h : p`. Then `or.inl h` gives a proof of `p ∨ q`.
2. Let `h : q`. Then `or.inr h` gives a proof of `p ∨ q`.

Below, we have a Lean proof of the previous theorem. The symbol `∨` is typed `\or`.
-/

example (x y : ℤ) (h : x + y = 5) : (x > y) ∨ (x + y = 5) :=
begin
  from or.inr h,
end

/-
Proofs by left or introduction proceed as you might expect.
-/

example (x y : ℤ) (h : x > y) : (x > y) ∨ (x + y = 5) :=
begin
  from or.inl h,
end

namespace exlean -- hide

/-
### Tasks

1. Replace `sorry` below with a one-line Lean proof, adapting the proof of the example above.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

variables (p q r s : Prop)

/- Theorem : no-side-bar
Let $p$, $q$, $r$, and $s$ be propostions. Suppose $h_1 : p$, $h_2 : s$, and $h_3 : r$. Then $r \lor q$ 
follows.
-/
theorem or_intro1 (h₁ : p) (h₂ : s) (h₃ : r) : r ∨ q :=
begin
  from or.inl h₃,

end

end exlean -- hide