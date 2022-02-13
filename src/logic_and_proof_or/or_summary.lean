import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 7: Or summary
-/

/-
### Introduction and elimination

The $\lor$ symbol is defined by two principles.

1. Or introduction. Let $p$ and $q$ be propostions.
    * Left or introduction on $h : p$ gives a proof of $p \lor q$.
    * Right or introduction on $h : q$ gives a proof of $p \lor q$.
2. Or elimination. Let $p$, $q$, and $r$ be propositions. Let $h : p \lor q$, $h_1 : p$, and
$h_2 : q$. Then or elimination on $h$, $h_1$, and $h_2$ gives a proof of $r$.

In Lean, the principles are as follows.

1. Or introduction. Let `p` and `q` be propositions.
    * Let `h : p`. Then `or.inl h` is a proof of `p ∨ q`.
    * Let `h : q`. Then `or.inr h` is a proof of `p ∨ q`.
2. Or elimination. Let `p`, `q`, and `r` be propositions. Let `h : p ∨ q`, `h₁ : p → r`, and
`h₂ : q → r`. Then `or.elim h h₁ h₂` is a proof of `r`.

### Or tactics

Using the `left`, `right`, and `cases` tactics, we can write backward proofs involving `∨`.

1. Or introduction. Let `p` and `q` be propositions. Suppose `⊢ p ∨ q` is the target.
    * `left` changes the goal to `⊢ p`.
    * `right` changes to goal to `⊢ q`.
2. Let `p`, `q`, `r` be propositions. Suppose `h : p ∨ q`. If the target is `⊢ r`, then
`cases h with h₁ h₂` replaces the current goal with two new goals:
    a. A goal in which `h` has been replaced with `h₁ : p` and
    b. a goal in which `h` has been replaced with `h₂ : q`.
In both cases the target remains as `⊢ r`.

### `apply`, `rw`, `norm_num`, `assume`

* `apply` is a general-purpose tactic for writing mixed forward / backward proofs. Supply
`apply` with the name of a theorem, some conditions for the theorem, and a suitable number of
wildcards. Lean will either close the goal or open enough new goals to account for the missing
conditions.
* `rw` is used for substitutions. For example, if `h : x = 5` and `⊢ x + y = 6`, then
`rw h` will change the target to `⊢ 5 + y = 6`.
* `norm_num` proves numerical goals, such as `5 * 7 + 4 = 39`.
* `assume` is used in proving implications. To prove `p → q` is to first `assume h : p` and then
derive `q` on this assumption.
-/

namespace exlean -- hide

/-
We end this world with a challenge question that will test your understanding of all the rules
of introduction and elimination for `∧` and `∨`.

### Tasks

1. Replace `sorry` below with a Lean proof.
2. On a piece of paper, state and give a handwritten proof of this result.
3. (Bonus) What's the shortest Lean proof you can write? What proof is most readable? Can you
explain your proof to your friends?
-/

variables (p q r : Prop)

/- Theorem : no-side-bar
Let $p$ and $q$. Suppose $h : p \lor q$. Then $q \lor p$ follows.
-/
theorem or_and_mastery : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
/-   assume h : p ∧ (q ∨ r),
  cases h with hp hqr,
  cases hqr with hq hr,
  { left,
    from and.intro hp hq, },
  { right,
    from and.intro hp hr, }, -/

/-   assume h : p ∧ (q ∨ r),
  cases h.right with hq hr,
  { from or.inl (and.intro h.left hq), },
  { from or.inr (and.intro h.left hr), }, -/

  
  from assume h, or.elim h.right (assume hq, or.inl (and.intro h.left hq)) (assume hr, or.inr (and.intro h.left hr)),



end

end exlean -- hide