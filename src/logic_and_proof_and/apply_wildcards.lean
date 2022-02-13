import data.int.basic -- hide

/-
# Logic and Proof (And)

## Level 9: Backward proof and `apply`

### Mixed forward and backward proofs

We've seen two ways to prove $p \land q$.

1. First prove $h_1 : p$ and $h_2 : q$. Applying and introduction to $h_1$ and $h_2$ gives 
the result. In Lean, `and.intro h₁ h₂` is a proof of `p ∧ q` from `h₁` and `h₂`. We use this proof
in `from and.intro h₁ h₂,` to close a goal `p ∧ q`.
2. Apply and introduction immediately to create two new goals: (1) to prove `p` and (2) to prove
`q`. In Lean, we do this via the `split` tactic.

The second approach above is called 'backward' proof.

A third approach is to combine both proof styles.

**Theorem**: Let $p$, $q$, and $r$ be propositions. Suppose $h_1 : p$, $h_2 : q$, and $h_3 : r$.
Then $p \land (q \land r)$.

**Proof**: Applying and introduction with $h_1$, it suffices to prove $q \land r$.
This follows by and introduction on $h_2$ and $h_3$.


The first line of the proof above involves a partial application of and introduction. We provide
and introduction with the first 'argument', $h_1 : p$ and leave, as a new goal, the proof of
$q \land r$.

### The `apply` tactic
-/

/-
The `and.intro` rule takes two arguments: `h₁ : p` and `h₂ : q` and returns a proof of `p ∧ q`.

The `apply` tactic takes any theorem and any number of arguments to that theorem and generates
enough goals to fill in the remaining arguments.

Here is a Lean version of the above proof. We use `apply`, giving `and.intro` the single argument
`h₁`. It remains to prove `q ∧ r`.
-/

variables (p q r : Prop)


example (h₁ : p) (h₂ : q) (h₃ : r) : p ∧ (q ∧ r) :=
begin
  apply and.intro h₁,
  show q ∧ r, from and.intro h₂ h₃,
end

/-
Alternatively, we could provide `apply and.intro` with *no* arguments. We would then
have to prove both goals, much like a `split` proof.
-/

example (h₁ : p) (h₂ : q) (h₃ : r) : p ∧ (q ∧ r) :=
begin
  apply and.intro,
  show p, from h₁,
  show q ∧ r, from and.intro h₂ h₃,
end


/-
If we `apply and.intro` with both arguments, we are effectively doing a `from` proof.
-/

example (h₁ : p) (h₂ : q) (h₃ : r) : p ∧ (q ∧ r) :=
begin
  have h₄ : q ∧ r, from and.intro h₂ h₃,
  apply and.intro h₁ h₄,
end

/-
Consider the following result and its (handwritten) proof.

**Theorem**: Let $p$, $q$, $r$ be propositions. Suppose $h_1 : p$, $h_2 : q$, and $h_3 : r$.
Then $(p \land q) \land r$.

**Proof**: Applying and introduction to $h_3$, it suffices to prove $p \land q$. This follows from
and introduction on $h_1$ and $h_2$.


As a human, you are clever enough to realise that $h_3$ in the proof above is meant to be the
second argument to and introduction.

Computers must be given more precise instructions. Any missing arguments at the front or middle
of an `apply` are indicated with a `_` 'wildcard character.
-/

example (h₁ : p) (h₂ : q) (h₃ : r) : (p ∧ q) ∧ r :=
begin
  apply and.intro _ h₃,
  show p ∧ q, from and.intro h₁ h₂,
end

/- Tactic : apply
`apply`, provided with a theorem name and any number of conditions of the theorem,
opens as many new goals are necessary to fill in proofs of the remaining conditions
of the theorem.
-/

namespace exlean -- hide

/-
### Tasks

1. Replace `sorry` below with a Lean proof, adapting the proof of the example above. Your proof
should use `and.intro` and the `apply` tactic. Use `show` to indicate changes of the goal.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Theorem : no-side-bar
Let $p$, $q$, $r$ be propostions. Suppose $h_1 : p$, $h_2 : q$, and $h_3 : r$. Then
$(p \land (q \land r)) \land p$ follows.
-/
theorem and_intro2 (h₁ : p) (h₂ : q) (h₃ : r) : (p ∧ (q ∧ r)) ∧ p :=
begin
  apply and.intro _ h₁,
  show p ∧ (q ∧ r), apply and.intro h₁,
  show q ∧ r, from and.intro h₂ h₃,

end

end exlean -- hide