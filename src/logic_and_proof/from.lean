import data.int.basic -- hide

/-
# Logic and Proof

## Level 1: Theorems and `from`

### Theorem statements, hypotheses, targets, proofs

As a student of higher mathematics, your main task is to prove theorems.

A theorem consists of two parts: (1) a statement of a mathematical result and (2) a proof of
that result.

Pythagoras' Theorem states: let  $T$ be a right-angled triangle, let $a$, $b$, $c$ be the
side-lengths of $T$, and let $c$ be the length of the hypotenuse. Then  $a^2 + b^2 = c ^2$.

In this theorem statement, the *hypotheses* are:
* $T$ is a right-angled triangle,
* $a$, $b$, $c$ are the side lengths of $T$,
* $c$ is the length of the hypotenuse.

Every theorem statement also has a *target*. In Pythagoras' Theorem, the target is:
* $\vdash a^2 + b^2 = c ^2$.
The symbol $\vdash$ is read 'to prove'.

At every point in the proof, you have a *goal*. The goal is to prove the target in the context
of the given hypotheses. The goal can change through the course of a proof.

### Easy proofs

In the simplest of theorems, the target is one of the hypotheses.

**Theorem**: Let $x$ be an integer. Suppose $h_1 : x > 0$ and $h_2 : x ^ 2 = 16$. Then $x ^ 2 = 16$.

In the theorem statement above, the target $\vdash x ^ 2 = 16$ can be deduced immediately from the
hypothesis I have labelled $h_2$. You can write the proof as follows:

**Proof**: The result follows from $h_2$.

### Easy proofs in Lean using `from`

We'll use the proof assistant Lean to write mathematical proofs. In the example below, the
hypotheses are:
* `x : ℤ`, that $x$ is an integer. Here, `ℤ` is typed `\int`.
* `h₁ : x > 0`, that $x > 0$. Note `h₁` is typed `h\1`.
* `h₂ : x ^ 2 = 16`, that $x^2 = 16$.

The target is to prove
* `x ^ 2 = 16`.

The proof is the single line:
* `from h₂,`

This corresponds to the handwritten proof, 'The result follows from $h_2$'. Here, `from` is
an example of a Lean 'tactic'. Tactics are computer programmes that help in proving theorems.
On the left pane is a drop-down menu of all tactics seen so far in this game.
-/

/- Tactic : from
If one of the hypothesis `h` matches the target, then `from h` will close the goal.

`from` is a synonym for the tactic `exact`.
-/

/- Tactic : exact
If one of the hypothesis `h` matches the target, then `exact h` will close the goal.
-/

example (x : ℤ) (h₁ : x > 0) (h₂ : x ^ 2 = 16) : x ^ 2 = 16 :=
begin
  from h₂,
end

namespace exlean -- hide

/-
### Task

Now it's your turn!

1. If you see the text 'Lean is busy...' in the upper-right hand pane, please
wait until Lean downloads.
2. In the lower-right hand pane, you'll see a warning message,
'declaration exlean.easy_proof uses `sorry`'. This is normal. It indicates that we haven't yet
written a proper proof.
3. Below, you'll see a theorem statement and (between the words `begin` and `end`), a `sorry` proof.
We use `sorry` to plug gaps in an incomplete proof.
4. Delete the word `sorry`. You'll get an error message. Don't worry this just means we don't have
a proof.
5. In the upper-right pane, you'll now see the *goal*. This consists of the hypotheses `x y : ℤ`,
`h₁ : x + y = 3`, `h₂ : x < 0`, `h₃ : x * y = -10`, and the target, `⊢ x + y = 3`.
6. **Write a one-line proof** of the target, adapting the proof above. Recall `h₂` is typed as `h\2`.
Don't forget the comma! On a piece of paper, state the theorem and give a 'handwritten' proof,
following the example above.
7. If everything went well, you'll see the text 'Proof complete!' in the upper-right pane.
8. Click 'Next level' in the top pane to proceed to the next level.
-/

/- Theorem : no-side-bar
Let $x$ and $y$ be integers. Suppose $h_1 : x + y = 3$, $h_2 : x < 0$, and $h_3 : x y = -10$.
Then $x + y = 3$.
-/
theorem easy_proof (x y : ℤ) (h₁ : x + y = 3) (h₂ : x < 0) (h₃ : x * y = -10) :
x + y = 3 :=
begin
  from h₁,

end


end exlean -- hide