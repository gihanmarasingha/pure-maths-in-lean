import tactic -- hide

/-
# Variables

## Level 2: For all introduction
-/

/-
We've seen how to *apply* for all statements. How do you *prove* a for all statement?

**Theorem**: Let $f : \mathbb Z \to \mathbb Z$ be a function. Let $h$ be the assumption that
for every $x$, $-5 < f(x)$ and $f(x) < 5$. Then, for every integer $y$, $f(y) < 5$.

**Proof**: Assume $y$ is an integer. We must show $f(y) < 5$. 
We have $h₁ : -5 < f(y) \land f(y) < 5$ from for all elimination on $h$ and $y$.
The result follows from right and elimination on $h_1$. ∎

As illustrated above, to prove something happens for every $x$ is to assume $y$ is a variable
quantity and then to demonstrate that the desired property holds for that $y$.
-/

variable (f : ℤ → ℤ)

example (h : ∀ x, -5 < f(x) ∧ f(x) < 5) : ∀ y, f(y) < 5 :=
begin
  assume y : ℤ,
  show f(y) < 5,
  have h₁ : -5 < f(y) ∧ f(y) < 5, from h y,
  from and.elim_right h₁,
end



/-

### Tasks

1. Replace `sorry` below with a Lean proof.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Hint: Starting the proof
Begin with `assume y : ℤ`. This changes the goal to one of showing `f(y + 1) = f(y) ∨ f(y) = 0`.
-/

namespace exlean -- hide


/- Theorem : no-side-bar
Let $f : \mathbb Z \to \mathbb Z$ be a function. Let $h$ be the assumption that for every
integer $x$, $f(x+1)=f(x)$. Then, for every integer $y$, $f(y+1) = f(y)$ or $f(y) = 0$.
-/
theorem all_intro1 (h : ∀ x, f(x + 1) = f(x)) :
∀ y, (f(y + 1) = f(y)) ∨ (f(y) = 0) :=
begin
  assume y : ℤ,
  show f(y + 1) = f(y) ∨ f(y) = 0,
  left,
  from h y,





end


end exlean -- hide