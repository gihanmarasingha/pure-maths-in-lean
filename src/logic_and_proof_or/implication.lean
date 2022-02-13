import data.int.basic tactic -- hide

/-
# Logic and Proof (Or)

## Level 5: Implication
-/

/-
Before continuing or study of $\lor$, we examine how to prove an implication.

### Implication

The statement $(x = 2) \to x ^ 2 = 4$ is an example of implication. It can be read, 'if $x = 2$, then $x^2 = 4$'.

To *prove* an implication $p \to q$ is to assume $p$ and derive $q$.

**Theorem**: $(x = 2) \to x ^2 = 4$.

**Proof**: Assume $h : x = 2$. We must prove $x ^ 2 = 4$. Rewriting with $h$, we must prove
$2 ^ 2 = 4$. This follows by numerical calculation.

### Proving implications in Lean

To prove `p → q` in Lean, start with `assume h : p` (replacing `h` with any other name). 
You then need to prove `q`.
-/

example (x : ℕ) : (x = 2) → (x ^ 2 = 4) :=
begin
  assume h : x = 2,
  show x ^ 2 = 4,
  rw (h : x = 2),
  show 2 ^ 2 = 4, norm_num,
end


/- Tactic: assume
If the target is `⊢ p → q`, then `assume h : p` replaces the goal with one in which the target
is `⊢ q` and in which the context contains the hypothesis `h : p`.
-/

namespace exlean -- hide

/-

### Tasks

1. Replace `sorry` below with a Lean proof.
2. On a piece of paper, state and give a handwritten proof of this result.
-/

/- Hint: Starting the proof
Start with `assume h : a = b,`

The remainder of the proof is identical to that of an example from an earlier level in this world.
-/

variables (a b : ℤ)

/- Theorem : no-side-bar
Let $a$ and $b$ be integers. Then $(a = b) \to (a = 5) \lor ((a = b) \lor (a = 7))$.
-/
theorem implication_intro1 : (a = b) → (a = 5) ∨ ((a = b) ∨ (a = 7)) :=
begin
  assume h : a = b,
  right,
  left,
  from h,




end

end exlean -- hide