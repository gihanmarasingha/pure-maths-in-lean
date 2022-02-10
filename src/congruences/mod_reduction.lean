import congruences.mod_mul  -- hide

/-
#  Congruences

## Level 9: Reduction of congruences
-/

namespace exlean -- hide

variables {n m a b : ℤ} -- hide

/-
We've seen the idea of reducing an integer $x$ modulo $n$. This means finding an integer $a$
such that $x \equiv a \pmod n$ with $0 \le a < |n|$.

The word 'reduction' has another meaning in the study of congruences.

Suppose $a$, $b$, $n$ and $m$ are integers with $m \mid n$. Suppose $a \equiv b \pmod n$.
It follows that $a \equiv b \pmod m$. This is called the _reduction of the congruence_
$a \equiv \pmod n$, modulo $m$.
-/

/-
### Task
Prove the reduction result mentioned above. You should be able to do this in one line by employing
an appropriate result from Divisibility World.

-/

/- Lemma : no-side-bar
Given $m \mid n$ and $a \equiv b \pmod n$, the congruence $a \equiv b \pmod m$ follows.
-/
lemma modeq_of_dvd_of_modeq (h₁ : m ∣ n) (h₂ : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
begin
  exact dvd_trans h₁ h₂,











end

end exlean -- hide