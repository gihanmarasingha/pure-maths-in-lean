import tactic.linarith divisibility.division -- hide

/-
# Divisibility

## Level 16: Non-divisibility examples
-/

namespace exlean -- hide

/-
In any particular numerical example, it's easy to show divisibility. For example, here's a proof
that $7 \mid 42$.
-/

example : (7 : ℤ) ∣  42 :=
begin
  use 6,
  norm_num,
end

/-
But how can we prove non-divisibility? How would you prove $7 \nmid 31$?

The idea is to use the uniqueness of division result. Suppose (for a contradiction), that
$h: 7 \mid 31$. Decomposing $h$ gives $m : \mathbb Z$ and $h : 31 = 7m = 7m + 0$.

But (as you may easily verify), we have $h_2 : 31 = 7 \times 4 + 3$.

Using $h$ and $h_2$ in the uniquness of division result, we infer $m = 4$ and $0 = 3$. This
latter is a contradiction.
-/

/-
Here we use the semi-colon `;` 'tactic combinator'. This is a time-saving measure that applies
the following tactic to each remaining goal. In our application, the tactic `tidy` is used
to complete each of the three goals that arise from the application of `division_unique 31 7`.
-/

example : ¬((7 : ℤ) ∣ 31) :=
begin
  assume h : (7 : ℤ) ∣ 31,
  cases h with m h, -- We have `m : ℤ` and `h : 31 = 7 * m`.
  have h₁ : (31 : ℤ) = 7 * m + 0, linarith,
  have h₂ : (31 : ℤ) = 7 * 4 + 3, norm_num,

  have k₁ : m = 4 ∧ (0 : ℤ) = 3,
  { apply division_unique 31 7;
    tidy, },
  linarith, -- `k₁` gives a contradiction.
end


/- Lemma : no-side-bar
5 does not divide sixty-two.
-/
lemma five_nmid_sixty_two : ¬ ((5 : ℤ) ∣ 62) :=
begin
  assume h : (5 : ℤ) ∣ 62,
  cases h with m hm,
  have h₁ : 62 = m * 5 + 0, linarith,
  have h₂ : (62 : ℤ) = 12 * 5 + 2, norm_num,
  
  have k₁ : m = 12 ∧ (0 : ℤ) = 2,
  { apply division_unique 62 5;
    tidy, },
  linarith,











  
end




end exlean -- hide