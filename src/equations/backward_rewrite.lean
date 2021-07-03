import myint.basic equations.multiple_rewrites -- hide

/-
# Equations

## Level 8: Backward rewrites

Suppose you wanted to prove `y + x = 0` on the assumptions `h1 : x + 0 = 0` and `h2 : y = 0`.
One option would be to rewrite with `h2` to give `⊢ 0 + x = 0`. You could then finish by
rewriting with `add_comm` and `h1`.

Another option is to start by rewriting with `h1` *backward*. This would replace `0`
in the target with `x + 0`. To do this in Lean, type `rw ←h1`.

To get the left arrow, type `\l` followed by space or tab. Alternatively, just type `<-`
-/



namespace exlean -- hide

open_locale mynum -- hide

open myint -- hide

variables (x y z : ℤ) -- hide

/-
Here is a proof of this result, using three rewrites, one backward.
-/

example (h1 : x + 0 = 0) (h2 : y = 0) : y + x = 0 :=
begin
  [pure_maths] -- hide
  rw [←h1, add_comm, h2],
  refl,

-- hide  
end

/-
Your turn! Prove the following using two rewrites, one backward.

Once you've done that, write a structured proof of the same result.
-/

/- Hint: Hint for structured proof

Introduce and prove the hypotheses `h2 : y + z * x = (z + x) + y` and
`h3 : (z + x) + y = y + (z + x)` using the `have` tactic. Finish by rewriting with these
hypotheses.
-/

/- Theorem : no-side-bar
Let `x`, `y`, and `z` be integers. If `(z + x) + y = y + z * x`, then `y + z * x = y + (z + x)`
-/
theorem funky_town
(h : (z + x) + y = y + z * x) : y + z * x = y + (z + x) :=
begin [pure_maths]
  rw [←h, add_comm],
  refl,
/-   have h2 : y + z * x = (z + x) + y,
  { rw h, refl },
  have h3 : (z + x) + y = y + (z + x),
  { rw add_comm, refl },
  rw [h2, h3], refl,  -/
end

end exlean -- hide