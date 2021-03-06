import myint.basic -- hide

/-
# Equations

## Level 1: Proving equations through reflexivity

In the introduction, you read that tactics are used modify the goal, eventually proving 
a theorem.

The `refl` tactic (short for `reflexivity`) can be used to prove any statement of the form
`?X = ?X`. Here, I use `?X` to stand in for any expression of any type.
It could be `8 + 9` or `a * b` or `"adele"` or whatever.

Below, you are asked to prove `x + y = x + y`, where `x` and `y` are integers.
The word `sorry` between the `begin` and `end` lines below asks Lean not to give an error message if a
proof isn't complete. You'll see a <span style="color:orange">warning</span> message in the
bottom-right hand pane. This indicates you shouldn't trust the proof just yet, as it uses `sorry`!

Delete `sorry` (using the backspace key on your keyboard). In the right-hand pane you'll see:
```
x y : ℤ
⊢ x + y = x + y
```

Here, `x y : ℤ` is the *context*, the set of things you know. In this case, you know `x` and `y`
are integers.

The *target* is `⊢ x + y = x + y`. The `⊢` symbol can be read 'to prove'. So your target is
to prove `x + y = x + y`.

The bottom part of the right-hand pane shows an <span style="color:red">error</span>  message:
tactic failed, there are unsolved goals. Don't panic! It's just telling you that you haven't yet
proved the result.

Your task is to replace `sorry` with `refl,`. Note the comma at the end of the line!
If you're successful, Lean will respond with the message `no goals` or `Proof complete!`
-/

/- Tactic : refl
The `refl` tactic closes any goal of the form `?X = ?X`. That is, it proves any equation where the
left and right sides are *definitionally equal*.
-/

/-
## Translation to a hand-written proof

In words, the `refl` says, "The result holds by reflexivity". A one-line written proof of
the theorem below would be, "The result hold by reflexivity".

-/

namespace exlean -- hide

open myint -- hide

open_locale mynum -- hide

variables (x y : ℤ) -- Declare `x` and `y` to be integers.

/- Theorem : no-side-bar
`x + y = x + y`, for all integers `x` and `y`.
-/
theorem x_plus_y_eq_x_plus_y : x + y = x + y :=
begin
  refl,


end

end exlean -- hide
