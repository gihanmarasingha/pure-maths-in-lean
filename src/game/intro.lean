/-
# Pure mathematics with Lean, version 1.0.0

## By Gihan Marasingha

This is an interactive book aimed at beginning mathematics undergraduates. You'll learn to prove
theorems online using a computer tool called Lean.

Each chapter is represented by a coloured circular button in the right-hand pane. Blue indicates your
current position, green is for completed chapters, and grey is for unread or incomplete chapters.

At every stage in a theorem, there is a *target*, the thing you want to prove, and a *context*, the
set of things you have already proved or assumed at the beginning of your argument.
The target and context change through the proof.

The word *goal* is used to refer variously to the target or to the combination of target and context.

You'll use *tactics* to modify the goal until you have proved the target (called 'closing the goal').
Each tactic may invoke one or more *theorems*.

Note: the book is roughly 30Mb in size. It must be downloaded before you can begin to work on the
problems. Once you open the book, wait for the text 'Lean is busy...' to disappear from the
top-right-hand pane before using Lean.

*Pure mathematics with Lean* is part of the 
<a href="https://exlean.org" target="blank">exlean</a> project.

**This book is under construction.** At the time of writing, only the first chapter is available.
It's on the additive commutativity, associativity, identity, and inverse properties of the integers.

## Credits

This game was made using the
<a href="https://github.com/mpedramfar/Lean-game-maker">Lean Game Maker</a> by Mohammad Pedramfar.

It uses ideas and special tactics from the 
<a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/">Natural Number Game</a>
by Kevin Buzzard.

<a href="https://leanprover.github.io/" target="blank">Lean</a> is an interactive theorem prover developed at Microsoft Research under the direction of
Leonardo de Moura.

Mathlib, Lean's mathematical library, is developed by the <a href="https://leanprover-community.github.io/" target="blank">Lean community</a>.

Here's some mathematics in MathJax, just to remind me that it's possible.
First inline: \\(a^2 + b^2 = c^2\\). Now displayed:

\\[ \int_{-\infty}^\infty  e^{-x^2} dx = \sqrt \pi. \\]

-/
