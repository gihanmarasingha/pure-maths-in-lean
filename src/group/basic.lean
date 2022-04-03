import tactic.basic 

universe u

namespace exlean

meta def try_refl_tac : tactic unit := `[intros; refl]

variables {M : Type u}

def npow_rec [has_one M] [has_mul M] : ℕ → M → M
| 0     a := 1
| (n+1) a := a * npow_rec n a

def gpow_rec {M : Type*} [has_one M] [has_mul M] [has_inv M] : ℤ → M → M
| (int.of_nat n) a := npow_rec n a
| -[1+ n]    a := (npow_rec n.succ a) ⁻¹

class group (G : Type u) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_one : ∀ (a : G), a * 1 = a)
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
(gpow : ℤ → G → G := gpow_rec)
(npow : ℕ → G → G := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)
(gpow_zero' : ∀ (a : G), gpow 0 a = 1 . try_refl_tac)
(gpow_succ' :
  ∀ (n : ℕ) (a : G), gpow (int.of_nat n.succ) a = a * gpow (int.of_nat n) a . try_refl_tac)
(gpow_neg' :
  ∀ (n : ℕ) (a : G), gpow (-[1+ n]) a = (gpow n.succ a) ⁻¹ . try_refl_tac)

end exlean