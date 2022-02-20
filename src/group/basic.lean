import tactic.basic strong_induction.well_ordering_principle data.set.basic

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

open group

variables {G : Type u} [group G] {a b : G}

instance group.has_pow_Z [group G] : has_pow G ℤ := ⟨λ x n, gpow n x⟩

instance group.has_pow_N [group G] : has_pow G ℕ := ⟨λ x n, npow n x⟩

@[simp] lemma npow_eq_pow {M : Type*} [group M] (n : ℕ) (x : M) : npow n x = x^n := rfl

@[simp] theorem pow_zero (a : G) : a^0 = 1 := npow_zero' _

lemma npow_one (x : G) : npow 1 x = x :=
by simp [npow_succ', npow_zero', mul_one]

lemma npow_add (m n : ℕ) (x : G) :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m ih,
  { rw [nat.zero_add, npow_zero', one_mul], },
  { rw [nat.succ_add, npow_succ', npow_succ', ih, ← mul_assoc] }
end

theorem pow_succ (a : G) (n : ℕ) : a^(n+1) = a * a^n :=
by rw [← npow_eq_pow, nat.add_comm, npow_add, npow_one, npow_eq_pow]

theorem pow_two (a : G) : a^2 = a * a :=
by rw [← npow_eq_pow, show 2 = 1 + 1, by refl, npow_add, npow_one]


def semiconj_by {M : Type u} [has_mul M] (a x y : M) : Prop := a * x = y * a

def commute {S : Type*} [has_mul S] (a b : S) : Prop := semiconj_by a b b

namespace semiconj_by

protected lemma eq {S : Type u} [has_mul S] {a x y : S} (h : semiconj_by a x y) :
  a * x = y * a := h

@[simp] lemma mul_right {a x y x' y' : G} (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x * x') (y * y') :=
by { unfold semiconj_by at *, rw [←mul_assoc, h, mul_assoc, h', mul_assoc] }

@[simp] lemma pow_right {a x y : G} (h : semiconj_by a x y) (n : ℕ) : semiconj_by a (x^n) (y^n) :=
begin
  induction n with n ih,
  { simp [← npow_eq_pow, npow_zero', semiconj_by, one_mul, mul_one],  },
  { simp only [← npow_eq_pow, nat.succ_eq_add_one, npow_one, npow_add] at ⊢ ih,
    exact ih.mul_right h }
end

end semiconj_by

namespace commute

@[refl, simp] protected theorem refl (a : G) : commute a a := eq.refl (a * a)

@[symm] protected theorem symm {a b : G} (h : commute a b) : commute b a :=
eq.symm h

@[simp] theorem pow_right (h : commute a b) (n : ℕ) : commute a (b ^ n) := h.pow_right n
@[simp] theorem pow_left (h : commute a b) (n : ℕ) : commute (a ^ n) b := (h.symm.pow_right n).symm
@[simp] theorem pow_pow (h : commute a b) (m n : ℕ) : commute (a ^ m) (b ^ n) :=
(h.pow_left m).pow_right n

@[simp] theorem self_pow (a : G) (n : ℕ) : commute a (a ^ n) := (commute.refl a).pow_right n
@[simp] theorem pow_self (a : G) (n : ℕ) : commute (a ^ n) a := (commute.refl a).pow_left n
@[simp] theorem pow_pow_self (a : G) (m n : ℕ) : commute (a ^ m) (a ^ n) :=
(commute.refl a).pow_pow m n

end commute

theorem pow_mul_comm' (a : G) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n

theorem pow_succ' (a : G) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']

theorem pow_add (a : G) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]


@[simp] theorem one_pow (n : ℕ) : (1 : G) ^ n = 1 :=
begin
  induction n with n ih,
  { rw pow_zero, },
  { rw [pow_succ, ih, one_mul], },
end

theorem pow_one (a : G) : a ^ 1 = a := by rw [← npow_eq_pow, npow_one]

theorem pow_mul (a : G) (m n : ℕ) : a^(m * n) = (a^m)^n :=
begin
  induction n with n ih,
  { rw [nat.mul_zero, pow_zero, pow_zero] },
  { rw [nat.mul_succ, pow_add, pow_succ', ih] }
end

example : a ^ 2 = a * a :=
begin
  rw pow_two,
end

def pow_eq_one_set (a : G) := {n : ℕ | (1 ≤ n) ∧ a ^ n = 1}

end exlean