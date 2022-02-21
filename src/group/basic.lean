import tactic.basic strong_induction.well_ordering_principle data.set.basic tactic.nth_rewrite.default

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

open group

attribute [simp] mul_one one_mul

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

@[simp] theorem pow_one (a : G) : a ^ 1 = a := by rw [← npow_eq_pow, npow_one]

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

namespace int

lemma neg_zero : -(0 : ℤ) = 0 := by {apply int.neg_eq_of_add_eq_zero, refl}

lemma sub_eq_neg_add (a b : ℤ) : a - b = -b + a :=
by rw [int.sub_eq_add_neg, int.add_comm _ _]

lemma neg_add_rev (a b : ℤ) : - (a + b) = (- b) + (-a) :=
begin
  apply int.neg_eq_of_add_eq_zero,
  rw [int.add_assoc, ←int.add_assoc b, int.add_right_neg, int.zero_add, int.add_right_neg],
end

@[elab_as_eliminator] protected lemma induction_on {p : ℤ → Prop}
  (i : ℤ) (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i :=
begin
  induction i,
  { induction i,
    { exact hz },
    { exact hp _ i_ih } },
  { have : ∀ n:ℕ, p (- n),
    { intro n, induction n,
      { simp only [hz, int.coe_nat_zero, neg_zero], },
      { convert hn _ n_ih using 1,
        simp only [sub_eq_neg_add, int.coe_nat_succ, neg_add_rev],  } },
    exact this (i + 1) }
end

lemma mul_add (a b c : ℤ) : a * (b + c) = a * b + a * c := int.distrib_left a b c

end int

@[simp, norm_cast] theorem gpow_coe_nat (a : G) (n : ℕ) : a ^ (n:ℤ) = a ^ n :=
begin
  induction n with n ih,
  { change gpow 0 a = npow 0 a, rw [gpow_zero', npow_zero'], },
  { change gpow (int.of_nat n) a = a ^ n at ih,
    change gpow (int.of_nat n.succ) a = a ^ n.succ,
    rw [gpow_succ', pow_succ, ih] }
end

@[simp] theorem gpow_zero (a : G) : a ^ (0:ℤ) = 1 :=
by { convert pow_zero a using 1, exact gpow_coe_nat a 0 }

@[simp] theorem gpow_one (a : G) : a ^ (1 : ℤ) = a :=
by { convert pow_one a using 1, exact gpow_coe_nat a 1 }

lemma gpow_neg'' (n : ℕ) (a : G) : a ^ (-((n : ℤ) + 1)) = (a ^ (n.succ : ℤ))⁻¹ :=
begin 
  simp only [←int.coe_nat_one, ←int.coe_nat_add],
  simp only [←int.neg_succ_of_nat_coe],
  dsimp only [pow],
  apply gpow_neg',
end

theorem inv_inv' : (a⁻¹)⁻¹ = a :=
begin
  calc (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1  : by rw mul_one
  ... = (a⁻¹)⁻¹ * (a⁻¹ * a)   : by rw mul_left_inv
  ... = ((a⁻¹)⁻¹ * a⁻¹) * a   : by rw mul_assoc
  ... = 1 * a                 : by rw mul_left_inv
  ... = a                     : by rw one_mul
end

theorem mul_right_inv' : b * b⁻¹ = 1 :=
begin
  calc b * b⁻¹ = (b⁻¹)⁻¹ * b⁻¹ : by rw inv_inv'
  ... = 1                      : by rw mul_left_inv
end

lemma inv_eq_of_mul_eq_one' (h : a * b = 1) : a⁻¹ = b :=
begin
  calc a⁻¹ = a⁻¹ * 1    : by rw mul_one
  ... = a⁻¹ * (a * b)   : by rw h
  ... = (a⁻¹ * a) * b   : by rw mul_assoc
  ... = 1 * b           : by rw mul_left_inv
  ... = b               : by rw one_mul
end 

theorem mul_inv_rev' : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one',
  calc (a * b) * (b⁻¹ * a⁻¹)
      = a * (b * (b⁻¹ * a⁻¹))   : by rw mul_assoc
  ... = a * ((b * b⁻¹) * a⁻¹)   : by rw mul_assoc
  ... = a * (1 * a⁻¹)           : by rw mul_right_inv'
  ... = a * a⁻¹                 : by rw one_mul
  ... = 1                       : by rw mul_right_inv'
end 

lemma gpow_add_one (a : G) (n : ℤ) : a ^ (n + 1) = a ^ n * a :=
begin
  induction n using exlean.int.induction_on with n ihn n ihn,
  { rw [int.zero_add, gpow_zero, one_mul, gpow_one],  },
  { simp only [←int.coe_nat_one, ←int.coe_nat_add, gpow_coe_nat] at ⊢ ihn,
    rw [pow_add, ihn], simp, },
  { cases n with n,
    { simp only [int.coe_nat_zero, int.neg_zero],
      convert pow_zero a using 1,
      { apply gpow_coe_nat, },
      { rw show (0 : ℤ) - 1 = -((0 : ℕ) + 1), by refl,
        rw [gpow_neg'', int.coe_nat_one, gpow_one, mul_left_inv], }, },    
    rw nat.succ_eq_add_one at *,
    simp only [←int.coe_nat_one, ←int.coe_nat_sub],   
    rw show -(((n + 1) : ℕ) : ℤ) - (1 : ℕ) = -( ((n + 1) : ℕ) + 1), by refl,
    rw show -((((n + 1) : ℕ) : ℤ) + 1) + (1 : ℕ) = -( (n : ℕ) + 1), by refl,
    rw [gpow_neg'', gpow_neg''],
    simp only [gpow_coe_nat, pow_succ'],
    apply inv_eq_of_mul_eq_one',
    nth_rewrite 1 pow_mul_comm',
    rw [mul_inv_rev', mul_inv_rev'],
    rw [mul_assoc (a ^ n), ←mul_assoc a, ←mul_assoc a, mul_right_inv', one_mul],
    rw [←mul_assoc, ←mul_assoc, mul_right_inv', one_mul, mul_left_inv], },
end

@[simp]
lemma mul_inv_cancel_right' (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv', mul_one]

lemma gpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : (mul_inv_cancel_right' _ _).symm
             ... = a^n * a⁻¹             : by rw [← gpow_add_one, int.sub_add_cancel]

lemma gpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using exlean.int.induction_on with n ihn n ihn,
  case hz : { simp only [int.add_zero, mul_one, gpow_zero] },
  { simp only [← int.add_assoc, gpow_add_one, ihn, mul_assoc] },
  { rw [gpow_sub_one, ← mul_assoc, ← ihn, ← gpow_sub_one, int.add_sub_assoc] }
end

@[simp] theorem one_inv : (1 : G)⁻¹ = 1 :=
begin
  apply inv_eq_of_mul_eq_one',
  simp,
end

@[simp] theorem gpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ :=
by { rw ← gpow_coe_nat, exact gpow_neg' n a }

@[simp] theorem gpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := gpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp, }
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, inv_inv', ← gpow_coe_nat], refl }

theorem gpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ :=
by { rw [← congr_arg has_inv.inv (pow_one x), gpow_neg, ← gpow_coe_nat], refl }

lemma gpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
by rw [int.sub_eq_add_neg, gpow_add, gpow_neg]

theorem gpow_mul (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n :=
begin
  induction n using exlean.int.induction_on with n ihn n ihn,
  { simp [int.mul_zero], },
  { simp [int.mul_add, gpow_add, ihn, int.mul_one], },
  { simp only [int.sub_eq_add_neg, int.mul_add, ihn, gpow_add],
    simp [int.mul_neg_eq_neg_mul_symm, gpow_neg, int.mul_one], },
end

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := by rw [gpow_coe_nat, one_pow]
| -[1+ n] := by rw [gpow_neg_succ_of_nat, one_pow, one_inv]

lemma inv_pow (n : ℕ) : (a ^ n)⁻¹ = (a⁻¹) ^ n :=
begin
  induction n with k ih,
  { simp, },
  { rw [pow_succ', mul_inv_rev', ih, pow_succ', pow_mul_comm'], },
end


end exlean