/-
Portions of this file are lifted from `data.nat.basic` and `data.nat.lemmas`
-/

-- import tactic.structure_helper

import tactic.pure_maths tactic.localized

namespace exlean

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

namespace mynat

open mynat

localized "notation `ℕ` := mynat" in mynum

instance : has_zero ℕ := ⟨zero⟩

def add : ℕ → ℕ → ℕ
| a zero := a
| a (succ b) := succ (add a b)

instance : has_add ℕ := ⟨mynat.add⟩

def pred : ℕ → ℕ
| zero := zero
| (succ a) := a

protected def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (succ b) := pred (sub a b)

instance : has_sub ℕ := ⟨mynat.sub⟩

section addition

theorem add_zero (a : ℕ) : a + 0 = a := rfl

theorem add_succ (a b : ℕ) : a + succ b = succ (a + b) := rfl

theorem zero_add' (a : ℕ) : 0 + a = a :=
mynat.rec_on a rfl (λ x h, (add_succ 0 x).symm ▸ (congr_arg _ h))

theorem add_assoc' (a b c : ℕ) : a + b + c = a + (b + c) :=
mynat.rec_on c (add_zero (a + b) ▸ rfl)
(λ x h, (add_succ (a + b) x).symm ▸ (add_succ b x).symm ▸
  (add_succ a (b + x)).symm ▸ (congr_arg _ h))

theorem succ_add' (a b : ℕ) : succ a + b = succ (a + b) :=
mynat.rec_on b ((add_zero a).symm ▸ (add_zero a.succ).symm ▸ rfl)
(λ x h, (add_succ a.succ x).symm ▸ (add_succ a x).symm ▸ h ▸ rfl)

theorem add_comm' (a b : ℕ) : a + b = b + a := mynat.rec_on b
((add_zero a).symm ▸ (zero_add' a).symm ▸ rfl)
(λ x h, (add_succ a x).symm ▸ (succ_add' x a).symm ▸ h ▸ rfl)

end addition

section multiplication

def mul : ℕ → ℕ → ℕ
| a zero := zero
| a (succ b) := (mul a b) + a

instance : has_mul ℕ := ⟨mul⟩

theorem mul_zero (a : ℕ) : a * 0 = 0 := rfl

theorem mul_succ (a b : ℕ) : a * succ b = (a * b) + a := rfl

instance : has_one ℕ := ⟨succ zero⟩

lemma zero_ne_one : (0 : mynat) ≠ 1 := λ h, mynat.no_confusion h

theorem succ_eq_add_one (a : ℕ) : a.succ = a + 1 := rfl

theorem zero_mul' (a : ℕ) : 0 * a = 0 := mynat.rec_on a rfl (λ x h, h)

theorem succ_mul' (a b : ℕ) : succ a * b = (a * b) + b :=
mynat.rec_on b rfl (λ x h, (mul_succ a.succ x).symm ▸ h.symm ▸ (mul_succ a x).symm ▸ 
  (add_assoc' (a*x) x a.succ).symm ▸ (add_assoc' (a*x) a x.succ).symm ▸ 
  (congr_arg _ $ (add_succ a x).symm ▸ (add_succ x a).symm ▸ add_comm' x a ▸ rfl) ) 

theorem one_mul' (a : ℕ) : 1 * a = a := mynat.rec_on a rfl
(λ x h, (mul_succ 1 x).symm ▸ h.symm ▸ (succ_eq_add_one x) ▸ rfl)

theorem mul_one' (a : ℕ) : a * 1 = a := mynat.rec_on a rfl
(λ x h, (mul_succ x.succ 0).symm ▸ (mul_zero x).symm ▸ (zero_add' x.succ).symm ▸ rfl)

theorem mul_add' (a b c : ℕ) : a * (b + c) = a * b + a * c := mynat.rec_on c rfl
(λ x h, (add_succ b x).symm ▸ (mul_succ a (b + x)).symm ▸ (mul_succ a x).symm ▸ h.symm ▸ 
(add_assoc' (a*b) (a*x) a).symm ▸ rfl)

theorem mul_assoc' (a b c : ℕ) : a * b * c = a * (b * c) := mynat.rec_on c rfl
(λ x h, (mul_succ (a*b) x).symm ▸ (mul_succ b x).symm ▸ h.symm ▸
  (mul_add' a (b*x) b).symm ▸ rfl)

theorem mul_comm' (a b : ℕ) : a * b = b * a := mynat.rec_on b
((zero_mul' a).symm ▸ (mul_zero a).symm ▸ rfl)
(λ x h, (mul_succ a x).symm ▸ (succ_mul' x a ).symm ▸ h ▸ rfl)

theorem add_mul' (a b c : ℕ) : (a + b) * c = a * c + b * c :=
(mul_comm' (a + b) c).symm ▸ (mul_add' c a b).symm ▸ (mul_comm' c a).symm ▸ (mul_comm' c b).symm ▸ rfl

end multiplication

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

instance : has_le ℕ :=
⟨mynat.less_than_or_equal⟩

@[reducible] protected def le (n m : ℕ) := mynat.less_than_or_equal n m
@[reducible] protected def lt (n m : ℕ) := mynat.less_than_or_equal (succ n) m

instance : has_lt ℕ := ⟨mynat.lt⟩

instance : decidable_eq ℕ
| zero     zero     := is_true rfl
| (succ x) zero     := is_false (λ h, mynat.no_confusion h)
| zero     (succ y) := is_false (λ h, mynat.no_confusion h)
| (succ x) (succ y) :=
    match decidable_eq x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (succ x))
    | is_false xney := is_false (λ h, mynat.no_confusion h (λ xeqy, absurd xeqy xney))
    end

@[refl] protected lemma le_refl (a : ℕ) : a ≤ a := less_than_or_equal.refl

protected lemma le_trans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
less_than_or_equal.rec h1 (λ p h2, less_than_or_equal.step)

lemma succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
λ h, less_than_or_equal.rec (mynat.le_refl (succ n)) (λ a b, less_than_or_equal.step) h

protected lemma lt_of_le_of_lt {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
mynat.le_trans (succ_le_succ h₁)

lemma not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false .

lemma pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
λ h, less_than_or_equal.rec_on h (mynat.le_refl (pred n))
  (λ n, mynat.rec (λ a b, b) (λ a b c, less_than_or_equal.step) n)

lemma le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m := pred_le_pred

lemma not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
λ n, mynat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

protected lemma lt_irrefl (n : ℕ) : ¬n < n := not_succ_le_self n

protected lemma le_antisymm {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
less_than_or_equal.cases_on h₁ (λ a, rfl) (λ a b c, absurd (mynat.lt_of_le_of_lt b c) (mynat.lt_irrefl n))

lemma le_succ (n : ℕ) : n ≤ succ n := less_than_or_equal.step (mynat.le_refl n)

lemma le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m := mynat.le_trans (le_succ n) h

protected lemma le_of_lt {n m : ℕ} (h : n < m) : n ≤ m := le_of_succ_le h

lemma zero_le : ∀ (n : ℕ), 0 ≤ n
| 0     := mynat.le_refl 0
| (n+1) := less_than_or_equal.step (zero_le n)

lemma le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m := mynat.le_trans h (le_succ m)

protected lemma eq_or_lt_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
less_than_or_equal.cases_on h (or.inl rfl) (λ n h, or.inr (succ_le_succ h))

lemma lt.base (n : ℕ) : n < succ n := mynat.le_refl (succ n)

lemma lt_succ_self (n : ℕ) : n < succ n := lt.base n

protected lemma lt_or_ge : ∀ (a b : ℕ), a < b ∨ b ≤ a
| a 0     := or.inr (zero_le a)
| a (b+1) :=
  match lt_or_ge a b with
  | or.inl h := or.inl (le_succ_of_le h)
  | or.inr h :=
    match mynat.eq_or_lt_of_le h with
    | or.inl h1 := or.inl (h1 ▸ lt_succ_self b)
    | or.inr h1 := or.inr h1
    end
  end

protected lemma le_total {m n : ℕ} : m ≤ n ∨ n ≤ m := or.imp_left mynat.le_of_lt (mynat.lt_or_ge m n)

protected lemma lt_of_le_and_ne {m n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
or.resolve_right (or.swap (mynat.eq_or_lt_of_le h1))

protected lemma lt_iff_le_not_le {m n : ℕ} : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) :=
⟨λ hmn, ⟨mynat.le_of_lt hmn, λ hnm, mynat.lt_irrefl _ (mynat.lt_of_le_of_lt hnm hmn)⟩,
 λ ⟨hmn, hnm⟩, mynat.lt_of_le_and_ne hmn (λ heq, hnm (heq ▸ mynat.le_refl _))⟩

instance decidable_le : ∀ a b : ℕ, decidable (a ≤ b)
| 0     b     := is_true (zero_le b)
| (a+1) 0     := is_false (not_succ_le_zero a)
| (a+1) (b+1) :=
  match decidable_le a b with
  | is_true h  := is_true (succ_le_succ h)
  | is_false h := is_false (λ a, h (le_of_succ_le_succ a))
  end

instance decidable_lt : ∀ a b : ℕ, decidable (a < b) :=
λ a b, mynat.decidable_le (succ a) b

instance : linear_order ℕ :=
{ le := mynat.less_than_or_equal,
  le_refl := @mynat.le_refl,
  le_trans := @mynat.le_trans,
  le_antisymm := @mynat.le_antisymm,
  le_total := @mynat.le_total,
  lt := mynat.lt,
  lt_iff_le_not_le := @mynat.lt_iff_le_not_le,
  decidable_lt               := mynat.decidable_lt,
  decidable_le               := mynat.decidable_le,
  decidable_eq               := mynat.decidable_eq }

lemma le.dest : ∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
| n _ less_than_or_equal.refl := ⟨0, rfl⟩
| n _ (less_than_or_equal.step h) :=
  match le.dest h with
  | ⟨w, hw⟩ := ⟨succ w, hw ▸ add_succ n w⟩
  end

@[simp] lemma succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
mynat.rec_on b
  (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
  (λ b, congr_arg pred)

theorem succ_sub_succ (n m : ℕ) : succ n - succ m = n - m := succ_sub_succ_eq_sub n m

@[ematch_lhs]
protected theorem add_sub_add_right : ∀ (n k m : ℕ), (n + k) - (m + k) = n - m
| n 0        m := by rw [mynat.add_zero, mynat.add_zero]
| n (succ k) m := by rw [add_succ, add_succ, succ_sub_succ, add_sub_add_right n k m]

@[ematch_lhs]
protected theorem add_sub_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
by rw [mynat.add_comm' k n, mynat.add_comm' k m, mynat.add_sub_add_right]

@[simp] protected lemma zero_sub : ∀ a : ℕ, 0 - a = 0
| 0     := rfl
| (a+1) := congr_arg pred (zero_sub a)

theorem sub_self_add (n m : ℕ) : n - (n + m) = 0 :=
show (n + 0) - (n + m) = 0, from by rw [mynat.add_sub_add_left, mynat.zero_sub]

theorem sub_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : n - m = 0 :=
exists.elim (mynat.le.dest h) (assume k, assume hk : n + k = m, by rw [← hk, sub_self_add])

lemma le_add_right : ∀ (n k : ℕ), n ≤ n + k
| n 0     := mynat.le_refl n
| n (k+1) := le_succ_of_le (le_add_right n k)

lemma le_add_left (n m : ℕ): n ≤ m + n := mynat.add_comm' n m ▸ le_add_right n m

@[simp]
protected theorem sub_zero (n : ℕ) : n - 0 = n := rfl

@[ematch_lhs]
protected theorem add_sub_cancel_left (n m : ℕ) : n + m - n = m :=
show n + m - (n + 0) = m, from by rw [mynat.add_sub_add_left, mynat.sub_zero]

@[ematch_lhs]
protected theorem add_sub_cancel (n m : ℕ) : n + m - m = n :=
suffices n + m - (0 + m) = n, from by rwa [mynat.zero_add'] at this, by rw [mynat.add_sub_add_right, mynat.sub_zero]

protected theorem add_sub_assoc {m k : ℕ} (h : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
exists.elim (le.dest h) (assume l, assume hl : k + l = m,
    by rw [← hl, mynat.add_sub_cancel_left, mynat.add_comm' k, ← mynat.add_assoc', mynat.add_sub_cancel])

theorem succ_pred_eq_of_pos : ∀ {n : ℕ}, 0 < n → succ (pred n) = n
| 0 h        := absurd h (lt_irrefl 0)
| (succ k) h := rfl

theorem add_sub_of_le {n m : ℕ} (h : n ≤ m) : n + (m - n) = m :=
exists.elim (le.dest h)
  (assume k, assume hk : n + k = m, by rw [← hk, mynat.add_sub_cancel_left])

protected theorem sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n :=
by rw [mynat.add_comm', add_sub_of_le h]

lemma le.intro {n m k : ℕ} (h : n + k = m) : n ≤ m := h ▸ le_add_right n k

protected lemma add_left_cancel : ∀ {n m k : ℕ}, n + m = n + k → m = k
| 0        m k := by simp [mynat.zero_add'] {contextual := tt}
| (succ n) m k := λ h,
  have n+m = n+k, by { simp [mynat.succ_add'] at h, assumption },
  add_left_cancel this

protected lemma le_of_add_le_add_left {k n m : ℕ} (h : k + n ≤ k + m) : n ≤ m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w
  begin
    rw [mynat.add_assoc'] at hw,
    apply mynat.add_left_cancel hw
  end
end

protected theorem lt_of_add_lt_add_left {k n m : ℕ} (h : k + n < k + m) : n < m :=
let h' := mynat.le_of_lt h in
mynat.lt_of_le_and_ne
  (mynat.le_of_add_le_add_left h')
  (λ heq, mynat.lt_irrefl (k + m) begin rw heq at h, assumption end)

protected lemma lt_of_add_lt_add_right {a b c : ℕ} (h : a + b < c + b) : a < c :=
mynat.lt_of_add_lt_add_left $
show b + a < b + c, by rwa [mynat.add_comm' b a, mynat.add_comm' b c]

protected theorem sub_pos_of_lt {m n : ℕ} (h : m < n) : 0 < n - m :=
have 0 + m < n - m + m, begin rw [mynat.zero_add', mynat.sub_add_cancel (le_of_lt h)], exact h end,
mynat.lt_of_add_lt_add_right this

protected lemma add_le_add_left {n m : ℕ} (h : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w begin rw [mynat.add_assoc', hw] end
end

protected lemma add_le_add_right {n m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
begin rw [mynat.add_comm' n k, mynat.add_comm' m k], apply mynat.add_le_add_left h end

protected theorem le_of_sub_eq_zero : ∀{n m : ℕ}, n - m = 0 → n ≤ m
| n 0 H := begin rw [mynat.sub_zero] at H, simp [H] end
| 0 (m+1) H := zero_le _
| (n+1) (m+1) H := mynat.add_le_add_right
  (le_of_sub_eq_zero begin simp [mynat.add_sub_add_right] at H, exact H end) _

protected lemma lt_of_sub_eq_succ {m n l : ℕ} (H : m - n = mynat.succ l) : n < m :=
not_le.1
  (assume (H' : n ≥ m), begin simp [mynat.sub_eq_zero_of_le H'] at H, contradiction end)

protected lemma sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
⟨assume c_eq, begin rw [c_eq.symm, mynat.sub_add_cancel ab] end,
  assume a_eq, begin rw [a_eq, mynat.add_sub_cancel] end⟩

protected lemma add_left_comm : ∀ (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm mynat.add mynat.add_comm' mynat.add_assoc'

protected lemma lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := mynat.le_trans

theorem succ_sub {m n : ℕ} (h : n ≤ m) : succ m - n = succ (m - n) :=
exists.elim (mynat.le.dest h)
  (assume k, assume hk : n + k = m,
    by rw [← hk, mynat.add_sub_cancel_left, ← add_succ, mynat.add_sub_cancel_left])

@[simp]
lemma pred_succ (n : ℕ) : pred (succ n) = n := rfl

protected lemma add_comm : ∀ n m : ℕ, n + m = m + n
| n 0     := eq.symm (mynat.zero_add' n)
| n (m+1) :=
  suffices succ (n + m) = succ (m + n), from
    eq.symm (succ_add' m n) ▸ this,
  congr_arg succ (add_comm n m)

protected theorem sub_self : ∀ (n : ℕ), n - n = 0
| 0        := by rw mynat.sub_zero
| (succ n) := by rw [succ_sub_succ, sub_self n]

lemma lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

lemma succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

protected lemma add_lt_add_left {n m : ℕ} (h : n < m) (k : ℕ) : k + n < k + m :=
lt_of_succ_le (add_succ k n ▸ mynat.add_le_add_left (succ_le_of_lt h) k)

protected lemma lt_add_of_pos_right {n k : ℕ} (h : 0 < k) : n < n + k := mynat.add_lt_add_left h n

private meta def sort_add :=
`[simp [mynat.add_assoc', mynat.add_comm, mynat.add_left_comm]]

@[simp]
lemma pred_zero : pred 0 = 0 := rfl

lemma succ_mul : ∀ (n m : ℕ), (succ n) * m = (n * m) + m
| n 0        := rfl
| n (succ m) :=
  begin
    simp [mul_succ, add_succ, succ_mul n m],
    sort_add
  end

protected lemma left_distrib : ∀ (n m k : ℕ), n * (m + k) = n * m + n * k
| 0        m k := by simp [mynat.zero_mul', add_zero]
| (succ n) m k :=
  begin simp [succ_mul, left_distrib n m k], sort_add end

lemma mul_le_mul_left {n m : ℕ} (k : ℕ) (h : n ≤ m) : k * n ≤ k * m :=
match le.dest h with
| ⟨l, hl⟩ :=
  have k * n + k * l = k * m, by rw [← mynat.left_distrib, hl],
  le.intro this
end

protected lemma mul_lt_mul_of_pos_left {n m k : ℕ} (h : n < m) (hk : 0 < k) : k * n < k * m :=
mynat.lt_of_lt_of_le (mynat.lt_add_of_pos_right hk) (mul_succ k n ▸ mynat.mul_le_mul_left k (succ_le_of_lt h))

theorem mul_pred_left : ∀ (n m : ℕ), pred n * m = n * m - m
| 0        m := by simp [mynat.zero_sub, pred_zero, mynat.zero_mul']
| (succ n) m := by rw [pred_succ, succ_mul, mynat.add_sub_cancel]

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
by rw [mynat.mul_comm', mul_pred_left, mynat.mul_comm']

theorem sub_succ (n m : ℕ) : n - succ m = pred (n - m) := rfl

protected theorem sub_sub : ∀ (n m k : ℕ), n - m - k = n - (m + k)
| n m 0        := by rw [mynat.add_zero, mynat.sub_zero]
| n m (succ k) := by rw [add_succ, mynat.sub_succ, mynat.sub_succ, sub_sub n m k]

protected theorem mul_sub_right_distrib : ∀ (n m k : ℕ), (n - m) * k = n * k - m * k
| n 0        k := by simp [mynat.sub_zero, mynat.zero_mul']
| n (succ m) k := by rw [mynat.sub_succ, mul_pred_left, mul_sub_right_distrib, succ_mul, mynat.sub_sub]

protected theorem mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by rw [mynat.mul_comm', mynat.mul_sub_right_distrib, mynat.mul_comm' m n, mynat.mul_comm' n k]

lemma zero_lt_succ (n : ℕ) : 0 < succ n := succ_le_succ (zero_le n)

lemma succ_pos (n : ℕ) : 0 < succ n := zero_lt_succ n

protected lemma right_distrib : ∀ (n m k : ℕ), (n + m) * k = n * k + m * k
| n m 0        := rfl
| n m (succ k) :=
  begin simp [mul_succ, right_distrib n m k], sort_add end

def nat_to_mynat : nat → mynat
| nat.zero     := mynat.zero
| (nat.succ n) := mynat.succ (nat_to_mynat n)

def mynat_to_nat : mynat → nat
| mynat.zero      := nat.zero
| (mynat.succ n)  := nat.succ (mynat_to_nat n)

lemma mynat_to_nat_nat_to_mynat (n : nat) : mynat_to_nat (nat_to_mynat n) = n :=
begin
  induction n with k ih,
  { refl, },
  { rw [nat_to_mynat, mynat_to_nat, ih], },
end

lemma nat_to_mynat_mynat_to_nat (n : mynat) : nat_to_mynat (mynat_to_nat n) = n :=
begin
  induction n with k ih,
  { refl, },
  { rw [mynat_to_nat, nat_to_mynat, ih], },
end

lemma zero_eq_zero : zero = 0 := rfl

lemma nat_to_mynat_add_hom (x y : nat) : (nat_to_mynat x) + (nat_to_mynat y) = nat_to_mynat (x + y) :=
begin
  induction x with k ih,
  { rw [nat_to_mynat, nat.zero_add, zero_eq_zero, zero_add'], },
  { rw [nat_to_mynat, succ_add', ih, nat.succ_add, nat_to_mynat], },
end

lemma mynat_to_nat_add_hom (x y : mynat) : (mynat_to_nat x) + (mynat_to_nat y) = mynat_to_nat (x + y) :=
begin
  induction x with k ih,
  { rw [mynat_to_nat, nat.zero_add, zero_eq_zero, zero_add'], },
  { rw [mynat_to_nat, nat.succ_add, ih, succ_add', mynat_to_nat], },
end

lemma nat_to_mynat_pred (n : nat) : nat_to_mynat n.pred = (nat_to_mynat n).pred :=
begin
  induction n with k ih;
  refl,
end

lemma mynat_to_nat_pred (n : mynat) : mynat_to_nat n.pred = (mynat_to_nat n).pred :=
begin
  induction n with k ih;
  refl,
end

lemma nat_to_mynat_sub_hom (x y : nat) : (nat_to_mynat x) - (nat_to_mynat y) = nat_to_mynat (x - y) :=
begin
  induction y with k ih,
  { rw [nat_to_mynat, nat.sub_zero, zero_eq_zero, mynat.sub_zero], },
  { rw [nat_to_mynat, sub_succ, ih, nat.sub_succ, nat_to_mynat_pred], }
end

lemma mynat_to_nat_sub_hom (x y : mynat) : (mynat_to_nat x) - (mynat_to_nat y) = mynat_to_nat (x - y) :=
begin
  induction y with k ih,
  { rw [mynat_to_nat, nat.sub_zero, zero_eq_zero, mynat.sub_zero], },
  { rw [mynat_to_nat, nat.sub_succ, ih, sub_succ, mynat_to_nat_pred], }
end

lemma nat_to_mynat_mul_hom (x y : nat) : (nat_to_mynat x) * (nat_to_mynat y) = nat_to_mynat(x * y) :=
begin
  induction x with k ih,
  { rw [nat_to_mynat, nat.zero_mul, nat_to_mynat, zero_eq_zero, mynat.zero_mul'], },
  { rw [nat_to_mynat, succ_mul, ih, nat.succ_mul, ←nat_to_mynat_add_hom], },
end

end mynat

end exlean