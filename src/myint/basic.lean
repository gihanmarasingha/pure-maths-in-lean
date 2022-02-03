/-
The contents of this file is a selection of text from `data.int.basic`.
-/

import mynat.basic

namespace exlean

inductive myint : Type
| of_nat : mynat → myint
| neg_succ_of_nat : mynat → myint

namespace myint

instance : has_zero myint := ⟨of_nat 0⟩

instance : has_coe mynat myint := ⟨myint.of_nat⟩

open mynat

open_locale mynum

localized "notation `ℤ` := myint" in mynum

notation `-[1+ ` n `]` := myint.neg_succ_of_nat n

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : ℕ) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

protected def neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

instance : has_neg myint := ⟨myint.neg⟩

protected def add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

instance : has_add myint := ⟨myint.add⟩

protected def mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_mul ℤ := ⟨myint.mul⟩

protected def sub : ℤ → ℤ → ℤ := λ m n, m + -n

instance : has_sub ℤ := ⟨myint.sub⟩

lemma of_nat_add_of_nat (m n : ℕ) : of_nat m + of_nat n = of_nat (m + n) := rfl
lemma of_nat_add_neg_succ_of_nat (m n : ℕ) :
                of_nat m + -[1+ n] = sub_nat_nat m (succ n) := rfl
lemma neg_succ_of_nat_add_of_nat (m n : ℕ) :
                -[1+ m] + of_nat n = sub_nat_nat n (succ m) := rfl
lemma neg_succ_of_nat_add_neg_succ_of_nat (m n : ℕ) :
                -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

lemma of_nat_mul_of_nat (m n : ℕ) : of_nat m * of_nat n = of_nat (m * n) := rfl
lemma of_nat_mul_neg_succ_of_nat (m n : ℕ) :
                of_nat m * -[1+ n] = neg_of_nat (m * succ n) := rfl
lemma neg_succ_of_nat_of_nat (m n : ℕ) :
                -[1+ m] * of_nat n = neg_of_nat (succ m * n) := rfl
lemma mul_neg_succ_of_nat_neg_succ_of_nat (m n : ℕ) :
               -[1+ m] * -[1+ n] = of_nat (succ m * succ n) := rfl
            
/- local attribute [simp] of_nat_add_of_nat of_nat_mul_of_nat 
  of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat
 -/

lemma of_nat_add (n m : ℕ) : of_nat (n + m) = of_nat n + of_nat m := rfl
lemma of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl

lemma neg_of_nat_zero : -(of_nat 0) = 0 := rfl
lemma neg_of_nat_of_succ (n : ℕ) : -(of_nat (succ n)) = -[1+ n] := rfl
lemma neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = of_nat (succ n) := rfl

lemma of_nat_eq_coe (n : ℕ) : of_nat n = ↑n := rfl
lemma neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

local attribute [simp] of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ
  neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat

section addition

protected lemma add_comm' : ∀ a b : ℤ, a + b = b + a
| (of_nat n) (of_nat m) := by simp [mynat.add_comm']
| (of_nat n) -[1+ m]    := rfl
| -[1+ n]    (of_nat m) := rfl
| -[1+ n]    -[1+m]     := by simp [mynat.add_comm']

protected lemma add_zero' : ∀ a : ℤ, a + 0 = a
| (of_nat n) := rfl
| -[1+ n]   := rfl

protected lemma zero_add' (a : ℤ) : 0 + a = a :=
myint.add_comm' a 0 ▸ myint.add_zero' a

lemma sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) :
  sub_nat_nat m n = of_nat (m - n) :=
begin unfold sub_nat_nat, rw h, unfold sub_nat_nat._match_1 end

theorem sub_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : n - m = 0 :=
exists.elim (mynat.le.dest h)
  (assume k, assume hk : n + k = m, by rw [← hk, sub_self_add])

lemma sub_nat_nat_of_le {m n : ℕ} (h : n ≤ m) : sub_nat_nat m n = of_nat (m - n) :=
sub_nat_nat_of_sub_eq_zero (sub_eq_zero_of_le h)

lemma sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) :
  sub_nat_nat m n = -[1+ k] :=
begin unfold sub_nat_nat, rw h, unfold sub_nat_nat._match_1 end

lemma sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : sub_nat_nat m n = -[1+ pred (n - m)] :=
have n - m = succ (pred (n - m)), from eq.symm (succ_pred_eq_of_pos (mynat.sub_pos_of_lt h)),
by rewrite sub_nat_nat_of_sub_eq_succ this

lemma sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (of_nat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (sub_nat_nat m n) :=
begin
  have H : ∀k, n - m = k → P m n (mynat.cases_on k (of_nat (m - n)) (λa, -[1+ a])),
  { intro k, cases k,
    { intro e,
      cases (mynat.le.dest (mynat.le_of_sub_eq_zero e)) with k h,
      rw [h.symm, mynat.add_sub_cancel_left],
      apply hp },
    { intro heq,
      have h : m ≤ n,
      { exact mynat.le_of_lt (mynat.lt_of_sub_eq_succ heq) },
      rw [mynat.sub_eq_iff_eq_add h] at heq,
      rw [heq, mynat.add_comm'],
      apply hn } },
  delta sub_nat_nat,
  exact H _ rfl
end

lemma sub_nat_nat_add_left {m n : ℕ} :
  sub_nat_nat (m + n) m = of_nat n :=
begin
  dunfold sub_nat_nat,
  rw [mynat.sub_eq_zero_of_le],
  dunfold sub_nat_nat._match_1,
  rw [mynat.add_sub_cancel_left],
  apply mynat.le_add_right
end

lemma sub_nat_nat_add_right {m n : ℕ} :
  sub_nat_nat m (m + n + 1) = neg_succ_of_nat n :=
calc sub_nat_nat._match_1 m (m + n + 1) (m + n + 1 - m) =
        sub_nat_nat._match_1 m (m + n + 1) (m + (n + 1) - m) : by rw [mynat.add_assoc']
  ... = sub_nat_nat._match_1 m (m + n + 1) (n + 1) : by rw [mynat.add_sub_cancel_left]
  ... = neg_succ_of_nat n : rfl

lemma sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
sub_nat_nat_elim m n (λm n i, sub_nat_nat (m + k) (n + k) = i)
  (assume i n, have n + i + k = (n + k) + i, by simp [mynat.add_comm', mynat.add_left_comm],
    begin rw [this], exact sub_nat_nat_add_left end)
  (assume i m, have m + i + 1 + k = (m + k) + i + 1, by simp [mynat.add_comm', mynat.add_left_comm],
    begin rw [this], exact sub_nat_nat_add_right end)

lemma sub_nat_nat_add (m n k : ℕ) : sub_nat_nat (m + n) k = of_nat m + sub_nat_nat n k :=
begin
  have h := le_or_lt k n,
  cases h with h' h',
  { rw [sub_nat_nat_of_le h'],
    have h₂ : k ≤ m + n, exact (le_trans h' (le_add_left _ _)),
    rw [sub_nat_nat_of_le h₂], simp,
    rw mynat.add_sub_assoc h' },
  rw [sub_nat_nat_of_lt h'], simp, rw [succ_pred_eq_of_pos (mynat.sub_pos_of_lt h')],
  transitivity, rw [← mynat.sub_add_cancel (le_of_lt h')],
  apply sub_nat_nat_add_add
end

lemma add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, of_nat m + of_nat n + c = of_nat m + (of_nat n + c)
| (of_nat k) := by simp [mynat.add_assoc']
| -[1+ k]    := by simp [sub_nat_nat_add]

lemma sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) :
  sub_nat_nat (m - n) k = sub_nat_nat m (k + n) :=
calc
  sub_nat_nat (m - n) k = sub_nat_nat (m - n + n) (k + n) : by rewrite [sub_nat_nat_add_add]
                    ... = sub_nat_nat m (k + n)           : by rewrite [mynat.sub_add_cancel h]

lemma sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
    sub_nat_nat m n + -[1+ k] = sub_nat_nat m (n + succ k) :=
begin
  have h := le_or_lt n m,
  cases h with h' h',
  { rw [sub_nat_nat_of_le h'], simp, rw [sub_nat_nat_sub h', mynat.add_comm'] },
  have h₂ : m < n + succ k, exact mynat.lt_of_lt_of_le h' (le_add_right _ _),
  have h₃ : m ≤ n + k, exact le_of_succ_le_succ h₂,
  rw [sub_nat_nat_of_lt h', sub_nat_nat_of_lt h₂], simp [mynat.add_comm'],
  rw [← add_succ, succ_pred_eq_of_pos (mynat.sub_pos_of_lt h'), add_succ, succ_sub h₃, pred_succ],
  rw [mynat.add_comm' n, mynat.add_sub_assoc (le_of_lt h')]
end

lemma add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + of_nat k = -[1+ m] + (-[1+ n] + of_nat k) :=
begin
  simp [add_succ],
  rw [myint.add_comm', sub_nat_nat_add_neg_succ_of_nat], simp [add_succ, succ_add', mynat.add_comm']
end

protected lemma add_comm : ∀ a b : ℤ, a + b = b + a
| (of_nat n) (of_nat m) := by simp [mynat.add_comm]
| (of_nat n) -[1+ m]    := rfl
| -[1+ n]    (of_nat m) := rfl
| -[1+ n]    -[1+m]     := by simp [mynat.add_comm]

protected lemma add_assoc' : ∀ a b c : ℤ, a + b + c = a + (b + c)
| (of_nat m) (of_nat n) c          := add_assoc_aux1 _ _ _
| (of_nat m) b          (of_nat k) := by rw [myint.add_comm, ← add_assoc_aux1, myint.add_comm (of_nat k),
                                         add_assoc_aux1, myint.add_comm b]
| a          (of_nat n) (of_nat k) := by rw [myint.add_comm, myint.add_comm a, ← add_assoc_aux1,
                                         myint.add_comm a, myint.add_comm (of_nat k)]
| -[1+ m]    -[1+ n]    (of_nat k) := add_assoc_aux2 _ _ _
| -[1+ m]    (of_nat n) -[1+ k]    := by rw [myint.add_comm, ← add_assoc_aux2, myint.add_comm (of_nat n),
                                         ← add_assoc_aux2, myint.add_comm -[1+ m] ]
| (of_nat m) -[1+ n]    -[1+ k]    := by rw [myint.add_comm, myint.add_comm (of_nat m),
                                         myint.add_comm (of_nat m), ← add_assoc_aux2,
                                         myint.add_comm -[1+ k] ]
| -[1+ m]    -[1+ n]    -[1+ k]    := by simp [add_succ, mynat.add_comm, mynat.add_left_comm, neg_of_nat_of_succ]

end addition

section negation

lemma of_nat_zero : of_nat (0 : mynat) = (0 : myint) := rfl

lemma sub_nat_self : ∀ n, sub_nat_nat n n = 0
| 0        := rfl
| (succ m) := begin rw [sub_nat_nat_of_sub_eq_zero, mynat.sub_self, of_nat_zero], rw mynat.sub_self end

end negation

local attribute [simp] sub_nat_self

section negation

protected lemma add_left_neg : ∀ a : ℤ, -a + a = 0
| (of_nat 0)        := rfl
| (of_nat (succ m)) := by simp
| -[1+ m]           := by simp

protected lemma add_right_neg (a : ℤ) : a + -a = 0 := by rw [myint.add_comm', myint.add_left_neg]

end negation

section multiplication

protected lemma mul_comm : ∀ a b : ℤ, a * b = b * a
| (of_nat m) (of_nat n) := by simp [mynat.mul_comm']
| (of_nat m) -[1+ n]    := by simp [mynat.mul_comm']
| -[1+ m]    (of_nat n) := by simp [mynat.mul_comm']
| -[1+ m]    -[1+ n]    := by simp [mynat.mul_comm']

lemma of_nat_mul_neg_of_nat (m : ℕ) :
   ∀ n, of_nat m * neg_of_nat n = neg_of_nat (m * n)
| 0        := rfl
| (succ n) := begin unfold neg_of_nat, simp end

lemma neg_of_nat_mul_of_nat (m n : ℕ) :
    neg_of_nat m * of_nat n = neg_of_nat (m * n) :=
begin rw myint.mul_comm, simp [of_nat_mul_neg_of_nat, mynat.mul_comm'] end

lemma neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * neg_of_nat n = of_nat (succ m * n)
| 0        := rfl
| (succ n) := begin unfold neg_of_nat, simp end

lemma neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) :
  neg_of_nat n * -[1+ m] = of_nat (n * succ m) :=
begin rw myint.mul_comm, simp [neg_succ_of_nat_mul_neg_of_nat, mynat.mul_comm'] end

end multiplication

local attribute [simp] of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat
  neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

/- TRY SOME STUFF -/

local attribute [simp] of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ
  neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat

local attribute [simp] of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat
  neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

section multiplication

protected lemma mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| (of_nat m) (of_nat n) (of_nat k) := by simp [mynat.mul_assoc']
| (of_nat m) (of_nat n) -[1+ k]    := by simp [mynat.mul_assoc']
| (of_nat m) -[1+ n]    (of_nat k) := by simp [mynat.mul_assoc']
| (of_nat m) -[1+ n]   -[1+ k]     := by simp [mynat.mul_assoc']
| -[1+ m]    (of_nat n) (of_nat k) := by simp [mynat.mul_assoc']
| -[1+ m]    (of_nat n) -[1+ k]    := by simp [mynat.mul_assoc']
| -[1+ m]    -[1+ n]    (of_nat k) := by simp [mynat.mul_assoc']
| -[1+ m]    -[1+ n]   -[1+ k]     := by simp [mynat.mul_assoc']

protected lemma mul_zero : ∀ (a : ℤ), a * 0 = 0
| (of_nat m) := rfl
| -[1+ m]    := rfl

protected lemma zero_mul (a : ℤ) : 0 * a = 0 := myint.mul_comm a 0 ▸ myint.mul_zero a

lemma neg_of_nat_eq_sub_nat_nat_zero : ∀ n, neg_of_nat n = sub_nat_nat 0 n
| 0        := rfl
| (succ n) := rfl

lemma of_nat_mul_sub_nat_nat (m n k : ℕ) :
  of_nat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) :=
begin
  have h₀ : m > 0 ∨ 0 = m,
    exact decidable.lt_or_eq_of_le (zero_le _),
  cases h₀ with h₀ h₀,
  { have h := mynat.lt_or_ge n k,
    cases h with h h,
    { have h' : m * n < m * k,
        exact mynat.mul_lt_mul_of_pos_left h h₀,
      rw [sub_nat_nat_of_lt h, sub_nat_nat_of_lt h'],
      simp, rw [succ_pred_eq_of_pos (mynat.sub_pos_of_lt h)],
      rw [← neg_of_nat_of_succ, mynat.mul_sub_left_distrib],
      rw [← succ_pred_eq_of_pos (mynat.sub_pos_of_lt h')], reflexivity },
    have h' : m * k ≤ m * n,
      exact mul_le_mul_left _ h,
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_le h'], simp,
    rw [mynat.mul_sub_left_distrib]
  },
  have h₂ : of_nat 0 = 0, exact rfl,
  subst h₀, simp [h₂, myint.zero_mul, mynat.zero_mul'],
end

lemma zero_eq : zero = 0 := rfl

lemma neg_of_nat_add (m n : ℕ) :
  neg_of_nat m + neg_of_nat n = neg_of_nat (m + n) :=
begin
  cases m,
  {  cases n,
    { simp [zero_eq], reflexivity },
      simp [zero_eq, mynat.zero_add'], reflexivity },
  cases n,
  { simp [zero_eq], reflexivity },
  simp [mynat.succ_add'], reflexivity
end

lemma neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) :
  -[1+ m] * sub_nat_nat n k = sub_nat_nat (succ m * k) (succ m * n) :=
begin
  have h := mynat.lt_or_ge n k,
  cases h with h h,
  { have h' : succ m * n < succ m * k,
      exact mynat.mul_lt_mul_of_pos_left h (mynat.succ_pos m),
    rw [sub_nat_nat_of_lt h, sub_nat_nat_of_le (le_of_lt h')],
    simp [succ_pred_eq_of_pos (mynat.sub_pos_of_lt h), mynat.mul_sub_left_distrib]},
  have h' : n > k ∨ k = n,
    exact decidable.lt_or_eq_of_le h,
  cases h' with h' h',
  { have h₁ : succ m * n > succ m * k,
      exact mynat.mul_lt_mul_of_pos_left h' (mynat.succ_pos m),
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_lt h₁], simp [mynat.mul_sub_left_distrib, mynat.mul_comm'],
    rw [mynat.mul_comm' k, mynat.mul_comm' n, ← succ_pred_eq_of_pos (mynat.sub_pos_of_lt h₁),
        ← neg_of_nat_of_succ],
    reflexivity },
  subst h', simp, reflexivity
end

end multiplication

local attribute [simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

section multiplication

protected lemma distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (of_nat m) (of_nat n) (of_nat k) := by simp [mynat.left_distrib]
| (of_nat m) (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw ← sub_nat_nat_add, reflexivity end
| (of_nat m) -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [myint.add_comm, ← sub_nat_nat_add], reflexivity end
| (of_nat m) -[1+ n]   -[1+ k]     := begin simp, rw [← mynat.left_distrib, succ_add', add_succ], end
| -[1+ m]    (of_nat n) (of_nat k) := begin simp [mynat.mul_comm'], rw [← mynat.right_distrib, mynat.mul_comm'] end
| -[1+ m]    (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [myint.add_comm, ← sub_nat_nat_add], reflexivity end
| -[1+ m]    -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [← sub_nat_nat_add], reflexivity end
| -[1+ m]    -[1+ n]   -[1+ k]     := begin simp, rw [← mynat.left_distrib, succ_add', add_succ] end

protected lemma distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c :=
begin rw [myint.mul_comm, myint.distrib_left], simp [myint.mul_comm] end

protected def one  : ℤ := of_nat 1

instance : has_one ℤ := ⟨myint.one⟩

protected lemma one_mul : ∀ (a : ℤ), (1 : ℤ) * a = a
| (of_nat n) := show of_nat (1 * n) = of_nat n, by rw mynat.one_mul'
| -[1+ n]    := show -[1+ (1 * n)] = -[1+ n], by rw mynat.one_mul'

protected lemma mul_one (a : ℤ) : a * 1 = a :=
by rw [myint.mul_comm, myint.one_mul]

protected lemma zero_ne_one : (0 : myint) ≠ 1 :=
begin
  intro h,
  apply mynat.zero_ne_one,
  apply myint.of_nat.inj h,
end

end multiplication

end myint

end exlean