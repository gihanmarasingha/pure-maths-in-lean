import group.power_lemmas strong_induction.well_ordering_principle data.nat.basic tactic.linarith

universe u

namespace exlean

open group

variables {G : Type u} [group G] {a b : G}

def is_of_finite_order (a : G) := set.nonempty (pow_eq_one_set a)

def has_order (a : G) (n : ℕ) := exlean.min_element n (pow_eq_one_set a)

noncomputable theory

open_locale classical

noncomputable def order_of (g : G) : ℕ :=
if h : (is_of_finite_order g) then
begin
  rw [is_of_finite_order, set.nonempty_def] at h,
  exact classical.some (well_ordering_principle h),
end
else 0

lemma order_eq_zero_of_not_of_finite_order {g : G}
(h : ¬(is_of_finite_order g)) : order_of g = 0 :=
by rwa [order_of, dif_neg]

lemma pow_order_of_eq_one (x : G) : x ^ order_of x = 1 :=
if h : (is_of_finite_order x) then
begin
  rw [order_of, dif_pos h],
  have h₄ := classical.some_spec (well_ordering_principle h),
  dsimp [pow_eq_one_set, min_element] at h₄,
  exact h₄.1.2,
end
else
by rwa [order_of, dif_neg, pow_zero]

open nat

lemma order_dvd_of_pow_eq_one {g : G} {r : ℕ} (h : g ^ r = 1) : order_of g ∣ r :=
if h₂ : (is_of_finite_order g) then
begin
  rw [order_of, dif_pos h₂],
  have h₃ := classical.some_spec (well_ordering_principle h₂),
  set n := classical.some (well_ordering_principle h₂) with h₄,
  rw ←h₄ at *,
  clear h₄,
  dsimp [min_element, pow_eq_one_set] at h₃,
  have h₄ : r % n + n * (r / n) = r := nat.mod_add_div r n ,
  rw [←h₄, pow_add, pow_mul, h₃.1.2, one_pow, group.mul_one] at h,
  suffices : r % n = 0,
  { rw [this, nat.zero_add] at h₄,
    use (r/n),
    rw h₄, },
  by_contra h₅,
  rw [←ne, ←pos_iff_ne_zero] at h₅,
  suffices : r % n < n,
  { linarith [h₃.2 (r % n) ⟨h₅, h⟩], },
  exact mod_lt _ h₃.1.1,
end
else
begin
  rw [order_eq_zero_of_not_of_finite_order h₂, zero_dvd_iff],
  by_contra h₃,
  apply h₂,
  rw [is_of_finite_order, set.nonempty_def],
  use r,
  rw [pow_eq_one_set, set.mem_set_of_eq],
  apply and.intro _ h,
  rwa [succ_le_iff, pos_iff_ne_zero],
end

end exlean