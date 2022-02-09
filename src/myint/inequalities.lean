import myint.basic



namespace exlean

namespace myint

open_locale mynum

--set_option pp.notation false

lemma myint_le_def (a b : ℤ) : a ≤ b ↔ myint_to_int a ≤ myint_to_int b :=
begin
  unfold has_le.le,
  unfold myint_le,
  trivial,
end

/- lemma add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
begin
  rw myint_le_def at h ⊢,
  rw [myint_to_int_add, myint_to_int_add],
  apply int.add_le_add_left h,
end
 -/
end myint

end exlean