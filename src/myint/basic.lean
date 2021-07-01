import  tactic.structure_helper tactic.pure_maths

namespace MyInt

class MyInt {α : Type} extends 
  has_add α, has_one α, has_mul α, has_inv α, has_zero α, has_neg α : Type :=
(add_comm : ∀ a b : α, a + b = b + a)
(add_zero : ∀ a, a + 0 = a)
(mul_one : ∀ a, a * 1 = a)
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)

variables {G : Type} [@MyInt G]

@[reducible] protected def MyInt.sub (a b : G) : G := a + -b

instance add_group_has_sub : has_sub G := ⟨MyInt.sub⟩

lemma sub_eq_add_neg (a b : G) : a - b = a + -b := rfl

constants (myint : Type) [myint_inst : @MyInt myint]

localized "notation `ℤ` := myint" in MyInt

export MyInt (myint myint_inst)

end MyInt