import equations.algebraic_structures algebra.ordered_ring

namespace exlean -- hide

open_locale mynum -- hide

open myint

namespace pre_group -- hide

instance : monoid myint :=
{ mul_assoc := exlean.myint.mul_assoc,
  one_mul   := exlean.myint.one_mul,
  mul_one   := exlean.myint.mul_one,
  .. }

instance : comm_monoid myint :=
{ mul_comm := exlean.myint.mul_comm,
  .. myint.monoid }

instance : inhabited myint := ⟨myint.of_nat 0⟩

instance : nontrivial myint :=
⟨⟨0, 1, myint.zero_ne_one⟩⟩

instance : comm_ring myint :=
{ add            := myint.add,
  add_assoc      := myint.add_assoc,
  zero           := myint.of_nat 0,
  zero_add       := exlean.pre_group.zero_add,
  add_zero       := exlean.pre_group.add_zero,
  neg            := myint.neg,
  add_left_neg   := myint.add_left_neg,
  add_comm       := myint.add_comm,
  mul            := myint.mul,
  mul_assoc      := myint.mul_assoc,
  one            := myint.one,
  one_mul        := myint.one_mul,
  mul_one        := myint.mul_one,
  sub            := myint.sub,
  left_distrib   := myint.distrib_left,
  right_distrib  := myint.distrib_right,
  mul_comm       := myint.mul_comm, }
/- 
instance : linear_ordered_comm_ring myint :=
{ add_le_add_left := @myint.add_le_add_left,
  mul_pos         := @myint.mul_pos,
  zero_le_one     := le_of_lt myint.zero_lt_one,
  .. myint.comm_ring, .. myint.linear_order, .. myint.nontrivial } -/

end pre_group

end exlean