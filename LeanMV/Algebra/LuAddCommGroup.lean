/-
`LuAddCommGroup` is an additive commutative group equipped with a lattice order
and a distinguished strong unit `u`.

The element `u` is required to be non-negative and to dominate the order in the
following sense: for every element `x`, there exists a natural number `n` such
that `x ≤ n • u`.
-/

import Mathlib.Algebra.Order.Group.Lattice

structure LuAddCommGroup where
  (G : Type)
  [addCommGroup : AddCommGroup G]
  [lattice : Lattice G]
  [addLeftMono : AddLeftMono G]
  [addRightMono : AddRightMono G]
  (u : G)
  (unit_nonneg : 0 ≤ u)
  (dominates : ∀ x : G, ∃ n : ℕ, x ≤ n • u)

attribute [instance]
  LuAddCommGroup.addCommGroup
  LuAddCommGroup.lattice
  LuAddCommGroup.addLeftMono
  LuAddCommGroup.addRightMono

namespace LuAddCommGroup
section Basic
variable {G : LuAddCommGroup}

@[simp] lemma unit_nonneg_simp : 0 ≤ u := unit_nonneg

end Basic
end LuAddCommGroup
