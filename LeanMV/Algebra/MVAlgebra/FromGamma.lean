/-
# MV-algebra defined by Mundici's Γ functor

This file proves that ΓG is an MV-algebra when equipped with the following
operations:
* truncated addition x ⊕ y = u ⊓ (x + y);
* negation ~x = u - x.
-/

import LeanMV.Algebra.Gamma
import LeanMV.Algebra.MVAlgebra.Basic

namespace Gamma
variable {G : LuAddCommGroup}

/- Truncated addition on ΓG is defined as `G.u ⊓ (x + y)` in the underlying
ℓ-group. -/
def add (x y : Γ G) : Γ G := by
  refine ⟨G.u ⊓ (x.val + y.val), ?_⟩
  constructor
  · -- 0 ≤ u ⊓ (x + y)
    apply le_inf
    · exact G.unit_nonneg
    · calc
        0 ≤ x.val := by simp
        _ = x.val + 0 := by simp
        _ ≤ x.val + y.val := add_le_add_left (nonneg y) x.val
  · -- u ⊓ (x + y) ≤ u
    exact (inf_le_left : G.u ⊓ (x.val + y.val) ≤ G.u)
scoped infixl:65 " + " => add

lemma add_assoc (x y z : Γ G) : x + y + z = x + (y + z) := by
  apply Subtype.ext
  simp [add]
  simp [inf_add, add_inf, inf_inf_distrib_left]
  simp [AddSemigroup.add_assoc]

lemma add_comm (x y : Γ G) : x + y = y + x := by
  apply Subtype.ext
  simp [add, AddCommGroup.add_comm]

@[simp] lemma zero_add (x : Γ G) : zero G + x = x := by
  apply Subtype.ext
  simp [add, zero]

@[simp] lemma add_zero (x : Γ G) : x + zero G = x := by
  rw [add_comm]
  exact zero_add x

def nsmul : ℕ → Γ G → Γ G
| 0, _ => zero G
| Nat.succ n, x => nsmul n x + x

def neg (x : Γ G) : Γ G := by
  refine ⟨G.u - x.val, ?_⟩
  constructor
  · -- 0 ≤ u - x
    have : x.val - x.val ≤ G.u - x.val := sub_le_sub_right x.property.2 x.val
    rw [sub_self] at this
    exact this
  · -- u - x ≤ u
    apply sub_le_self
    exact x.property.1
scoped prefix:100 "~" => neg

@[simp] lemma neg_neg (x : Γ G) : ~~x = x := by
  simp [neg]

lemma neg_zero : ~(zero G) = u G := by
  apply Subtype.ext
  simp [u, zero, neg]

@[simp] lemma add_one (x : Γ G) : x + ~zero G = ~(zero G) := by
  apply Subtype.ext
  simp [neg_zero, add, u]

def ominus (x y : Γ G) : Γ G := ~(~x + y)
infixl:65 " ⊖ " => ominus

lemma ominus_val (x y : Γ G) : (x ⊖ y).val = 0 ⊔ (x.val - y.val) := by
  simp [ominus, add, neg]
  simp [sub_inf]
  simp [sub_add_comm]

lemma swap' (x y : Γ G) : (x ⊖ y) + y = (y ⊖ x) + x := by
  apply Subtype.ext
  simp [add, ominus_val]
  simp [sup_add, sup_comm]

lemma swap (x y : Γ G) : ~(~x + y) + y = ~(~y + x) + x := by
  repeat rw [← ominus]
  exact swap' x y

instance (G : LuAddCommGroup) : MVAlgebra (Γ G) :=
{
  add := add
  add_assoc := add_assoc
  zero := zero G
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  add_comm := add_comm
  neg := neg
  neg_neg := neg_neg
  add_one := add_one
  swap := swap
}

end Gamma
