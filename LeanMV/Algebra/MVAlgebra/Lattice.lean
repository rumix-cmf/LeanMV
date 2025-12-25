/-
# Lattice structure on MV-algebras

This file shows that the natural order on an MV-algebra induces a bounded
lattice structure.

The natural order on an MV-algebra is a lattice-order with
- `x ⊔ y = (x ⊙ ~y) + y`,
- `x ⊓ y = (x + ~y) ⊙ y`.
The top and bottom elements are respectively `~0` and `0`.
-/

import LeanMV.Algebra.MVAlgebra.Order
import Mathlib.Order.Lattice
import Mathlib.Order.Bounds.Basic

namespace MVAlgebra
section BoundedLattice

variable {α : Type} [MVAlgebra α]

def sup (x y : α) : α := (x ⊙ ~y) + y
infixl:68 " ⊔ " => sup

lemma sup_comm (x y : α) : x ⊔ y = y ⊔ x := by
  calc
    x ⊔ y = ~(~x + y) + y := by rw [sup, odot, neg_neg]
    _ = ~(~y + x) + x := by rw [swap]
    _ = ~(~y + ~~x) + x := by nth_rw 1 [← neg_neg x]

lemma le_sup_right (x y : α) : y ≤ x ⊔ y := by
  have y_le_sup : le_4 y (x ⊔ y) := by
    rw [le_4, sup]
    rw [← ominus]
    rw [add_comm]
    use x ⊖ y
  exact ((le_charac y (x ⊔ y)).out 0 3).mpr y_le_sup

lemma le_sup_left (x y : α) : x ≤ x ⊔ y := by
  rw [sup_comm]
  exact le_sup_right y x

lemma sup_le (x y z : α) : x ≤ z → y ≤ z → x ⊔ y ≤ z := by
  intro x_le_z y_le_z
  have h₁ : x ≤ z ↔ ~x + z = ~0 := le_iff x z
  rw [h₁] at x_le_z
  have h₂ : y ≤ z ↔ y + (z ⊖ y) = z := (le_charac y z).out 0 2
  rw [h₂] at y_le_z
  have sup_le_z_eq : ~(x ⊔ y) + z = ~0 → x ⊔ y ≤ z :=
    (le_iff (x ⊔ y) z).mpr
  apply sup_le_z_eq
  unfold sup
  rw [← y_le_z]
  rw [← add_assoc]
  rw [← neg_neg (x ⊙ ~y)]
  nth_rw 2 [← neg_neg y]
  rw [← odot]
  rw [← ominus]
  rw [swap']
  nth_rw 2 [odot]
  simp
  rw [add_assoc]
  rw [add_assoc (~x) (y) (z ⊖ y)]
  rw [y_le_z]
  rw [x_le_z]
  simp

def inf (x y : α) : α := (x + ~y) ⊙ y
infixl:69 " ⊓ " => inf

lemma duality (x y : α) : x ⊓ y = ~(~x ⊔ ~y) := by
  unfold sup inf
  unfold odot
  simp

lemma duality' (x y : α) : x ⊔ y = ~(~x ⊓ ~y) := by
  rw [duality]
  simp

lemma inf_comm (x y : α) : x ⊓ y = y ⊓ x := by
  repeat rw [duality]
  rw [sup_comm]

lemma inf_le_left (x y : α) : x ⊓ y ≤ x := by
  rw [duality]
  nth_rw 2 [← neg_neg x]
  apply le_neg (~x) (~x ⊔ ~y)
  exact le_sup_left (~x) (~y)

lemma inf_le_right (x y : α) : x ⊓ y ≤ y := by
  rw [inf_comm]
  exact inf_le_left y x

lemma le_inf (z x y : α) : z ≤ x → z ≤ y → z ≤ x ⊓ y := by
  intro zx zy
  rw [duality, ← neg_neg z]
  apply le_neg (~x ⊔ ~y) (~z)
  apply sup_le
  · apply le_neg
    exact zx
  · apply le_neg
    exact zy

instance : Lattice α :=
{
  sup := sup,
  le_sup_left := le_sup_left,
  le_sup_right := le_sup_right,
  sup_le := sup_le,
  inf := inf,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
}

lemma le_top (x : α) : x ≤ ~0 := by
  apply (le_iff x (~0)).mpr
  rw [add_one_eq_one]

lemma bot_le (x : α) : 0 ≤ x := by
  apply (le_iff 0 x).mpr
  rw [add_comm]
  rw [add_one_eq_one]

instance : BoundedOrder α :=
{
  top := ~0,
  le_top := le_top,
  bot := 0,
  bot_le := bot_le
}

end BoundedLattice
end MVAlgebra
