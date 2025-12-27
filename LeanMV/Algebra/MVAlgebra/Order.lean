/-
# Order structure on MV-algebras

This file defines the natural partial order intrinsic to all MV-algebras.

Several equivalent characterisations of the order relation are provided, and
basic order-theoretic properties are established.
-/

import LeanMV.Algebra.MVAlgebra.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Order.Defs.PartialOrder

-- # Natural order

namespace MVAlgebra
section NaturalOrder

variable {α : Type} [MVAlgebra α]

def le (x y : α) : Prop := ~x + y = ~0
instance : LE α :=
{
  le := le
}
/- Helper lemma to rewrite `≤` into its definition. -/
lemma le_iff (x y : α) : x ≤ y ↔ ~x + y = ~0 := Iff.rfl

lemma le_neg (x y : α) : x ≤ y → ~y ≤ ~x := by
  intro h
  simp [le_iff]
  rw [add_comm]
  exact h

/-
Equivalent definitions of natural order. We give three more definitions and
prove their equivalence:
1. `~x ⊕ y = ~0`
2. `x ⊖ y = 0`
3. `x ⊕_(y ⊖ x) = y`
4. `∃ z, x + z = y`.
-/
def le_2 (x y : α) : Prop := x ⊖ y = 0
def le_3 (x y : α) : Prop := x + (y ⊖ x) = y
def le_4 (x y : α) : Prop := ∃ z, x + z = y

lemma le_12 (x y : α) : x ≤ y → le_2 x y := by
  rw [le_2]
  intro h
  rw [ominus, odot]
  simp
  rw [h]
  simp

lemma le_23 (x y : α) : le_2 x y → le_3 x y := by
  rw [le_2, le_3]
  intro h
  rw [add_comm]
  rw [swap']
  rw [h]
  simp

lemma le_34 (x y : α) : le_3 x y → le_4 x y := by
  rw [le_3, le_4]
  intro h
  exact ⟨y ⊖ x, h⟩

lemma le_41 (x y : α) : le_4 x y → x ≤ y := by
  rw [le_4]
  intro h
  rw [le_iff]
  rcases h with ⟨z, hz⟩
  rw [← hz]
  rw [← add_assoc]
  nth_rw 2 [add_comm]
  rw [add_neg]
  rw [add_comm]
  rw [add_one]

theorem le_charac (x y : α) :
List.TFAE [le x y, le_2 x y, le_3 x y, le_4 x y] := by
  tfae_have 1 → 2 := le_12 x y
  tfae_have 2 → 3 := le_23 x y
  tfae_have 3 → 4 := le_34 x y
  tfae_have 4 → 1 := le_41 x y
  tfae_finish

/- `≤` is indeed a partial order. -/
lemma le_refl (x : α) : x ≤ x := by
  rw [le_iff]
  rw [add_comm]
  rw [add_neg]

/- `≤` is antisymmetric. -/
lemma le_antisymm (x y : α) : x ≤ y → y ≤ x → x = y := by
  intro x_le_y y_le_x
  have h₁ : x ≤ y ↔ le_3 x y := (le_charac x y).out 0 2
  have h₂ : y ≤ x ↔ le_2 y x := (le_charac y x).out 0 1
  rw [h₁, le_3] at x_le_y
  rw [h₂, le_2] at y_le_x
  calc
    x = x + 0 := by simp
    _ = x + (y ⊖ x) := by rw [y_le_x]
    _ = y := by rw [x_le_y]

/- `≤` is transitive. -/
lemma le_trans (x y z : α) : x ≤ y → y ≤ z → x ≤ z := by
  intro h₁ h₂
  have h₁' : x ≤ y ↔ le_4 x y := (le_charac x y).out 0 3
  have h₂' : y ≤ z ↔ le_4 y z := (le_charac y z).out 0 3
  rw [h₁', le_4] at h₁
  rw [h₂', le_4] at h₂
  rcases h₁ with ⟨u, h₁u⟩
  rcases h₂ with ⟨v, h₂v⟩
  have x_le_z : le_4 x z := by
    rw [le_4]
    rw [← h₂v]
    rw [← h₁u]
    -- use u + v
    refine ⟨u+v, ?_⟩
    rw [add_assoc]
  exact ((le_charac x z).out 0 3).mpr x_le_z

instance : PartialOrder α :=
{
  le := le,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm
}

end NaturalOrder
end MVAlgebra
