/-
# MV-algebras

In this file, we define the structure of an **MV-algebra** by extending
`AddCommMonoid` with a negation operation `~` and three defining axioms. We
define the auxiliary operations $⊙$, $⊖$ (`odot`, `ominus`). Finally, we give
different equivalent definitions of the natural order of MV-algebras and prove
some results.

## Main definitions
* `MValgebra`: The core algebraic structure.
* `odot, ominus`: Auxilary operations.
* `le`: The natural order on an MV-algebra.

## Main result
* The natural order on an MV-algebra determines a bounded lattice strtucture.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Logic.Basic
import Mathlib.Tactic.TFAE

-- # Definition of MV-algebra

class HasNegation (α : Type) where
  neg : α → α
prefix:100 "~" => HasNegation.neg

class MValgebra (α : Type) extends AddCommMonoid α, HasNegation α where
  /- Negation is an involution. -/
  neg_neg : ∀ x : α, ~~x = x

  /- The constant $1 = ∼0$ acts as an absorbing element for addition. -/
  add_one_eq_one : ∀ x : α, x + ~0 = ~0

  /- The key axiom that defines the MV-algebra structure. -/
  swap: ∀ x y : α, ~(~x + y) + y = ~(~y + x) + x

namespace MValgebra

section SimpLemmas
variable {α : Type} [MValgebra α]

@[simp] lemma neg_neg_simp (x : α) : ~~x = x :=
  MValgebra.neg_neg x

@[simp] lemma add_one_eq_one_simp (x : α) : x + ~0 = ~0 :=
  MValgebra.add_one_eq_one x

@[simp] lemma add_neg_eq_one (x : α) : x + ~x = ~0 := by
  calc
    x + ~x = x + ~(x + 0) := by nth_rw 2 [← add_zero x]
    _ = x + ~(x + ~~0) := by simp
    _ = ~(~~0 + x) + x := by
      rw [add_comm]
      nth_rw 2 [add_comm]
    _ = ~(~x + ~0) + ~0 := by rw [swap]
    _ = ~0 := by rw [add_one_eq_one]

end SimpLemmas

-- ----------------------------------------------------------------------------
-- # Auxiliary operations

section AuxiliaryOperations
variable {α : Type} [MValgebra α]

def odot (x y : α) : α := ~(~x + ~y)
infixl:70 " ⊙ " => odot

@[simp] lemma odot_assoc (x y z : α) : x ⊙ y ⊙ z = x ⊙ (y ⊙ z) := by
  unfold odot
  simp
  rw [add_assoc]

@[simp] lemma odot_comm (x y : α) : x ⊙ y = y ⊙ x := by
  unfold odot
  rw [add_comm]

def ominus (x y : α) : α := x ⊙ ~y
infixl:65 " ⊖ " => ominus

lemma ominus_anticomm (x y : α) : y ⊖ x = ~x ⊖ ~y := by
  unfold ominus
  simp

/- We use $⊖$ to rewrite the third axiom. -/
lemma swap' (x y : α) : (x ⊖ y) + y = (y ⊖ x) + x := by
  unfold ominus
  unfold odot
  simp
  rw [swap]

end AuxiliaryOperations

-- ----------------------------------------------------------------------------
-- # Natural order

section NaturalOrder
variable {α : Type} [MValgebra α]

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

-- lemma le_neg (x y : α) : x ≤ y ↔ ~y ≤ ~x := by
--   have h : x ≤ y → ~y ≤ ~x := by
--     intro xy
--     simp [le_iff]
--     rw [add_comm]
--     apply xy
--   have h' : ~y ≤ ~x → x ≤ y := by
--     intro nynx
--     simp [le_iff]
--     rw [add_comm, ← neg_neg y]
--     apply nynx
--   exact ⟨h,h'⟩

-- lemma le_neg' (x y : α) : x ≤ ~y ↔ y ≤ ~x := by
--   have h : x ≤ ~y → y ≤ ~x := by
--     intro xny
--     rw [le_neg]
--     simp
--     exact xny
--   have h' : y ≤ ~x → x ≤ ~y := by
--     intro ynx
--     rw [le_neg]
--     simp
--     exact ynx
--   exact ⟨h,h'⟩

/- Equivalent definitions of natural order. We give three more definitions and
prove their equivalence:
1. $~x ⊕ y = ~0$
2. $x ⊖ y = 0$
3. $x ⊕_(y ⊖ x) = y$
4. $∃ z, x + z = y$. -/
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
  use y ⊖ x

lemma le_41 (x y : α) : le_4 x y → x ≤ y := by
  rw [le_4]
  intro h
  rw [le_iff]
  rcases h with ⟨z, hz⟩
  rw [← hz]
  rw [← add_assoc]
  nth_rw 2 [add_comm]
  rw [add_neg_eq_one]
  rw [add_comm]
  rw [add_one_eq_one]

theorem le_charac (x y : α) :
List.TFAE [le x y, le_2 x y, le_3 x y, le_4 x y] := by
  tfae_have 1 → 2 := le_12 x y
  tfae_have 2 → 3 := le_23 x y
  tfae_have 3 → 4 := le_34 x y
  tfae_have 4 → 1 := le_41 x y
  tfae_finish

/- $≤$ is indeed a partial order. -/
lemma le_refl (x : α) : x ≤ x := by
  rw [le_iff]
  rw [add_comm]
  rw [add_neg_eq_one]

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
    use u + v
    rw [add_assoc]
  exact ((le_charac x z).out 0 3).mpr x_le_z

instance : PartialOrder α :=
{
  le := MValgebra.le,
  le_refl := MValgebra.le_refl,
  le_trans := MValgebra.le_trans,
  le_antisymm := MValgebra.le_antisymm
}

-- ## Lattice structure of MV-algebras

/-
The natural order on an MV-algebra is a lattice-order with
* $x ⊔ y = (x ⊙ ~y) + y$,
* $x ⊓ y = (x + ~y) ⊙ y$.
The top and bottom elements are respectively $~0$ and $0$.
-/

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
  -- rw [duality]
  -- nth_rw 2 [← neg_neg x]
  -- apply le_neg
  -- exact le_sup_left (~x) (~y)
  rw [duality]
  nth_rw 2 [← neg_neg x]
  apply le_neg (~x) (~x ⊔ ~y)
  exact le_sup_left (~x) (~y)

lemma inf_le_right (x y : α) : x ⊓ y ≤ y := by
  rw [inf_comm]
  exact inf_le_left y x

lemma le_inf (z x y : α) : z ≤ x → z ≤ y → z ≤ x ⊓ y := by
  -- intro z_le_x z_le_y
  -- apply le_neg at z_le_x
  -- apply le_neg at z_le_y
  -- have h : ~x ⊔ ~y ≤ ~z := by
  --   apply sup_le
  --   · exact z_le_x
  --   · exact z_le_y
  -- rw [duality]
  -- rw [← neg_neg z]
  -- apply le_neg
  -- exact h
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

end NaturalOrder
end MValgebra
