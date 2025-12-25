/-
# MV-algebras

This file defines the basic structure of an MV-algebra.

An MV-algebra is a commutative monoid equipped with a unary negation satisfying
some characteristic axioms. This file introduces the core `MVAlgebra` typeclass
and the auxiliary operations `⊙`, `⊖`.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NthRewrite

class HasNegation (α : Type) where
  neg : α → α
prefix:100 "~" => HasNegation.neg

class MVAlgebra (α : Type) extends AddCommMonoid α, HasNegation α where
  /- Negation is an involution. -/
  neg_neg : ∀ x : α, ~~x = x

  /- The constant $1 = ∼0$ acts as an absorbing element for addition. -/
  add_one_eq_one : ∀ x : α, x + ~0 = ~0

  /- The key axiom that defines the MV-algebra structure. -/
  swap: ∀ x y : α, ~(~x + y) + y = ~(~y + x) + x

namespace MVAlgebra

section SimpLemmas
variable {α : Type} [MVAlgebra α]

@[simp] lemma neg_neg_simp (x : α) : ~~x = x :=
  MVAlgebra.neg_neg x

@[simp] lemma add_one_eq_one_simp (x : α) : x + ~0 = ~0 :=
  MVAlgebra.add_one_eq_one x

lemma add_neg_eq_one (x : α) : x + ~x = ~0 := by
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
variable {α : Type} [MVAlgebra α]

def odot (x y : α) : α := ~(~x + ~y)
infixl:70 " ⊙ " => odot

/- Addition is associative. -/
lemma odot_assoc (x y z : α) : x ⊙ y ⊙ z = x ⊙ (y ⊙ z) := by
  unfold odot
  simp
  rw [add_assoc]

/- Addition is commutative. -/
lemma odot_comm (x y : α) : x ⊙ y = y ⊙ x := by
  unfold odot
  rw [add_comm]

def ominus (x y : α) : α := x ⊙ ~y
infixl:65 " ⊖ " => ominus

lemma ominus_anticomm (x y : α) : y ⊖ x = ~x ⊖ ~y := by
  simp [ominus, odot_comm]

/- We use `⊖` to rewrite the third axiom. -/
lemma swap' (x y : α) : (x ⊖ y) + y = (y ⊖ x) + x := by
  unfold ominus
  unfold odot
  simp
  rw [swap]

end AuxiliaryOperations
end MVAlgebra
