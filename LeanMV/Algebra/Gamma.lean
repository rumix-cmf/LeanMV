/-
# The Γ functor (carrier level)

This file defines the carrier of Mundici's Γ functor.

Given a lattice-ordered abelian group with strong unit `G : LuAddCommGroup`,
ΓG is defined as the closed interval `[0, G.u]` in the underlying ℓ-group.

At this stage, Γ is only a subtype:
* elements are values `x : G.G` together with proofs `0 ≤ x ≤ G.u`;
* no algebraic structure is defined yet;
* no functorial action on morphisms is provided.

The purpose of this file is to isolate the order-theoretic content of Γ from
the algebraic facts that will be proved later (see `FromGamma.lean`).
-/

import LeanMV.Algebra.LuAddCommGroup

def Γ (G : LuAddCommGroup) :=
  { x : G.G // 0 ≤ x ∧ x ≤ G.u }

namespace Gamma
section Basic
variable {G : LuAddCommGroup}

@[simp] lemma nonneg (x : Γ G) : 0 ≤ x.val := x.property.1

@[simp] lemma le_u (x : Γ G) : x.val ≤ G.u := x.property.2

/- The strong unit and zero are elements of ΓG. -/
def u (G : LuAddCommGroup) : Γ G := by
  refine ⟨G.u, ?_⟩
  constructor
  · exact G.unit_nonneg
  · exact le_refl G.u

def zero (G : LuAddCommGroup) : Γ G := by
  refine ⟨0, ?_⟩
  constructor
  · exact le_refl 0
  · exact G.unit_nonneg

end Basic
end Gamma
