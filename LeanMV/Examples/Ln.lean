/-
# The finite MV-algebra Łₙ

The finite MV-algebra Łₙ, defined (up to isomorphism) via Mundici's Γ
functor: Łₙ₊₁ ≅ Γ(ℤ, n).
-/

import LeanMV

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace Ln

/- (ℤ, n) is an abelian ℓ-group with strong unit n > 0. -/
def Z_LuAddCommGroup (n : ℕ) : LuAddCommGroup :=
{
  G := ℤ
  u := (Nat.succ n : ℤ)
  unit_nonneg := by
    apply le_of_lt
    exact_mod_cast Nat.succ_pos n
  dominates := by
    intro x
    refine ⟨x.natAbs, ?_⟩
    have : x ≤ n.succ • x.natAbs := by
      calc
        x ≤ x.natAbs := Int.le_natAbs
        _ ≤ n.succ • x.natAbs := by
          apply le_self_nsmul
          constructor
          · exact n.succ_ne_zero
    rw [nsmul_eq_mul, mul_comm, ← nsmul_eq_mul]
    exact this
}

/- Łₙ = Γ(ℤ, n-1) = {0, 1, ..., n-1} -/
def Ł : ℕ → Type
| 0 => PUnit
| 1 => PUnit
| n + 2 => Γ (Z_LuAddCommGroup n)

instance (n : ℕ) : MVAlgebra (Ł (n+2)) := by
  dsimp [Ł]
  infer_instance

end Ln

-- ----------------------------------------------------------------------------
section SanityChecks

open Ln

example : (Z_LuAddCommGroup 0).G = ℤ := rfl
example : (Z_LuAddCommGroup 0).u = (1 : ℤ) := rfl
example : Ł 2 = Γ (Z_LuAddCommGroup 0) := rfl
example : Ł 2 = {x : ℤ // 0 ≤ x ∧ x ≤ (1 : ℤ) } := rfl

end SanityChecks
