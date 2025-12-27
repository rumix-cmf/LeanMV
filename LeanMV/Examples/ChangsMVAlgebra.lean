/-
# Chang's MV-algebra C
-/

import LeanMV.Algebra.MVAlgebra.FromGamma

import Mathlib

namespace ChangsMVAlgebra

/- ℤ lex ℤ is an abelian ℓ-group with strong unit (1, 0). -/
def LexZZ_LuAddCommGroup : LuAddCommGroup :=
{
  G := Lex (ℤ × ℤ)
  u := (1, 0)
  unit_nonneg := by
    left
    simp
  dominates := by
    intro x
    refine ⟨x.1.natAbs + 1, ?_⟩
    left
    simp
    calc
      x.1 ≤ |x.1| := le_abs_self _
      _ < _ + 1 := Int.lt_succ _
}

def C : Type := Γ LexZZ_LuAddCommGroup

instance : MVAlgebra C := by
  dsimp [C]
  infer_instance

end ChangsMVAlgebra
