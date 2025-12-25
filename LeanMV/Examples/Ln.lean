/-
# Finite MV-algebras

This file defines the finite MV-algebras `Ł n` arising from the Łukasiewicz
chain on `n + 1` elements.
-/

import LeanMV.Algebra.MVAlgebra.Basic

def Ł (n : ℕ) := Fin (n + 1)

namespace Ł

/- Truncated addition on `Ł n`. -/
def add (n : ℕ) (x y : Ł n) : Ł n :=
⟨
  Nat.min n (x.val + y.val), by
    have h : Nat.min n (x.val + y.val) ≤ n := Nat.min_le_left _ _
    exact Nat.lt_succ_of_le h
⟩
infixl:65 " + " => add _

/- Addition is associative. -/
theorem add_assoc (n : ℕ) (x y z : Ł n) : x + y + z = x + (y + z) := by
  apply Fin.ext
  simp [add, Nat.min]
  simp [← Nat.add_min_add_right, ← Nat.add_min_add_left]
  repeat rw [← Nat.min_assoc]
  simp [Nat.add_assoc]

/- Addition is commutative. -/
theorem add_comm (n : ℕ) (x y : Ł n) : x + y = y + x := by
  apply Fin.ext
  simp [add]
  simp [Nat.add_comm]

/- Zero element of `Ł n`.-/
def zero (n : ℕ) : Ł n :=
⟨
  0, by
    exact Nat.succ_pos n
⟩

/- Zero is a left identity. -/
@[simp] theorem zero_add (n : ℕ) (x : Ł n) : zero n + x = x := by
  apply Fin.ext
  simp [add, zero]
  apply Nat.min_eq_right
  exact x.is_le

/- Zero is a right identity. -/
@[simp] theorem add_zero (n : ℕ) (x : Ł n) : x + zero n = x := by
  rw [add_comm]
  rw [zero_add]

/- Multiples. -/
def nsmul (n : ℕ) : ℕ → Ł n → Ł n
| 0, _ => zero n
| Nat.succ k, x => nsmul n k x + x

/- Łukasiewicz negation. -/
def neg (n : ℕ) (x : Ł n) : Ł n :=
⟨
  n.sub x.val, by
  have h : n.sub x.val ≤ n := Nat.sub_le _ _
  exact Nat.lt_succ_of_le h
⟩

/- Double negation. -/
@[simp] theorem neg_neg (n : ℕ) (x : Ł n) : neg n (neg n x) = x := by
  apply Fin.ext
  simp [neg]
  exact Nat.sub_sub_self (x.is_le)

/- Top element of `Ł n`. -/
def one (n : ℕ) : Ł n :=
⟨
  n, by
    exact Nat.lt_succ_self n
⟩

/- Negation of zero is one. -/
lemma neg_zero (n : ℕ) : neg n (zero n) = one n := by
  apply Fin.ext
  simp [neg, zero, one]

/- Adding one yields one. -/
theorem add_one_eq_one (n : ℕ) (x : Ł n) :
  x + neg n (zero n) = neg n (zero n) := by
  apply Fin.ext
  simp [neg_zero, one, add]

/- Truncated subtraction. -/
def ominus (n : ℕ) (x y : Ł n) : Ł n :=
  neg n (neg n x + y)
infixl:65 " ⊖ " => ominus _

/- Value of truncated subtraction. -/
@[simp] lemma ominus_val (n : ℕ) (x y : Ł n) :
  (x ⊖ y).val = Nat.max 0 (x.val - y.val) := by
  simp [ominus, add, neg]
  by_cases hyx : y.val ≤ x.val
  · -- case y ≤ x
    have : n - x.val + y.val ≤ n := by
      calc
        n - x.val + y.val
          ≤ n - x.val + x.val := Nat.add_le_add_left hyx _
        _ = n := Nat.sub_add_cancel x.is_le
    simp [Nat.min]
    rw [Nat.min_eq_right this]
    calc
      n - (n - x.val + y.val)
        = n - (n - x.val) - y.val := by rw [Nat.sub_add_eq]
      _ = x.val - y.val := by rw [Nat.sub_sub_self x.is_le]
  · -- case x < y
    have hxy : x.val ≤ y.val := Nat.le_of_not_le hyx
    have hzero : x.val - y.val = 0 := Nat.sub_eq_zero_iff_le.mpr hxy
    simp [hzero]
    have : n ≤ n - x.val + y.val := by
      calc
        n = n - x.val + x.val := by
          symm
          exact Nat.sub_add_cancel x.is_le
        _ ≤ n - x.val + y.val := Nat.add_le_add_left hxy _
    simp [Nat.min]
    rw [Nat.min_eq_left this]
    simp

/- The characteristic MV-algebra axiom. -/
theorem swap (n : ℕ) (x y : Ł n) : (x ⊖ y) + y = (y ⊖ x) + x := by
  apply Fin.ext
  simp [add, Nat.min]
  by_cases hxy : x.val ≤ y.val
  · -- case x ≤ y
    have h₀ : x.val - y.val = 0 := Nat.sub_eq_zero_iff_le.mpr hxy
    simp [h₀]
    simp [Nat.sub_add_cancel hxy]
  · -- case y ≤ x
    have hyx : y.val ≤ x.val := Nat.le_of_not_le hxy
    have h₀ : y.val - x.val = 0 := Nat.sub_eq_zero_iff_le.mpr hyx
    simp [h₀]
    simp [Nat.sub_add_cancel hyx]

/- `Ł n` is indeed an MV-algebra. -/
instance (n : ℕ) : MVAlgebra (Ł n) :=
{
  add := add n,
  add_assoc := add_assoc n,
  zero := zero n,
  zero_add := zero_add n,
  add_zero := add_zero n,
  nsmul := nsmul n,
  add_comm := add_comm n,
  neg := neg n,
  neg_neg := neg_neg n,
  add_one_eq_one := add_one_eq_one n,
  swap := swap n
}

end Ł
