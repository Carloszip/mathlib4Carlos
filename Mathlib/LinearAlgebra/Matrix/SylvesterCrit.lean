module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

universe v

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : ℕ}
variable {R : Type v} [CommRing R] [PartialOrder R] [StarRing R]
variable {A : Matrix (Fin n) (Fin n) R}

-- this is probably defined somewhere else
def finCast (i : Fin n) : Fin i → Fin n :=
fun k => ⟨k.1, lt_trans k.2 i.2⟩

-- I wasnt able to define this without losing generality, so now n is just a natural number
def leadingMinor (A : Matrix (Fin n) (Fin n) R) (i : Fin n) : Matrix (Fin i) (Fin i) R :=
  A.submatrix (finCast i) (finCast i)

theorem isPosDef_if_Pos_Det_leadingMinors {M : Matrix (Fin n) (Fin n) R}
{h : ∀ i : Fin n , (M.leadingMinor i).det > 0 } : M.PosDef := by sorry

theorem Pos_Det_leadingMinors_if_isPosDef {M : Matrix (Fin n) (Fin n) R}
{h : M.IsHermitian} {hM : M.PosDef} : ∀ i : Fin n , (M.leadingMinor i).det > 0 := by
  intro i
  have : (M.leadingMinor i).PosDef := by
    unfold PosDef
    constructor
    · sorry --leading minor is hermitian
      --because M.leadingMinor i j = M i j = star (M j i) = star (M.leadingMinor j i)
    · intro x hx
      let x2: Fin n → R := sorry -- x2 k = x k if k ≤ i, 0 if not
      have hx2 : x2 ≠ 0 := by sorry
      have : star x ⬝ᵥ M.leadingMinor i *ᵥ x = star x2 ⬝ᵥ M *ᵥ x2 := by sorry
      rw [this]
      exact hM.2 x2 hx2
  sorry--posdef matrices have positive determinant.

theorem isPosDef_iff_Pos_Det_leadingMinors {M : Matrix (Fin n) (Fin n) R}
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : Fin n , (M.leadingMinor i).det > 0) := by
  constructor
  · intro h1
    apply Pos_Det_leadingMinors_if_isPosDef
    · exact h
    · exact h1
  · intro h2
    apply isPosDef_if_Pos_Det_leadingMinors
    exact fun i ↦ h2 i


end Matrix
