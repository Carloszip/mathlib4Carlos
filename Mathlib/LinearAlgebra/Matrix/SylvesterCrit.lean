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

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type v} [CommRing R] [PartialOrder R] [StarRing R]
variable {A : Matrix n n R}

def prinMinor (A : Matrix n n R) (i : n) : Matrix n n R := A --this should be the principal minor of length i × i

theorem isPosDef_if_Pos_Det_PrinMinors {M : Matrix n n R}
{h : ∀ i : n , (M.prinMinor i).det > 0 } : M.PosDef := by sorry

theorem Pos_Det_PrinMinors_if_isPosDef {M : Matrix n n R}
{h : M.IsHermitian} {hM : M.PosDef} : ∀ i : n , (M.prinMinor i).det > 0 := by sorry

--test

theorem isPosDef_iff_Pos_Det_PrinMinors {M : Matrix n n R}
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : n , (M.prinMinor i).det > 0) := by
  constructor
  · intro h1
    apply Pos_Det_PrinMinors_if_isPosDef
    · exact h
    · exact h1
  · intro h2
    apply isPosDef_if_Pos_Det_PrinMinors
    exact fun i ↦ h2 i
