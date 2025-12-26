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

--WORKING RIGHT NOW!!!!

def leading_Minor (A : Matrix n n R) (i : n) : Matrix n n R := A --to do
--this should be the leading minor of length i × i

theorem isPosDef_if_pos_Det_LeadMinors {M : Matrix n n R}
{h : ∀ i : n , (M.leading_Minor i).det > 0 } : M.PosDef := by sorry

theorem pos_Det_PrinMinors_if_isPosDef {M : Matrix n n R}
{h : M.IsHermitian} {hM : M.PosDef} : ∀ i : n , (M.prinMinor i).det > 0 := by sorry

theorem isPosDef_iff_Pos_Det_LeadMinors {M : Matrix n n R}
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : n , (M.leading_Minor i).det > 0) := by
  constructor
  · intro h1
    apply pos_Det_LeadMinors_if_isPosDef
    · exact h
    · exact h1
  · intro h2
    apply isPosDef_if_pos_Det_LeadMinors
    exact fun i ↦ h2 i

end Matrix

--hola
--second try
