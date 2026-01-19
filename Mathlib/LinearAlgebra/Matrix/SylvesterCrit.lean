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
fun k => ⟨k.val, lt_trans k.isLt i.isLt⟩

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
    · ext j k
      exact IsHermitian.apply h ⟨↑j, finCast._proof_1 i j⟩ ⟨↑k, finCast._proof_1 i k⟩
      --leading minor is hermitian
      --because M.leadingMinor i j = M i j = star (M j i) = star (M.leadingMinor j i)
    · intro x hx
      let x2sup : Finset (Fin n) := {
        val := x.support.val.map (fun j => finCast i j)
        nodup := by
          refine Multiset.Nodup.map ?_ ?_
          · exact injective_of_le_imp_le (fun j ↦ finCast i j) fun {x y} a ↦ a
          · exact x.support.nodup
        }
      let x2fun : Fin n → R := fun (k : Fin n) =>
          if isLt : k.val < i then
            x ⟨k.val, isLt⟩
          else
            0 -- x2 k = x k if k ≤ i, 0 if not
      let x2: Fin n →₀ R :=
        { support := x2sup
          toFun := x2fun
          mem_support_toFun := by
            let h := x.mem_support_toFun
            intro a
            by_cases H: a.val < i
            · let a': Fin i := {
                val := a.val
                isLt := by exact H
              }
              have h1 : a ∈ x2sup ↔ a' ∈ x.support := by sorry
              have h2 : (x2fun a ≠ 0) ↔ (x.toFun a' ≠ 0) := by sorry
              specialize h a'
              rw [h1,h2]
              exact h
            · push_neg at H
              have h1 : (a ∉ x2sup) := by sorry
              have h2 : x2fun a  = 0 := by sorry
              exact (iff_false_left h1).mpr fun a ↦ a h2
        }
      have hx2 : x2 ≠ 0 := by
        refine Finsupp.ne_iff.mpr ?_
        rw [Finsupp.ne_iff] at hx
        obtain ⟨a, ha⟩ := hx
        use finCast i a
        have : x2 (finCast i a) = x a := by exact dif_pos a.isLt
        rw[this]
        exact ha
      have : (x.sum fun j xj ↦ x.sum fun k xk ↦ star xj * M.leadingMinor i j k * xk) =
        (x2.sum fun j xj ↦ x2.sum fun k xk ↦ star xj * M j k * xk) := by
          nth_rw 2 [show x.sum = fun g ↦ ∑ a ∈ x.support, g a (x a) from rfl]
          rw [show
              (x.sum fun j xj ↦
                  (fun g ↦ ∑ a ∈ x.support, g a (x a)) fun k xk ↦
                    star xj * M.leadingMinor i j k * xk) =
                ∑ a ∈ x.support,
                  (fun j xj ↦
                      (fun g ↦ ∑ a ∈ x.support, g a (x a)) fun k xk ↦
                        star xj * M.leadingMinor i j k * xk)
                    a (x a)
              from rfl]
          nth_rw 2 [show x2.sum = fun g ↦ ∑ a ∈ x2.support, g a (x2 a) from rfl]
          rw [show
              (x2.sum fun j xj ↦
                  (fun g ↦ ∑ a ∈ x2.support, g a (x2 a)) fun k xk ↦
                    star xj * M j k * xk) =
                ∑ a ∈ x2.support,
                  (fun j xj ↦
                      (fun g ↦ ∑ a ∈ x2.support, g a (x2 a)) fun k xk ↦
                        star xj * M j k * xk)
                    a (x2 a)
              from rfl]
          sorry --this is by def of x2.support
        --these definitions are always weird
      rw[this]
      exact hM.2 hx2
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
