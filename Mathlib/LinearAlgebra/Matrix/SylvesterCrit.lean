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
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.Field.Defs

@[expose] public section

universe v

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : ℕ}
--variable {R : Type v} [RCLike R]
abbrev R := ℝ --we need RClike for posdef implies pos determinant, and partialorder for det>0
variable {A : Matrix (Fin n) (Fin n) R}

-- this is probably defined somewhere else
def finCast (i : Fin n) : Fin (i + 1) → Fin n :=
fun k => ⟨k.val, Nat.lt_of_lt_of_le k.is_lt (Nat.succ_le_of_lt i.is_lt)⟩

-- I wasnt able to define this without losing generality, so now n is just a natural number
def leadingMinor (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
  Matrix (Fin (i + 1)) (Fin (i + 1)) R := A.submatrix (finCast i) (finCast i)

theorem isPosDef_if_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R}
(h : ∀ i : Fin n , (M.leadingMinor i).det > 0) : M.PosDef := by sorry

lemma PosDef_leadingMinor_if_isPosDef {M : Matrix (Fin n) (Fin n) R}
(h : M.IsHermitian) (hM : M.PosDef) (i : Fin n) : (M.leadingMinor i).PosDef := by
  unfold PosDef
  constructor -- it is hermitian and blablabla
  · ext j k -- easy part [done]
    exact IsHermitian.apply h ⟨↑j, finCast._proof_1 i j⟩ ⟨↑k, finCast._proof_1 i k⟩
    -- leading minor is hermitian
    -- because M.leadingMinor i j = M i j = star (M j i) = star (M.leadingMinor j i)
  · intro x hx -- not so easy part [not_done]
    -- we define x2 as an extension of x
    let x2sup : Finset (Fin n) := { -- we define the support
      val := x.support.val.map (fun j => finCast i j)
      nodup := by
        refine Multiset.Nodup.map ?_ ?_
        · exact injective_of_le_imp_le (fun j ↦ finCast i j) fun {x y} a ↦ a
        · exact x.support.nodup
      }
    let x2fun : Fin n → R := fun (k : Fin n) => -- the function
        if isLt : k.val < i + 1 then
          x ⟨k.val, isLt⟩
        else
          0 -- x2 k = x k if k ≤ i, 0 if not
    let x2: Fin n →₀ R := -- and finally the 'vector'
      { support := x2sup
        toFun := x2fun
        mem_support_toFun := by -- hideous junk
          let h := x.mem_support_toFun
          intro a
          by_cases H: a.val < i + 1 -- if a is less than i then it comes from the original x,
          -- else it is 0
          · let a': Fin (i + 1) := {
              val := a.val
              isLt := by exact H
            }
            have h1 : a ∈ x2sup ↔ a' ∈ x.support := by -- needs shortening [not_done]
              constructor
              · intro h
                simp only [x2sup, Finset.mem_def, Multiset.mem_map] at h
                simp only [Finsupp.mem_support_iff, ne_eq]
                obtain ⟨j, hj, heq⟩ := h
                have : a' = j := by
                  refine Fin.val_inj.mp ?_
                  exact Fin.mk.inj_iff.mp (id (Eq.symm heq))
                rw[this]
                exact Finsupp.mem_support_iff.mp hj
              · intro h
                refine mem_def.mpr ?_
                unfold x2sup
                simp only [Multiset.mem_map, mem_val, Finsupp.mem_support_iff, ne_eq]
                use a'
                constructor
                · exact Finsupp.mem_support_iff.mp h
                · exact rfl
            have h2 : (x2fun a ≠ 0) ↔ (x.toFun a' ≠ 0) := by -- this is clear enough [done]
              unfold x2fun
              rw [dif_pos H]
              exact Iff.symm (Iff.of_eq rfl)
            specialize h a'
            rw [h1,h2]
            exact h
          · push_neg at H -- this probably could be clearer [not_done]
            have h1 : (a ∉ x2sup) := by
              simp only [mem_mk, Multiset.mem_map, mem_val, Finsupp.mem_support_iff, ne_eq,
                not_exists, not_and, x2sup]
              intro j hj
              push_neg
              have : (finCast i j).val < i.val + 1 := by
                simp [finCast]
              grw[H] at this
              exact Ne.symm (Fin.ne_of_gt this)
            have h2 : x2fun a  = 0 := by
              simp only [dite_eq_right_iff, x2fun]
              intro h
              linarith
            exact (iff_false_left h1).mpr fun a ↦ a h2
      }
    have hx2 : x2 ≠ 0 := by -- this is clear [done]
      refine Finsupp.ne_iff.mpr ?_
      rw [Finsupp.ne_iff] at hx
      obtain ⟨a, ha⟩ := hx
      use finCast i a
      rw [show x2 (finCast i a) = x a from dif_pos a.isLt]
      exact ha
    -- the next part is really confusing (sorry :/ )
    -- this is by def of x2.support
    have : (x.sum fun j xj ↦ x.sum fun k xk ↦ star xj * M.leadingMinor i j k * xk) =
      (x2.sum fun j xj ↦ x2.sum fun k xk ↦ star xj * M j k * xk) := by
        unfold leadingMinor
        simp only [Matrix.submatrix_apply]
        let f : Fin (i+1) ↪ Fin n :=
          { toFun := finCast i -- this should probably be outside
            inj' := by exact
            injective_of_le_imp_le (finCast i) fun {x y} a ↦ a
          }
        have h_supp : x2.support = x.support.map f := rfl
        unfold Finsupp.sum --now is just a sum :)
        rw [h_supp, Finset.sum_map]
        unfold x2 x2fun
        simp only [Finsupp.coe_mk, mul_dite, mul_zero, sum_map]
        congr
        ext j
        congr
        ext k
        by_cases H1 : f k < i.val + 1
        · rw [dif_pos H1]
          by_cases H2 : f j < i.val + 1
          · rw [dif_pos H2]
            exact rfl
          · push_neg at H2 -- contradiction
            have h1 : i.val + 1 ≤ (f j).val := H2
            have h2 : (f j).val = j.val := rfl
            have h3 : j.val < i.val + 1 := j.isLt
            linarith
        · push_neg at H1 -- contradiction
          have h1 : i.val + 1 ≤ (f k).val := H1
          have h2 : (f k).val = k.val := rfl
          have h3 : k.val < i.val + 1 := k.isLt
          linarith
    rw[this]
    exact hM.2 hx2

open scoped Classical in -- [done]
theorem Det_pos_leadingMinors_if_isPosDef {M : Matrix (Fin n) (Fin n) R}
(h : M.IsHermitian) (hM : M.PosDef) : ∀ i : Fin n , (M.leadingMinor i).det > 0 := by
  exact fun i => (PosDef_leadingMinor_if_isPosDef h hM i).det_pos -- posdef matrices have pos. det.

theorem isPosDef_iff_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R} -- [done]
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : Fin n , (M.leadingMinor i).det > 0) := by
  exact ⟨ fun h1 i => Det_pos_leadingMinors_if_isPosDef h h1 i,
  fun h2 => isPosDef_if_Det_pos_leadingMinors h2⟩

end Matrix
