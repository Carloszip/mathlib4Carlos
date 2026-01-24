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
def finCast {i : ℕ} (hi : i ≤ n) : Fin i → Fin n :=
fun k => ⟨k.val, Fin.val_lt_of_le k hi ⟩

-- I wasnt able to define this without losing generality, so now n is just a natural number
def leadingMinor (A : Matrix (Fin n) (Fin n) R) (i : ℕ) (hi : i ≤ n) :
  Matrix (Fin i) (Fin i) R := A.submatrix (finCast hi) (finCast hi)

lemma PosDef_leadingMinor_if_isPosDef {M : Matrix (Fin n) (Fin n) R}
(h : M.IsHermitian) (hM : M.PosDef) (i : ℕ) (hi : i ≤ n) : (M.leadingMinor i hi).PosDef := by
  unfold PosDef
  constructor -- it is hermitian and blablabla
  · ext j k -- easy part [done]
    exact IsHermitian.apply h ?_ ?_
    -- leading minor is hermitian
    -- because M.leadingMinor i j = M i j = star (M j i) = star (M.leadingMinor j i)
  · intro x hx -- not so easy part [not_done]
    -- we define x2 as an extension of x
    let x2sup : Finset (Fin n) := { -- we define the support
      val := x.support.val.map (fun j => finCast hi j)
      nodup := by
        have hinj := injective_of_le_imp_le (fun j ↦ finCast hi j) fun {x y} a ↦ a
        exact Multiset.Nodup.map hinj x.support.nodup
      }
    let x2fun : Fin n → R := fun (k : Fin n) => -- the function
        if isLt : k.val < i then
          x ⟨k.val, isLt⟩
        else
          0 -- x2 k = x k if k ≤ i, 0 if not
    let x2: Fin n →₀ R := -- and finally the 'vector'
      { support := x2sup
        toFun := x2fun
        mem_support_toFun := by -- hideous junk
          let h := x.mem_support_toFun
          intro a
          by_cases H: a.val < i
          -- if a is less than i then it comes from the original x,
          -- else it is 0
          · let a': Fin i := {
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
                exact ⟨Finsupp.mem_support_iff.mp h ,
                rfl ⟩
            have h2 : (x2fun a ≠ 0) ↔ (x.toFun a' ≠ 0) := by -- this is clear enough [done]
              unfold x2fun
              rw [dif_pos H]
              exact Iff.symm (Iff.of_eq rfl)
            specialize h a'
            rw [h1,h2]
            exact h
          · push_neg at H -- this probably could be clearer [not_done]
            have h1 : (a ∉ x2sup) := by
              intro ha
              simp only [x2sup, Finset.mem_def, Multiset.mem_map] at ha
              obtain ⟨j, hj, heq⟩ := ha
              have heq': j.val = a.val := by exact Fin.mk.inj_iff.mp heq
              have : a.val < i := by rw[←heq'] ; exact j.is_lt
              linarith
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
      use finCast hi a
      rw [show x2 (finCast hi a) = x a from dif_pos a.isLt]
      exact ha
    -- the next part is really confusing (sorry :/ ) [not_done]
    -- this is by def of x2.support
    have : (x.sum fun j xj ↦ x.sum fun k xk ↦ star xj * M.leadingMinor i hi j k * xk) =
      (x2.sum fun j xj ↦ x2.sum fun k xk ↦ star xj * M j k * xk) := by
        unfold leadingMinor
        simp only [Matrix.submatrix_apply]
        let f : Fin i ↪ Fin n :=  -- this should probably be outside
          { toFun := finCast hi
            inj' := injective_of_le_imp_le (finCast hi) fun {x y} a ↦ a
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
        by_cases H1 : f k < i
        · rw [dif_pos H1]
          by_cases H2 : f j < i
          · rw [dif_pos H2]
            exact rfl
          · push_neg at H2 -- contradiction
            have h1 : i ≤ (f j).val := H2
            have h2 : (f j).val = j.val := rfl
            have h3 : j.val < i := j.isLt
            linarith
        · push_neg at H1 -- contradiction
          have h1 : i ≤ (f k).val := H1
          have h2 : (f k).val = k.val := rfl
          have h3 : k.val < i := k.isLt
          linarith
    rw[this]
    exact hM.2 hx2

open scoped Classical in -- [done]
theorem Det_pos_leadingMinors_if_isPosDef {M : Matrix (Fin n) (Fin n) R}
(h : M.IsHermitian) (hM : M.PosDef) :
∀ i : Fin (n+1) , (M.leadingMinor i (Fin.is_le i)).det > 0 := by
  exact fun i => (PosDef_leadingMinor_if_isPosDef h hM i (Fin.is_le i)).det_pos

theorem isPosDef_if_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R}
(h : ∀ i : Fin (n+1) , (M.leadingMinor i (Fin.is_le i)).det > 0) : M.PosDef := by
  induction n with
  | zero => -- kinda bloated but [done]
      constructor
      · exact isHermitian_iff_isSymmetric.mpr fun x ↦ congrFun rfl
      · intro x hx
        have : x = 0 := by
          ext i
          exact Fin.elim0 i
        exact (hx this).elim
  | succ n ih => -- (._.) [not_done]
      let Mn := M.leadingMinor n (Nat.le_add_right n 1) -- block decomposition
      have hMn_pos : Mn.PosDef := by -- Mn is posdef
        apply ih
        intro i
        have heq : (Mn.leadingMinor i (Fin.is_le i)) = (M.leadingMinor i (Fin.is_le')) := by
          ext i j
          unfold Mn leadingMinor finCast
          simp only [submatrix_apply]
        rw [heq]
        exact h ⟨↑i, Nat.lt_add_right 1 (Fin.is_lt i)⟩
      have hM_Det_pos : M.det > 0 := by -- det M is > 0
        have : M = M.leadingMinor (n+1) (Nat.le_refl (n + 1)) := rfl
        rw [this]
        exact h ⟨n+1, lt_add_one (n + 1)⟩
      have hMn_Det_pos : Mn.det > 0 := by -- det Mn is > 0
        have : Mn = M.leadingMinor (n) (Nat.le_add_right n 1) := rfl
        rw [this]
        exact h ⟨n, by refine Nat.lt_add_right 1 (lt_add_one n)⟩
      /- sketch
       / Mn v \ this is our matrix
       \ vt d /

       by the determinant formula we obtain what we should.
      -/
      sorry

theorem isPosDef_iff_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R} -- [done]
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : Fin (n+1) , (M.leadingMinor i (Fin.is_le i)).det > 0) := by
  exact ⟨fun h1 i => Det_pos_leadingMinors_if_isPosDef h h1 i,
  fun h2 => isPosDef_if_Det_pos_leadingMinors h2⟩

end Matrix
