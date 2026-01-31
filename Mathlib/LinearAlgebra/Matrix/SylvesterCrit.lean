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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finsupp.Defs

@[expose] public section

universe v

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : ℕ}
--variable {R : Type v} [RCLike R]
abbrev R := ℝ --we need RClike for posdef implies pos determinant, and partialorder for det>0
variable {A : Matrix (Fin n) (Fin n) R}

-- here rests Fin.cast RIP u_u

-- I wasnt able to define this without losing generality, so now n is just a natural number
def leadingMinor (A : Matrix (Fin n) (Fin n) R) (i : ℕ) (hi : i ≤ n) :
  Matrix (Fin i) (Fin i) R := A.submatrix (Fin.castLE hi) (Fin.castLE hi)


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
      val := x.support.val.map (fun j => Fin.castLE hi j)
      nodup := by
        have hinj := injective_of_le_imp_le (fun j ↦ Fin.castLE hi j) fun {x y} a ↦ a
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
      use Fin.castLE hi a
      rw [show x2 (Fin.castLE hi a) = x a from dif_pos a.isLt]
      exact ha
    -- the next part is really confusing (sorry :/ ) [not_done]
    -- this is by def of x2.support
    have : (x.sum fun j xj ↦ x.sum fun k xk ↦ star xj * M.leadingMinor i hi j k * xk) =
      (x2.sum fun j xj ↦ x2.sum fun k xk ↦ star xj * M j k * xk) := by
        unfold leadingMinor
        simp only [Matrix.submatrix_apply]
        let f : Fin i ↪ Fin n :=  -- this should probably be outside
          { toFun := Fin.castLE hi
            inj' := injective_of_le_imp_le (Fin.castLE hi) fun {x y} a ↦ a
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


theorem isPosDef_if_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R} (h : M.IsHermitian)
(hM : ∀ i : Fin (n+1) , (M.leadingMinor i (Fin.is_le i)).det > 0) : M.PosDef := by
  induction n with
  | zero => -- kinda bloated but [done]
    constructor
    · exact h
    · intro x hx
      have : x = 0 := by
        ext i
        exact Fin.elim0 i
      exact (hx this).elim
  | succ n ih => -- (._.) [not_done]
    let Mn := M.leadingMinor n (Nat.le_add_right n 1)
    have hMn_pos : Mn.PosDef := by -- Mn is posdef
      have : Mn.IsHermitian := by
        exact congrFun (congrFun (congrArg submatrix h) (Fin.castLE (Nat.le_add_right n 1)))
            (Fin.castLE (Nat.le_add_right n 1))
      apply ih this
      intro i
      have heq : (Mn.leadingMinor i (Fin.is_le i)) = (M.leadingMinor i (Fin.is_le')) := by
        ext i j
        unfold Mn leadingMinor Fin.castLE
        simp only [submatrix_apply]
      rw [heq]
      exact hM ⟨↑i, Nat.lt_add_right 1 (Fin.is_lt i)⟩
    have hM_Det_pos : M.det > 0 := by -- det M is > 0
      have : M = M.leadingMinor (n+1) (Nat.le_refl (n + 1)) := rfl
      rw [this]
      exact hM ⟨n+1, lt_add_one (n + 1)⟩

    /- To do:
    approach with Schur complement (I believe this is hard)

    approach with Eigenvalues, probably easier
    • M is Posdef iff all eigenvalues are positive
    • Mn is Posdef → all eigenvalues are pos
    • First: there is at most one negative eigenvalue
      ∘ if there are two v, u, construct v_n u - u_n v
      ∘ wt M w = wcut,t Mn wcut must be > 0
      ∘ but wt M w = v_n² (ut M u) - u_n² (vt M v) < 0
      ∘ contradiction
    • Second: suppose there is one negative eigenvalue
      ∘ det M = pos pos pos * neg = neg
      ∘ but det M > 0
      ∘ contradiction
    • all eigenvalues are positive → M is Posdef-/

    rw [IsHermitian.posDef_iff_eigenvalues_pos h] -- we must prove all eigenvalues are positive
    have hdet : M.det = ∏ j, h.eigenvalues j := by -- det is the product of eigenvalues [done]
        rw [h.det_eq_prod_eigenvalues]
        simp only [RCLike.ofReal_real_eq_id, id_eq]
    have hneq0: ∀ (i: Fin (n + 1)), h.eigenvalues i ≠ 0 := by -- no eigenvalue is 0 [done]
      intro i
      by_contra H
      have : M.det = 0 := by
        rw [hdet]
        apply Finset.prod_eq_zero_iff.mpr
        refine ⟨i, mem_univ i, H⟩
      linarith

    by_contra H -- by contradiction.
    push_neg at H
    obtain ⟨i, hi⟩ := H
    have hi : h.eigenvalues i < 0 := Std.lt_of_le_of_ne hi (hneq0 i)

    have hnot2 : ¬∃ j, j ≠ i ∧ h.eigenvalues j < 0 := by
      by_contra H
      obtain ⟨j, hne, hj⟩ := H

      let ufun := h.eigenvectorBasis i -- defining u and v
      let vfun := h.eigenvectorBasis j
      let u : Fin (n+1) →₀ R := Finsupp.equivFunOnFinite.symm ufun
      let v : Fin (n+1) →₀ R := Finsupp.equivFunOnFinite.symm vfun
      let un := u (Fin.last n)
      let vn := v (Fin.last n)

      have hortho : Orthonormal R h.eigenvectorBasis := h.eigenvectorBasis.orthonormal

      have hu2 : 0 > u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj := by
        have hquad : u.sum (fun i ui => u.sum (fun j uj => star ui * M i j * uj))
          = h.eigenvalues i * ‖(ufun)‖^2 := by

          -- Gemini did this [not_done]
          have h1 : (u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) =
            u.sum (fun i ui => star ui * (M.mulVec ufun i)) := by
            unfold Matrix.mulVec Finsupp.sum
            simp only [star_trivial]
            congr
            ext a
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
            congr 1
            unfold dotProduct
            apply Finset.sum_subset (Finset.subset_univ _)
            intro x hx1 hx2
            rw [Finsupp.notMem_support_iff] at hx2
            exact mul_eq_zero_of_right (M a x) hx2


          have h2 : M.mulVec ufun = fun k => h.eigenvalues i * ufun k :=
            h.mulVec_eigenvectorBasis i

          have h3 : (u.sum fun i_1 ui ↦ star ui * (fun k ↦ h.eigenvalues i * ufun.ofLp k) i_1) =
            h.eigenvalues i * u.sum (fun i ui => star ui * ui) := by
            unfold Finsupp.sum
            simp [Finset.mul_sum, mul_comm, mul_assoc]
            congr

          have hnorm : u.sum (fun i ui => star ui * ui) = ‖ufun‖^2 := by
            unfold u Finsupp.sum
            rw [Finset.sum_subset (Finset.subset_univ _)]
            · rw [PiLp.norm_sq_eq_of_L2]
              congr
              ext x
              simp
              ring
            · intro x hx1 hx2
              simp only [Finsupp.equivFunOnFinite_symm_apply_support, Set.Finite.toFinset_setOf,
                ne_eq, mem_filter, mem_univ, true_and, Decidable.not_not] at hx2
              simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, star_trivial, mul_eq_zero,
                or_self]
              exact hx2
          rw [h1, h2, h3, hnorm]

        rw[hquad]
        have : ‖ufun‖ ^ 2 > 0 := by
          have : ‖ufun‖ ≠ 0 := by
            rw [hortho.1 i]
            exact Ne.symm zero_ne_one
          exact sq_pos_iff.mpr this
        exact mul_neg_of_neg_of_pos hi this


      have hv2 : 0 > v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj := by
      -- copy the one above [done]
        have hquad : v.sum (fun i vi => v.sum (fun j vj => star vi * M i j * vj))
          = h.eigenvalues j * ‖(vfun)‖^2 := by

          -- Gemini did this [not_done]
          have h1 : (v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj) =
            v.sum (fun i vi => star vi * (M.mulVec vfun i)) := by
            unfold Matrix.mulVec Finsupp.sum
            simp only [star_trivial]
            congr
            ext a
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
            congr 1
            unfold dotProduct
            apply Finset.sum_subset (Finset.subset_univ _)
            intro x hx1 hx2
            rw [Finsupp.notMem_support_iff] at hx2
            exact mul_eq_zero_of_right (M a x) hx2


          have h2 : M.mulVec vfun = fun k => h.eigenvalues j * vfun k :=
            h.mulVec_eigenvectorBasis j

          have h3 : (v.sum fun i_1 vi ↦ star vi * (fun k ↦ h.eigenvalues j * vfun.ofLp k) i_1) =
          h.eigenvalues j * v.sum (fun i vi => star vi * vi) := by
            unfold Finsupp.sum
            simp [Finset.mul_sum, mul_comm, mul_assoc]
            congr

          have hnorm : v.sum (fun i vi => star vi * vi) = ‖vfun‖^2 := by
            unfold v Finsupp.sum
            rw [Finset.sum_subset (Finset.subset_univ _)]
            · rw [PiLp.norm_sq_eq_of_L2]
              congr
              ext x
              simp
              ring
            · intro x hx1 hx2
              simp only [Finsupp.equivFunOnFinite_symm_apply_support, Set.Finite.toFinset_setOf,
                ne_eq, mem_filter, mem_univ, true_and, Decidable.not_not] at hx2
              simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, star_trivial, mul_eq_zero,
                or_self]
              exact hx2
          rw [h1, h2, h3, hnorm]

        rw[hquad]
        have : ‖vfun‖ ^ 2 > 0 := by
          have : ‖vfun‖ ≠ 0 := by
            rw [hortho.1 j]
            exact Ne.symm zero_ne_one
          exact sq_pos_iff.mpr this
        exact mul_neg_of_neg_of_pos hj this

      have hu : u ≠ 0 := by -- bloated [not_done]
        by_contra H
        apply_fun Finsupp.equivFunOnFinite at H
        simp only [apply_symm_apply, u] at H
        rw [show Finsupp.equivFunOnFinite 0 = 0 from rfl] at H
        have h0 : ufun = 0 := PiLp.ext (congrFun H)
        have : dotProduct (star ufun) ufun = 1 := by -- ufun · ufun = norm² = 1² = 1
          have hnorm := hortho.1 i
          have : (1 : R) = 1 * 1 := by ring
          rw [this, ←hnorm, ←real_inner_self_eq_norm_mul_norm ufun]
          exact rfl
        rw [h0] at this
        simp only [WithLp.ofLp_zero, star_trivial, dotProduct_zero, zero_ne_one] at this

      have hv : v ≠ 0 := by -- copy the one above [done]
        by_contra H
        apply_fun Finsupp.equivFunOnFinite at H
        simp only [apply_symm_apply, v] at H
        rw [show Finsupp.equivFunOnFinite 0 = 0 from rfl] at H
        have h0 : vfun = 0 := PiLp.ext (congrFun H)
        have : dotProduct (star vfun) vfun = 1 := by
          have hnorm := hortho.1 j
          have : (1 : R) = 1 * 1 := by ring
          rw [this, ←hnorm, ←real_inner_self_eq_norm_mul_norm vfun]
          exact rfl
        rw [h0] at this
        simp only [WithLp.ofLp_zero, star_trivial, dotProduct_zero, zero_ne_one] at this

      let wfun : Fin (n+1) → R := fun k ↦ vn * u k - un * v k
      let w := Finsupp.equivFunOnFinite.symm wfun -- we define w like this

      have hwn : w (Fin.last n) = 0 := by -- last element is 0
        simp [w, wfun, un, vn]
        ring

      have hw0 : w ≠ 0 := by -- this is harder than expected [not_done]
        by_contra H -- by contradiction
        unfold w wfun at H
        have huv: vn • u - un • v = 0 := by
          rw [← H]
          ext k
          simp
        by_cases hun: un ≠ 0
        · have hv' : v = (vn/un) • u := by -- if un ≠ 0 we can divide
            have : un • v = vn • u := (sub_eq_zero.mp huv).symm
            calc v = (un⁻¹) • (un • v) := Eq.symm (inv_smul_smul₀ hun v)
              _ = (un⁻¹) • (vn • u) := congrArg (HSMul.hSMul un⁻¹) this
              _ = (un⁻¹ * vn) • u := smul_smul un⁻¹ vn u
              _ = (vn/un) • u := by congr 1; exact inv_mul_eq_div un vn
          have hv : vfun = (vn/un) • ufun := by
            -- we obtain that the two vectors are parallel
            -- and that cant be since they are orthogonal
            unfold u v at hv'
            simp only at hv'
            apply_fun Finsupp.equivFunOnFinite at hv'
            unfold ufun vfun at hv' ⊢
            simp only [apply_symm_apply] at hv'
            ext k
            rw[hv']
            simp
          have hdot := hortho.2 hne.symm
          simp only at hdot
          unfold vfun ufun at hv
          rw [hv, inner_smul_right] at hdot
          rw [inner_self_eq_norm_sq_to_K, hortho.1 i] at hdot
          rw [← RCLike.ofReal_pow 1 2, one_pow 2] at hdot
          simp only [RCLike.ofReal_real_eq_id, id_eq, mul_one,
            div_eq_zero_iff, hun, or_false] at hdot
          rw [hdot, zero_div un, zero_smul] at hv
          have h_norm := hortho.1 j
          rw [hv] at h_norm
          simp at h_norm

        · unfold un at hun
          push_neg at hun

          -- the following argument says that if the last component of a (eigen)vector u is 0
          -- then ut M u > 0
          -- it is later used again and I believe it should be a lemma somewhere
          have h_pos : 0 < (u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) := by
            let f := (Fin.castLE (Nat.le_succ n))

            -- trivial [done]
            have hinj : Set.InjOn f (f⁻¹' ↑u.support) := by
              intro x hx y hy heq
              apply Fin.castLE_injective
              exact heq

            let u2 : Fin n →₀ ℝ := u.comapDomain f hinj

            -- this looks so bad [not_done]
            -- ut M u = u2t Mn u2
            have heq : (u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) =
              (u2.sum fun i u2i ↦ u2.sum fun j u2j ↦ star u2i * Mn i j * u2j) := by
              rw [Finsupp.sum_fintype]
              · rw [Finsupp.sum_fintype]
                · rw [Fin.sum_univ_castSucc, Finsupp.sum_fintype]
                  · simp only [hun, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
                    congr
                    ext a
                    simp only [star_trivial, mul_zero, implies_true, Finsupp.sum_fintype]
                    rw [Fin.sum_univ_castSucc]
                    simp only [hun, mul_zero, add_zero]
                    congr
                  · intro b
                    exact mul_zero (star (u (Fin.last n)) * M (Fin.last n) b)
                · intro c
                  simp only [star_zero, zero_mul]
                  exact Finsupp.sum_zero
              · intro d
                simp only [star_zero, zero_mul]
                exact Finsupp.sum_zero

            have hu20 : u2 ≠ 0 := by -- this is ok [done]
              by_contra H
              apply hu
              ext k
              by_cases hk : k = Fin.last n
              · rw [hk]
                simp only [Finsupp.coe_zero, Pi.zero_apply]
                rw [hun]
              · let j : Fin n := ⟨k.val, Fin.val_lt_last hk⟩
                have : u2 j = 0 := by simp_rw[H] ; rfl
                rw [Finsupp.comapDomain_apply] at this
                exact this

            rw [heq]
            exact hMn_pos.2 hu20

          linarith


      have hwn : w (Fin.last n) = 0 := by -- last element is 0 [done]
        simp [w, wfun, un, vn]
        ring

      have h_pos : 0 < (w.sum fun i wi ↦ w.sum fun j wj ↦ star wi * M i j * wj) := by
        let f := (Fin.castLE (Nat.le_succ n))

        -- trivial [done]
        have hinj : Set.InjOn f (f⁻¹' ↑w.support) := by
          intro x hx y hy heq
          apply Fin.castLE_injective
          exact heq

        let w2 : Fin n →₀ ℝ := w.comapDomain f hinj

        -- this looks so bad [not_done]
        have heq : (w.sum fun i wi ↦ w.sum fun j wj ↦ star wi * M i j * wj) =
          (w2.sum fun i w2i ↦ w2.sum fun j w2j ↦ star w2i * Mn i j * w2j) := by
          rw [Finsupp.sum_fintype]
          · rw [Finsupp.sum_fintype]
            · rw [Fin.sum_univ_castSucc, Finsupp.sum_fintype]
              · simp only [hwn, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
                congr
                ext a
                simp only [star_trivial, mul_zero, implies_true, Finsupp.sum_fintype]
                rw [Fin.sum_univ_castSucc]
                simp only [hwn, mul_zero, add_zero]
                congr
              · intro b
                exact mul_zero (star (w (Fin.last n)) * M (Fin.last n) b)
            · intro c
              simp only [star_zero, zero_mul]
              exact Finsupp.sum_zero
          · intro d
            simp only [star_zero, zero_mul]
            exact Finsupp.sum_zero

        have hw20 : w2 ≠ 0 := by -- this is ok [done]
          by_contra H
          apply hw0
          ext k
          by_cases hk : k = Fin.last n
          · rw [hk]
            simp only [Finsupp.coe_zero, Pi.zero_apply]
            rw [hwn]
          · let j : Fin n := ⟨k.val, Fin.val_lt_last hk⟩
            have : w2 j = 0 := by simp_rw[H] ; rfl
            rw [Finsupp.comapDomain_apply] at this
            exact this

        rw [heq]
        exact hMn_pos.2 hw20

      have h_neg : (w.sum fun i wi ↦ w.sum fun j wj ↦ star wi * M i j * wj) ≤ 0 := by
        -- just sums [not_done]
        have heq : (w.sum fun i wi ↦ w.sum fun j wj ↦ star wi * M i j * wj) =
          vn^2 * (u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) +
          un^2 * (v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj) := by

          have h1 : -- this should be a lemma and it will make things easier everywhere [IMPORTANT]
            (w.sum fun i wi ↦ w.sum fun j wj ↦ star wi * M i j * wj) =
            ∑ i : Fin (n+1), ∑ j : Fin (n+1), star (w i) * M i j * (w j) := by
            rw [Finsupp.sum_fintype]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [Finsupp.sum_fintype]
              · intro a ; simp
            · intro b ; simp

          have h2 :
            (∑ i, ∑ j, star (w i) * M i j * (w j)) =
            (vn^2 * ∑ i, ∑ j, star (u i) * M i j * (u j)) -
            (vn * un * ∑ i, ∑ j, star (u i) * M i j * (v j)) -
            (un * vn * ∑ i, ∑ j, star (v i) * M i j * (u j)) +
            (un^2 * ∑ i, ∑ j, star (v i) * M i j * (v j)) := by
            simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, star_trivial, w, wfun]
            simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, pow_two]
            have hmul1 : ∀ x x_1 : Fin (n+1), vn * u x * M x x_1 * (vn * u x_1) =
              vn * vn * (u x * M x x_1 * u x_1) := by
              intro x x_1
              ring_nf
            have hmul2 : ∀ x x_1 : Fin (n+1), un * v x * M x x_1 * (un * v x_1) =
              un * un * (v x * M x x_1 * v x_1) := by
              intro x x_1
              ring_nf
            have hmul3 : ∀ x x_1 : Fin (n+1), un * v x * M x x_1 * (vn * u x_1) =
              un * vn * (v x * M x x_1 * u x_1) := by
              intro x x_1
              ring_nf
            have hmul4 : ∀ x x_1 : Fin (n+1), vn * u x * M x x_1 * (un * v x_1) =
              vn * un * (u x * M x x_1 * v x_1) := by
              intro x x_1
              ring_nf
            simp [hmul1, hmul2, hmul3, hmul4]
            ring

          have h3 :
            (vn * un * ∑ i, ∑ j, star (u i) * M i j * (v j)) = 0 ∧
            (un * vn * ∑ i, ∑ j, star (v i) * M i j * (u j)) = 0 := by
            constructor
            · apply mul_eq_zero_of_right

              have horth' : ∑ i, vfun.ofLp i * u i = 0 := by
                simp only [u, Finsupp.coe_equivFunOnFinite_symm]
                have hort := hortho.2 hne.symm
                simp only at hort
                rw [PiLp.inner_apply] at hort
                rw[← hort]
                unfold ufun vfun
                congr

              have ht : (∑ i, ∑ j, star (u i) * M i j * v j) =
                ∑ i, star (u i) * (M.mulVec vfun i) := by
                unfold Matrix.mulVec dotProduct
                simp_rw [Finset.mul_sum]
                simp_rw [mul_assoc]
                congr

              have hMv : M.mulVec vfun = fun k => h.eigenvalues j * vfun k := by
                simpa using h.mulVec_eigenvectorBasis j
              rw [ht]
              simp only [star_trivial, hMv]
              simp only [mul_comm, mul_assoc, ← mul_sum, mul_eq_zero]
              right
              exact horth'

            · apply mul_eq_zero_of_right

              have horth' : ∑ i, ufun.ofLp i * v i = 0 := by
                simp only [v, Finsupp.coe_equivFunOnFinite_symm]
                have hort := hortho.2 hne
                simp only at hort
                rw [PiLp.inner_apply] at hort
                rw[← hort]
                unfold ufun vfun
                congr

              have ht : (∑ i, ∑ j, star (v i) * M i j * u j) =
                ∑ i, star (v i) * (M.mulVec ufun i) := by
                unfold Matrix.mulVec dotProduct
                simp_rw [Finset.mul_sum]
                simp_rw [mul_assoc]
                congr

              have hMv : M.mulVec ufun = fun k => h.eigenvalues i * ufun k := by
                simpa using h.mulVec_eigenvectorBasis i
              rw [ht]
              simp only [star_trivial, hMv]
              simp only [mul_comm, mul_assoc, ← mul_sum, mul_eq_zero]
              right
              exact horth'

          rw [h1, h2]
          rw [h3.1, h3.2]
          simp only [sub_zero]
          have h4 : (u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) =
            ∑ i : Fin (n+1), ∑ j : Fin (n+1), star (u i) * M i j * (u j) := by
            rw [Finsupp.sum_fintype]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [Finsupp.sum_fintype]
              · intro a ; simp
            · intro b ; simp
          have h5 : (v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj) =
            ∑ i : Fin (n+1), ∑ j : Fin (n+1), star (v i) * M i j * (v j) := by
            rw [Finsupp.sum_fintype]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [Finsupp.sum_fintype]
              · intro a ; simp
            · intro b ; simp
          rw [h4, h5]


        rw [heq]
        nlinarith

      linarith

    have honlyone: ∀ (j : Fin (n + 1)), j ≠ i → 0 < h.eigenvalues j := by -- [done]
      by_contra H
      push_neg at H
      obtain ⟨j, hneq, hj⟩ := H
      have hj : h.eigenvalues j < 0 := Std.lt_of_le_of_ne hj (hneq0 j)
      have hthereis2 : ∃ j, j ≠ i ∧ h.eigenvalues j < 0 := by use j
      exact hnot2 hthereis2

    have : M.det < 0 := by -- if there is only one... [done]
      rw [hdet]
      have : h.eigenvalues i * ∏ j ∈ Finset.univ.erase i, h.eigenvalues j = ∏ j, h.eigenvalues j :=
        Finset.mul_prod_erase Finset.univ h.eigenvalues (Finset.mem_univ i)
      rw [←this]
      have : ∏ j ∈ univ.erase i, h.eigenvalues j > 0 := by
        apply Finset.prod_pos
        intro j hj
        exact honlyone j (ne_of_mem_erase hj)
      exact mul_neg_of_neg_of_pos hi this
    linarith


theorem isPosDef_iff_Det_pos_leadingMinors {M : Matrix (Fin n) (Fin n) R} -- [done]
{h : M.IsHermitian} : M.PosDef ↔ (∀ i : Fin (n+1) , (M.leadingMinor i (Fin.is_le i)).det > 0) := by
  exact ⟨fun h1 i => Det_pos_leadingMinors_if_isPosDef h h1 i,
  fun h2 => isPosDef_if_Det_pos_leadingMinors h h2⟩

end Matrix
