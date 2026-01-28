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
    let Mn := M.leadingMinor n (Nat.le_add_right n 1) -- block decomposition
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

    have hatmost2 : ¬∃ (u v : Fin (n+1) →₀ R), -- there cant be two different eigenvectors with
    -- negative eigenvalue (dificult part) [not_done]
      u ≠ 0 ∧ v ≠ 0 ∧ u ⬝ᵥ v = 0 ∧
      (0 > u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) ∧
      (0 > v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj) := by
        by_contra H
        obtain ⟨u, v, hu, hv, huv, hu2, hv2⟩ := H
        let un := u (Fin.last n)
        let vn := v (Fin.last n)

        let w_fun : Fin (n+1) → R := fun k => vn * u k - un * v k -- we construct w
        let w : Fin (n+1) →₀ R := Finsupp.equivFunOnFinite.symm w_fun

        have hwn : w (Fin.last n) = 0 := by -- last element is 0
          simp [w, w_fun, un, vn]
          ring

        let pullfun : Fin (n+1) → Fin n := fun k => -- workaround [not_done]
        if isLt : k.val < n then
          ⟨k.val, isLt⟩
        else
          sorry
        let w2sup : Finset (Fin n) := { -- we define the support
          val := w.support.val.map pullfun
          nodup := by
            refine Multiset.Nodup.map ?_ ?_
            · sorry
            · exact w.support.nodup
          }

        let w2fun : Fin n → R := fun (k : Fin n) => -- the function
           w ⟨k.val, Nat.lt_add_right 1 k.isLt⟩

        let w2 : Fin n →₀ R := {
          support := w2sup
          toFun := w2fun
          mem_support_toFun := sorry
        }

        sorry

    have honlyone: ∀ (j : Fin (n + 1)), j ≠ i → 0 < h.eigenvalues j := by -- almost done [not_done]
      by_contra H
      push_neg at H
      obtain ⟨j, hneq, hj⟩ := H
      have hj : h.eigenvalues j < 0 := Std.lt_of_le_of_ne hj (hneq0 j)

      -- Someone must check these defs [not_done]
      let ufun := h.eigenvectorBasis i
      let vfun := h.eigenvectorBasis j
      let u : Fin (n+1) →₀ R := Finsupp.equivFunOnFinite.symm ufun
      let v : Fin (n+1) →₀ R := Finsupp.equivFunOnFinite.symm vfun

      have hortho : Orthonormal R h.eigenvectorBasis := h.eigenvectorBasis.orthonormal

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

      have huv : u ⬝ᵥ v = 0 := hortho.2 hneq -- [done]

      have hu2 : 0 > u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj := by sorry
      have hv2 : 0 > v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj := by sorry

      have : ∃ (u v : Fin (n+1) →₀ R), u ≠ 0 ∧ v ≠ 0 ∧ u ⬝ᵥ v = 0 ∧
      (0 > u.sum fun i ui ↦ u.sum fun j uj ↦ star ui * M i j * uj) ∧
      (0 > v.sum fun i vi ↦ v.sum fun j vj ↦ star vi * M i j * vj) := by
        use u
        use v
      exact hatmost2 this

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
