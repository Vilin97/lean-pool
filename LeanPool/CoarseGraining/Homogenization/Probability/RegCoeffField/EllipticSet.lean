/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Sigma
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# The elliptic-matrix locus is closed, convex and measurable

This file ports the finite-dimensional closed/convex description of the elliptic
matrix locus `{A : Mat d | IsEllipticMatrix lam Lam A}` from the coarse-graining
salvage (`Homogenization.Book.Ch04.Internal.SliceNullMeasurability`), adapted to
the shipped tree's imports.  It is the ingredient that makes the carrier
truncation `ellipticTruncateReg` a genuine carrier element: the pointwise
predicate `IsEllipticMatrix 1 Θ (a x)` cuts out a Borel set of matrices, so the
pullback `{x | IsEllipticMatrix 1 Θ (a x)}` is measurable.

The fourth ellipticity inequality `Lam⁻¹ |ξ|² ≤ ξ · A⁻¹ ξ` is replaced by an
inverse-free image bound `|A η|² ≤ Lam (η · A η)` (`IsEllipticEntryLU`), whose
sublevel description is a countable-free intersection of closed half-spaces,
hence closed and convex.

The `Mat d = Fin d → Fin d → ℝ` matrix-entry space carries the product Borel
structure; we record the corresponding `BorelSpace` instance transferred from the
genuine pi type so that closed matrix sets are measurable for the carrier's
`instMatMeasurableSpace`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Local copy of the identity action -/

/-- The identity matrix acts as the identity on vectors (local copy, kept private
to avoid depending on the raw random-field layer). -/
private theorem matVecMul_one_local (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The flux inequality `‖B η‖² ≤ Lam · η · (symmPart B) η` for an elliptic
matrix `B` (local copy of the coarse-graining fact). -/
private theorem vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix
    {lam Lam : ℝ} {B : Mat d} (hB : IsEllipticMatrix lam Lam B) (η : Vec d) :
    vecNormSq (matVecMul B η) ≤ Lam * vecDot η (matVecMul (symmPart B) η) := by
  have hdet : IsUnit B.det := isUnit_det_of_isEllipticMatrix hB
  set ξ := matVecMul B η with hξ
  have hBinv : matVecMul B⁻¹ ξ = η := by
    rw [hξ, matVecMul_mul, Matrix.nonsing_inv_mul B hdet, matVecMul_one_local]
  have hident :
      vecDot ξ (matVecMul B⁻¹ ξ) = vecDot η (matVecMul (symmPart B) η) := by
    rw [hBinv, vecDot_comm, vecDot_matVecMul_symmPart, hξ]
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hB.1 hB.2.1
  have hsecond : Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul B⁻¹ ξ) := hB.2.2.2 ξ
  rw [hident] at hsecond
  have hscaled := mul_le_mul_of_nonneg_left hsecond hLam_pos.le
  have hcancel : Lam * (Lam⁻¹ * vecNormSq ξ) = vecNormSq ξ := by
    field_simp [hLam_pos.ne']
  rw [hcancel] at hscaled
  exact hscaled

/-! ## The inverse-free ellipticity predicate -/

/-- The two inverse-free ellipticity inequalities for general constants
`(lam, Lam)`, as a predicate on the matrix-entry space `Mat d`.  Coercivity is a
linear inequality in the matrix; the image bound is a convex-quadratic `≤ affine`
inequality.  Both loci are closed and convex. -/
def IsEllipticEntryLU (lam Lam : ℝ) (v : Mat d) : Prop :=
  (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul v ξ)) ∧
    (∀ η : Vec d, vecNormSq (matVecMul v η) ≤ Lam * vecDot η (matVecMul v η))

/-- **Inverse-free characterization for general `(lam, Lam)`.**  Given coercivity,
the fourth ellipticity inequality is equivalent to the inverse-free image bound. -/
theorem isEllipticMatrix_iff_isEllipticEntryLU {lam Lam : ℝ} (A : Mat d) :
    IsEllipticMatrix lam Lam A ↔
      0 < lam ∧ lam ≤ Lam ∧ IsEllipticEntryLU lam Lam A := by
  constructor
  · intro hA
    refine ⟨hA.1, hA.2.1, fun ξ => hA.2.2.1 ξ, fun η => ?_⟩
    have h := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hA η
    rwa [vecDot_matVecMul_symmPart] at h
  · rintro ⟨hlam, hle, hc, himg⟩
    have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam hle
    have hlin : ∀ x y : Vec d, matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
      intro x y; funext i
      simp [matVecMul, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]
    have hinj : Function.Injective (matVecMul A) := by
      intro x y hxy
      have hz : matVecMul A (x - y) = 0 := by rw [hlin, hxy]; simp
      have hcz := hc (x - y)
      rw [hz, vecDot_zero_right] at hcz
      have hnn : lam * vecNormSq (x - y) ≤ 0 := hcz
      have hznn : vecNormSq (x - y) ≤ 0 := by
        by_contra hcon
        push Not at hcon
        exact absurd hnn (not_le.mpr (mul_pos hlam hcon))
      have hzero : vecNormSq (x - y) = 0 := le_antisymm hznn (vecNormSq_nonneg _)
      exact sub_eq_zero.mp (vecNormSq_eq_zero hzero)
    have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    refine ⟨hlam, hle, fun ξ => hc ξ, fun ξ => ?_⟩
    set η := matVecMul A⁻¹ ξ with hη
    have hAη : matVecMul A η = ξ := by
      rw [hη, matVecMul_mul, Matrix.mul_nonsing_inv A hdet, matVecMul_one_local]
    have himgη := himg η
    rw [hAη] at himgη
    have hdot : vecDot η ξ = vecDot ξ (matVecMul A⁻¹ ξ) := by rw [hη, vecDot_comm]
    rw [hdot] at himgη
    have hthis := mul_le_mul_of_nonneg_left himgη (le_of_lt (inv_pos.mpr hLam_pos))
    rw [← mul_assoc, inv_mul_cancel₀ hLam_pos.ne', one_mul] at hthis
    exact hthis

/-! ## Closedness -/

/-- The inverse-free `(lam, Lam)`-ellipticity locus is closed in `Mat d`. -/
theorem isClosed_isEllipticEntryLU {lam Lam : ℝ} :
    IsClosed {v : Mat d | IsEllipticEntryLU lam Lam v} := by
  have h1 : IsClosed
      {v : Mat d | ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul v ξ)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter (fun ξ => ?_)
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed
      {v : Mat d |
        ∀ η : Vec d, vecNormSq (matVecMul v η) ≤ Lam * vecDot η (matVecMul v η)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter (fun η => ?_)
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter h2

/-! ## Convexity -/

/-- Convexity of the squared vector energy along convex combinations. -/
theorem vecNormSq_convex_le {V W : Vec d} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    vecNormSq (a • V + b • W) ≤ a * vecNormSq V + b * vecNormSq W := by
  set P := vecDot V V with hP
  set Q := vecDot W W with hQ
  set R := vecDot V W with hR
  have hWV : vecDot W V = R := by rw [hR, vecDot_comm]
  have hLHS : vecNormSq (a • V + b • W) = a * a * P + a * b * R + b * a * R + b * b * Q := by
    simp only [vecNormSq, vecDot_add_left, vecDot_add_right, vecDot_smul_left,
      vecDot_smul_right, hWV, ← hP, ← hQ, ← hR]
    ring
  have hPQR : (0 : ℝ) ≤ P + Q - 2 * R := by
    have hnn := vecNormSq_nonneg (V - W)
    have hexp : vecNormSq (V - W) = P + Q - 2 * R := by
      simp only [vecNormSq, sub_eq_add_neg, vecDot_add_left, vecDot_add_right,
        vecDot_neg_left, vecDot_neg_right, hWV, ← hP, ← hQ, ← hR]
      ring
    linarith [hexp ▸ hnn]
  have hid :
      a * P + b * Q - (a * a * P + a * b * R + b * a * R + b * b * Q) =
        a * b * (P + Q - 2 * R) := by
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have hnnprod : 0 ≤ a * b * (P + Q - 2 * R) :=
    mul_nonneg (mul_nonneg ha hb) hPQR
  have hnV : vecNormSq V = P := hP.symm
  have hnW : vecNormSq W = Q := hQ.symm
  rw [hLHS, hnV, hnW]; linarith [hid ▸ hnnprod]

/-- The inverse-free `(lam, Lam)`-ellipticity locus is convex in `Mat d`. -/
theorem convex_isEllipticEntryLU {lam Lam : ℝ} :
    Convex ℝ {v : Mat d | IsEllipticEntryLU lam Lam v} := by
  intro v hv w hw a b ha hb hab
  refine ⟨fun ξ => ?_, fun η => ?_⟩
  · have hpv := hv.1 ξ
    have hpw := hw.1 ξ
    have hstep : matVecMul (a • v + b • w) ξ = a • matVecMul v ξ + b • matVecMul w ξ := by
      rw [add_matVecMul, smul_matVecMul, smul_matVecMul]
    rw [hstep, vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
    have hsplit : lam * vecNormSq ξ = a * (lam * vecNormSq ξ) + b * (lam * vecNormSq ξ) := by
      rw [← add_mul, hab, one_mul]
    rw [hsplit]
    have h1 : a * (lam * vecNormSq ξ) ≤ a * vecDot ξ (matVecMul v ξ) :=
      mul_le_mul_of_nonneg_left hpv ha
    have h2 : b * (lam * vecNormSq ξ) ≤ b * vecDot ξ (matVecMul w ξ) :=
      mul_le_mul_of_nonneg_left hpw hb
    linarith
  · set V := matVecMul v η with hV
    set W := matVecMul w η with hW
    have hstep : matVecMul (a • v + b • w) η = a • V + b • W := by
      rw [hV, hW, add_matVecMul, smul_matVecMul, smul_matVecMul]
    have hconv : vecNormSq (a • V + b • W) ≤ a * vecNormSq V + b * vecNormSq W :=
      vecNormSq_convex_le ha hb hab
    have hqv : a * vecNormSq V ≤ a * (Lam * vecDot η V) :=
      mul_le_mul_of_nonneg_left (hv.2 η) ha
    have hqw : b * vecNormSq W ≤ b * (Lam * vecDot η W) :=
      mul_le_mul_of_nonneg_left (hw.2 η) hb
    have hrhs :
        a * (Lam * vecDot η V) + b * (Lam * vecDot η W) =
          Lam * vecDot η (a • V + b • W) := by
      rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]; ring
    calc
      vecNormSq (matVecMul (a • v + b • w) η)
          = vecNormSq (a • V + b • W) := by rw [hstep]
      _ ≤ a * vecNormSq V + b * vecNormSq W := hconv
      _ ≤ a * (Lam * vecDot η V) + b * (Lam * vecDot η W) := by linarith
      _ = Lam * vecDot η (a • V + b • W) := hrhs
      _ = Lam * vecDot η (matVecMul (a • v + b • w) η) := by rw [hstep]

/-! ## The elliptic matrix locus is closed and convex -/

/-- The set characterization: for admissible constants, the `IsEllipticMatrix`
locus is exactly the inverse-free `IsEllipticEntryLU` locus. -/
private theorem isEllipticMatrix_setOf_eq {lam Lam : ℝ} (h : 0 < lam ∧ lam ≤ Lam) :
    {A : Mat d | IsEllipticMatrix lam Lam A} = {v : Mat d | IsEllipticEntryLU lam Lam v} := by
  ext A
  simp only [Set.mem_ofPred_eq]
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  exact ⟨fun hA => hA.2.2, fun hA => ⟨h.1, h.2, hA⟩⟩

private theorem isEllipticMatrix_setOf_eq_empty {lam Lam : ℝ} (h : ¬ (0 < lam ∧ lam ≤ Lam)) :
    {A : Mat d | IsEllipticMatrix lam Lam A} = ∅ := by
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hA
  exact h ⟨hA.1, hA.2.1⟩

/-- The `(lam, Lam)`-elliptic matrix locus is closed in `Mat d`. -/
theorem isClosed_isEllipticMatrix {lam Lam : ℝ} :
    IsClosed {A : Mat d | IsEllipticMatrix lam Lam A} := by
  by_cases h : 0 < lam ∧ lam ≤ Lam
  · rw [isEllipticMatrix_setOf_eq h]; exact isClosed_isEllipticEntryLU
  · rw [isEllipticMatrix_setOf_eq_empty h]; exact isClosed_empty

/-- The `(lam, Lam)`-elliptic matrix locus is convex in `Mat d`. -/
theorem convex_isEllipticMatrix {lam Lam : ℝ} :
    Convex ℝ {A : Mat d | IsEllipticMatrix lam Lam A} := by
  by_cases h : 0 < lam ∧ lam ≤ Lam
  · rw [isEllipticMatrix_setOf_eq h]; exact convex_isEllipticEntryLU
  · rw [isEllipticMatrix_setOf_eq_empty h]; exact convex_empty

/-! ## Measurability of the matrix locus -/

/-- The matrix-entry space `Mat d = Fin d → Fin d → ℝ` carries the product Borel
structure: its carrier σ-algebra `instMatMeasurableSpace` agrees with the Borel
σ-algebra of the product topology.  Transferred from the genuine pi type.

Named distinctly from the raw-`CoeffField` layer's `instBorelSpaceMat`
(`Ch04.Internal.CoarseObservableMeasurability.Basic`) so that the carrier and raw
layers coexist in a single import closure; both witness the same (defeq) product
Borel structure and are found by instance resolution, never by name. -/
instance instBorelSpaceMatEntry : BorelSpace (Mat d) :=
  ⟨BorelSpace.measurable_eq (α := Fin d → Fin d → ℝ)⟩

/-- **The elliptic matrix locus is measurable.**  Being closed in the product
topology, it is Borel, hence measurable for the carrier's matrix σ-algebra. -/
theorem measurableSet_isEllipticMatrix {lam Lam : ℝ} :
    MeasurableSet {A : Mat d | IsEllipticMatrix lam Lam A} :=
  isClosed_isEllipticMatrix.measurableSet

end

end Homogenization
