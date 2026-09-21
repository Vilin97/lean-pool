/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.ScalarizationWitnesses

/-! # Scalarization Definitions -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Scalarization definitions

Scalar-matrix helper lemmas and the internal scalarization route used to prove
the public Chapter 4 scalar selectors.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace Internal

/-- Internal route package for scalarization of the annealed coarse-grained
matrices on origin cubes.  Public callers should use the direct
`RestrictionLawCarrier.*AtScale` scalar selectors instead. -/
structure AnnealedScalarizationTheory {d : ℕ} (P : RestrictionCoeffLaw d) : Prop where
  scalarized : ∀ n : ℤ, HasAnnealedScalarizationAtScale P n

namespace AnnealedScalarizationTheory

/-- The chosen scalarization witness at scale `n`. -/
noncomputable def witness {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) :
    AnnealedScalarizationWitness P n :=
  Classical.choice (h.scalarized n)

/-- The scalar `\bar\sigma_n`. -/
noncomputable def barSigma {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) : ℝ :=
  (h.witness n).sigma

/-- The scalar `\bar\sigma_{*,n}`. -/
noncomputable def barSigmaStar {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) : ℝ :=
  (h.witness n).sigmaStar

theorem annealedSigma_eq {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) :
    annealedSigmaAtScale P n = h.barSigma n • (1 : Mat d) :=
  (h.witness n).sigma_eq

theorem annealedSigmaStar_eq {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) :
    annealedSigmaStarAtScale P n = h.barSigmaStar n • (1 : Mat d) :=
  (h.witness n).sigmaStar_eq

theorem annealedKappa_eq_zero {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) :
    annealedKappaAtScale P n = 0 :=
  (h.witness n).kappa_eq_zero

/-- The scalar contrast ratio used downstream. -/
noncomputable def contrast {d : ℕ} {P : RestrictionCoeffLaw d}
    (h : AnnealedScalarizationTheory P) (n : ℤ) : ℝ :=
  h.barSigma n * (h.barSigmaStar n)⁻¹

end AnnealedScalarizationTheory

end Internal

/-- A Löwner comparison between scalar matrices is the corresponding scalar
comparison. -/
theorem scalar_le_of_matLoewnerLE_smul_one
    {d : ℕ} [NeZero d] {a b : ℝ}
    (h : MatLoewnerLE (a • (1 : Mat d)) (b • (1 : Mat d))) :
    a ≤ b := by
  have hbasis := h (Pi.single (0 : Fin d) 1)
  simpa [smul_matVecMul, matVecMul_single, vecDot_single_left] using hbasis

/-- Scalar comparisons lift to Löwner comparisons between scalar identity
matrices. -/
theorem matLoewnerLE_smul_one_of_scalar_le
    {d : ℕ} {a b : ℝ} (h : a ≤ b) :
    MatLoewnerLE (a • (1 : Mat d)) (b • (1 : Mat d)) := by
  intro x
  have hnorm_nonneg : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have hmul :
      (1 / 2 : ℝ) * (a * vecNormSq x) ≤
        (1 / 2 : ℝ) * (b * vecNormSq x) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h hnorm_nonneg) (by norm_num)
  have hOne : matVecMul (1 : Mat d) x = x := by
    change (1 : Matrix (Fin d) (Fin d) ℝ).mulVec x = x
    exact Matrix.one_mulVec x
  simpa [smul_matVecMul, vecDot_smul_right, vecNormSq, hOne] using hmul

/-- Scalar coefficients of scalar identity matrices are unique. -/
theorem scalar_eq_of_smul_one_eq_smul_one
    {d : ℕ} [NeZero d] {a b : ℝ}
    (h : a • (1 : Mat d) = b • (1 : Mat d)) :
    a = b := by
  have hentry := congrArg (fun M : Mat d => M 0 0) h
  simpa using hentry

/-- A strictly positive a.e. integrable real function has strictly positive
expectation under a probability measure. -/
theorem integral_pos_of_integrable_pos_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ}
    (hfint : Integrable f μ) (hfpos : ∀ᵐ x ∂μ, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [hfpos] with x hx
    exact le_of_lt hx
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hfint]
  rw [pos_iff_ne_zero]
  intro hsupp_zero
  have hsupp_ae : Function.support f ∈ ae μ := by
    filter_upwards [hfpos] with x hx
    exact hx.ne'
  have hcompl_zero : μ (Function.support f)ᶜ = 0 :=
    mem_ae_iff.mp hsupp_ae
  have huniv_le :
      μ Set.univ ≤ μ (Function.support f) + μ (Function.support f)ᶜ :=
    measure_univ_le_add_compl (μ := μ) (Function.support f)
  have huniv_le_zero : μ Set.univ ≤ 0 := by
    simp [hsupp_zero, hcompl_zero] at huniv_le
  have huniv_pos : 0 < μ Set.univ := by
    simp
  exact (not_lt_of_ge huniv_le_zero) huniv_pos

theorem matrix_posDef_diag_pos {d : ℕ} {A : Mat d} (hA : A.PosDef) (i : Fin d) :
    0 < A i i := by
  simpa using (hA.diag_pos (i := i))

/-- If the integral of an a.e. positive-definite matrix field is a scalar
multiple of the identity, then the scalar coefficient is positive. -/
theorem scalar_coefficient_pos_of_smul_one_eq_integral_posDef
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {d : ℕ} [NeZero d] {F : α → Mat d} {c : ℝ}
    (hFint : Integrable F μ)
    (hPos : ∀ᵐ x ∂μ, (F x).PosDef)
    (hScalar : (∫ x, F x ∂μ) = c • (1 : Mat d)) :
    0 < c := by
  let i : Fin d := 0
  have hEntryInt : Integrable (fun x => F x i i) μ :=
    Integrable.eval (Integrable.eval hFint i) i
  have hEntryPos : ∀ᵐ x ∂μ, 0 < F x i i := by
    filter_upwards [hPos] with x hx
    exact matrix_posDef_diag_pos hx i
  have hIntegralPos : 0 < ∫ x, F x i i ∂μ :=
    integral_pos_of_integrable_pos_ae hEntryInt hEntryPos
  have hCoeff : (∫ x, F x i i ∂μ) = c := by
    calc
      (∫ x, F x i i ∂μ) = (∫ x, F x ∂μ) i i := by
        exact (integral_matrix_apply (μ := μ) (f := F) hFint i i).symm
      _ = (c • (1 : Mat d)) i i := by
        rw [hScalar]
      _ = c := by
        simp [i]
  simpa [hCoeff] using hIntegralPos

namespace Internal

/-- Internal primitive scalarization data for the inverse-star and upper-left
annealed blocks.  Public callers should use direct structural-law endpoints. -/
abbrev AnnealedPrimitiveScalarizationData {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) :=
  AnnealedScalarizationPrimitiveData P n

namespace AnnealedPrimitiveScalarizationData

/-- The scalar coefficient of the annealed inverse-star block. -/
noncomputable def barSigmaStarInv {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  Classical.choose
    (annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant P n
      h.sigmaStarInvFlip h.sigmaStarInvSwap)

/-- The scalar coefficient of the annealed upper-left block. -/
noncomputable def barB {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  Classical.choose
    (annealedBAtScale_isScalarMatrix_of_invariant P n h.bFlip h.bSwap)

/-- The primitive scalar contrast used by downstream estimates. -/
noncomputable def contrast {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  h.barB * h.barSigmaStarInv

theorem sigmaStarInv_eq {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) :
    annealedSigmaStarInvAtScale P n = h.barSigmaStarInv • (1 : Mat d) :=
  Classical.choose_spec
    (annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant P n
      h.sigmaStarInvFlip h.sigmaStarInvSwap)

theorem b_eq {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) :
    annealedBAtScale P n = h.barB • (1 : Mat d) :=
  Classical.choose_spec
    (annealedBAtScale_isScalarMatrix_of_invariant P n h.bFlip h.bSwap)

theorem sigma_eq {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) :
    annealedSigmaAtScale P n = h.barB • (1 : Mat d) := by
  rw [annealedSigmaAtScale_eq_annealedBAtScale_of_sigmaStarInvKappaMean_eq_zero
    P n h.sigmaStarInvKappaMean_eq_zero]
  exact h.b_eq

theorem kappa_eq_zero {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) :
    annealedKappaAtScale P n = 0 :=
  annealedKappaAtScale_eq_zero_of_sigmaStarInvKappaMean_eq_zero
    P n h.sigmaStarInvKappaMean_eq_zero

theorem barSigma_eq_barB {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hPrim : AnnealedPrimitiveScalarizationData (d := d) P n) :
    hScal.barSigma n = hPrim.barB :=
  scalar_eq_of_smul_one_eq_smul_one <| by
    calc
      hScal.barSigma n • (1 : Mat d) = annealedSigmaAtScale P n :=
        (hScal.annealedSigma_eq n).symm
      _ = hPrim.barB • (1 : Mat d) := hPrim.sigma_eq

theorem barSigmaStar_eq_inv_barSigmaStarInv {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} {n : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hPrim : AnnealedPrimitiveScalarizationData (d := d) P n) :
    hScal.barSigmaStar n = hPrim.barSigmaStarInv⁻¹ :=
  scalar_eq_of_smul_one_eq_smul_one <| by
    have hInv :
        (hPrim.barSigmaStarInv • (1 : Mat d))⁻¹ =
          hPrim.barSigmaStarInv⁻¹ • (1 : Mat d) := by
      by_cases hs : hPrim.barSigmaStarInv = 0
      · simp [hs]
      · rw [nonsing_inv_smul hPrim.barSigmaStarInv hs (by simp)]
        simp
    calc
      hScal.barSigmaStar n • (1 : Mat d) = annealedSigmaStarAtScale P n :=
        (hScal.annealedSigmaStar_eq n).symm
      _ = (annealedSigmaStarInvAtScale P n)⁻¹ := rfl
      _ = (hPrim.barSigmaStarInv • (1 : Mat d))⁻¹ := by
        rw [hPrim.sigmaStarInv_eq]
      _ = hPrim.barSigmaStarInv⁻¹ • (1 : Mat d) := hInv

theorem scalar_contrast_eq {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hPrim : AnnealedPrimitiveScalarizationData (d := d) P n) :
    hScal.contrast n = hPrim.contrast := by
  simp [AnnealedScalarizationTheory.contrast, contrast,
    barSigma_eq_barB hScal hPrim,
    barSigmaStar_eq_inv_barSigmaStarInv hScal hPrim]

theorem barSigmaStarInv_le_of_matLoewnerLE
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {m n : ℤ}
    (hm : AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hLE : MatLoewnerLE (annealedSigmaStarInvAtScale P m)
      (annealedSigmaStarInvAtScale P n)) :
    hm.barSigmaStarInv ≤ hn.barSigmaStarInv := by
  rw [hm.sigmaStarInv_eq, hn.sigmaStarInv_eq] at hLE
  exact scalar_le_of_matLoewnerLE_smul_one hLE

theorem barB_le_of_matLoewnerLE
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {m n : ℤ}
    (hm : AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hLE : MatLoewnerLE (annealedBAtScale P m) (annealedBAtScale P n)) :
    hm.barB ≤ hn.barB := by
  rw [hm.b_eq, hn.b_eq] at hLE
  exact scalar_le_of_matLoewnerLE_smul_one hLE

theorem contrast_le_of_component_le
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {m n : ℤ}
    (hm : AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hB_le : hm.barB ≤ hn.barB)
    (hStar_le : hm.barSigmaStarInv ≤ hn.barSigmaStarInv)
    (hStar_m_nonneg : 0 ≤ hm.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hn.barB) :
    hm.contrast ≤ hn.contrast := by
  dsimp [contrast]
  exact mul_le_mul hB_le hStar_le hStar_m_nonneg hB_n_nonneg

theorem barSigmaStar_le_of_barSigmaStarInv_le
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hm : AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hStar_le : hm.barSigmaStarInv ≤ hn.barSigmaStarInv)
    (hStar_m_pos : 0 < hm.barSigmaStarInv) :
    hScal.barSigmaStar n ≤ hScal.barSigmaStar m := by
  have hStar_n_pos : 0 < hn.barSigmaStarInv :=
    lt_of_lt_of_le hStar_m_pos hStar_le
  have hInv_le : hn.barSigmaStarInv⁻¹ ≤ hm.barSigmaStarInv⁻¹ :=
    (inv_le_inv₀ hStar_n_pos hStar_m_pos).2 hStar_le
  simpa [barSigmaStar_eq_inv_barSigmaStarInv hScal hm,
    barSigmaStar_eq_inv_barSigmaStarInv hScal hn] using hInv_le

theorem barSigmaStar_le_barSigma_of_one_le_contrast
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hPrim : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hContrast : 1 ≤ hPrim.contrast)
    (hStar_pos : 0 < hPrim.barSigmaStarInv) :
    hScal.barSigmaStar n ≤ hScal.barSigma n := by
  have hInv_le : hPrim.barSigmaStarInv⁻¹ ≤ hPrim.barB := by
    exact (inv_le_iff_one_le_mul₀' hStar_pos).2 (by
      simpa [contrast, mul_comm] using hContrast)
  simpa [barSigmaStar_eq_inv_barSigmaStarInv hScal hPrim,
    barSigma_eq_barB hScal hPrim] using hInv_le

theorem barSigma_le_of_barB_le
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hScal : AnnealedScalarizationTheory (d := d) P)
    (hm : AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : AnnealedPrimitiveScalarizationData (d := d) P n)
    (hB_le : hm.barB ≤ hn.barB) :
    hScal.barSigma m ≤ hScal.barSigma n := by
  simpa [barSigma_eq_barB hScal hm, barSigma_eq_barB hScal hn] using hB_le

end AnnealedPrimitiveScalarizationData

/-- Internal scalar coefficient of the primitive upper-left block. -/
noncomputable abbrev barBAtScaleOfPrimitive {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  h.barB

/-- Internal scalar coefficient of the primitive inverse-star block. -/
noncomputable abbrev barSigmaStarInvAtScaleOfPrimitive {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  h.barSigmaStarInv

/-- Internal primitive contrast `Theta_n`. -/
noncomputable abbrev annealedThetaAtScaleOfPrimitive {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} {n : ℤ}
    (h : AnnealedPrimitiveScalarizationData (d := d) P n) : ℝ :=
  h.contrast

end Internal

end

end Ch04
end Book
end Homogenization
