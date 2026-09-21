/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Identity

/-! # Bound -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ProductBound

Cutoff-product bound by Ch4 scalar-response weak norms.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

theorem abs_cutoffProductTermOnDependentFamily_le_scaledWeakNormProduct
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s t : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (ht_pos : 0 < t)
    (hst : s + t ≤ 1)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {φ : Vec d → ℝ} (p q p0 q0 : Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q))
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField φ x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤ B) :
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let scaledGrad := cubeBesovScaleWeight (-s) Q * gradWeak
    let scaledFlux := cubeBesovScaleWeight (-t) Q * fluxWeak
    let gradCoeff :=
      (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ (scalarCutoffGradientField φ)) *
        ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (Fintype.card (Fin d) : ℝ))
    let fluxCoeff :=
      (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + (1 - s)) *
          cubeBesovScaleWeight (-(1 - s - t)) Q)
    |cutoffProductTermOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        φ p q p0 q0| ≤
      (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
  intro gradWeak fluxWeak scaledGrad scaledFlux gradCoeff fluxCoeff
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let u : H1Function (openCubeSet Q) :=
    canonicalMaximizerPotentialDefectH1OnCube Q aQ p q p0
  let flux : Vec d → Vec d := canonicalMaximizerFluxDefectOnCube Q aQ p q q0
  let ξ : Vec d → Vec d := scalarCutoffGradientField φ
  let A : ℝ :=
    cubeAverage Q
      (fun x => vecDot (flux x)
        (((u x - cubeAverage Q (fun y => u y)) • ξ x : Vec d)))
  have hid :
      cutoffProductTermOnCube Q aQ φ p q p0 q0 = -(1 / 2 : ℝ) * A := by
    have hraw :=
      cutoffProductTermOnCube_eq_neg_half_cubeAverage_fluxDefect_centeredPotentialDefect_smul_scalarCutoffGradientField
        (Q := Q) (a := aQ) (φ := φ) p q p0 q0
        hφ hφ_compact hφ_sub hcutoffGradient
    simpa [A, u, flux, ξ, F, aQ] using hraw
  have hhalf :
      |cutoffProductTermOnCube Q aQ φ p q p0 q0| ≤ |A| := by
    rw [hid]
    have h_abs : |-(1 / 2 : ℝ) * A| = (1 / 2 : ℝ) * |A| := by
      rw [abs_mul]
      norm_num
    rw [h_abs]
    nlinarith [abs_nonneg A]
  have hmain :
      |A| ≤ (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
    simpa [A, u, flux, ξ, gradWeak, fluxWeak, scaledGrad, scaledFlux,
      gradCoeff, fluxCoeff, F, aQ, canonicalMaximizerPotentialDefectH1OnCube_grad] using
      abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct
        (Q := Q) (s := s) (t := t) hs_pos hs_lt_one hst
        (flux := flux) (u := u) (ξ := ξ) (B := B)
        (gradWeak := gradWeak) (fluxWeak := fluxWeak)
        hB hcutoffGradient hcutoffSmooth hcutoffDeriv
        (by simpa [flux] using canonicalMaximizerFluxDefectOnCube_memLp Q aQ p q q0)
        (by
          intro N
          have hraw :=
            cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
              a ha Q hs_pos N p q p0
          unfold canonicalMaximizerGradientDefectOnCube at hraw
          simpa [u, F, aQ, gradWeak, canonicalMaximizerPotentialDefectH1OnCube_grad] using hraw)
        (by
          intro N
          simpa [flux, F, aQ, fluxWeak] using
            cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
              a ha Q ht_pos N p q q0)
  simpa [F, aQ] using hhalf.trans hmain

/-- The actual manuscript cutoff product term is controlled by the Ch4
scalar-response flux weak norms, once `cutoffGradient` is identified as the
gradient field of the scalar cutoff. -/
theorem abs_cutoffProductTermOnDependentFamily_le_cutoffProductBridgeRHS
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {φ : Vec d → ℝ} (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {cutoffCircOne cutoffCircS cutoffDerivative poincareConst cutoffConstant
      centeredCutoffConstant : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient_eq : cutoffGradient = scalarCutoffGradientField φ)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    |cutoffProductTermOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        φ p q p0 q0| ≤
      cutoffProductBridgeRHS Q s cutoffGradient
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
        ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let T : ℝ :=
    cubeAverage Q
      (fun x =>
        vecDot
          (canonicalMaximizerFluxDefectOnCube Q aQ p q q0 x)
          (canonicalMaximizerPotentialDefectOnCube Q aQ p q p0 x •
            cutoffGradient x))
  have hid :
      cutoffProductTermOnCube Q aQ φ p q p0 q0 =
        -(1 / 2 : ℝ) * T := by
    have hraw :=
      cutoffProductTermOnCube_eq_neg_half_cubeAverage_fluxDefect_potentialDefect_smul_scalarCutoffGradientField
        (Q := Q) (a := aQ) (φ := φ) p q p0 q0 hφ hφ_compact hφ_sub
    simpa [T, hcutoffGradient_eq] using hraw
  have hprod_abs : |cutoffProductTermOnCube Q aQ φ p q p0 q0| ≤ |T| := by
    rw [hid]
    have habs : |-(1 / 2 : ℝ) * T| = (1 / 2 : ℝ) * |T| := by
      rw [abs_mul]
      norm_num
    rw [habs]
    nlinarith [abs_nonneg T]
  have hbridge :
      |T| ≤
        cutoffProductBridgeRHS Q s cutoffGradient
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
          ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
          cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
    simpa [T, F, aQ] using
      productTerm_le_cutoffProductBridge_of_dependentCanonicalMaximizer
        (Q := Q) (s := s) (a := a) (ha := ha)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        (dualField := dualField) (cutoffGradient := cutoffGradient)
        (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
        (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
        (cutoffConstant := cutoffConstant)
        (centeredCutoffConstant := centeredCutoffConstant)
        hcutoffDerivative hs_pos hs_lt_one hdualField hcutoffGradient
        hcutoffConstant hcenteredCutoffConstant hpoincareConst
        hcutoffCircOne hcutoffCircS hfull hcutoffSmooth hcutoffDeriv
        hdualCircOne hdualCircS hcutoffConstant_bound
        hcenteredCutoffConstant_bound
  exact hprod_abs.trans hbridge

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
