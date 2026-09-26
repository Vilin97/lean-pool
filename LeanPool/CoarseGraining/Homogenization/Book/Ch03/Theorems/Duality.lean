/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.DualityPositivePairing
public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.SharpLoss

/-! # Duality -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.3.1: Duality estimate from flux defect to solution comparison

This file freezes the public contract for
`l.duality.from.flux.defect.deterministic.theory`.
-/

noncomputable section

/-- Public two-exponent replacement package for the deterministic duality
estimate.  This is the proved replacement surface for the false same-exponent
route: the comparison fields are measured at exponent `s`, while the localized
flux defect is measured at an independent exponent `t < s / 2`. -/
structure FluxDefectDualityTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {a0 : ConstantCoeffMatrix d}
        {s t : ℝ} {j : ℕ},
        IsPositiveScalarMatrix a0.matrix →
        (w : HomogenizationComparisonDatum Q a a0) →
        0 < s → 0 < t → t < s / 2 → s < 1 →
          homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v ≤
            dualityFromFluxDefectExponentLossRHS C Q a a0 s t j w.u

private theorem fluxDefectDualityTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss
    {d : ℕ} [NeZero d] {Cproj : ℝ}
    (hproj : ScalarSolutionComparisonDualityEstimateExponentLoss d Cproj) :
    FluxDefectDualityTheory d := by
  let C : ℝ := Cproj + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith [hproj.1]
  refine ⟨⟨C, hC_pos, ?_⟩⟩
  intro Q a a0 s t j ha0 w hs ht hts hs_lt
  rcases ha0 with ⟨sigma0, hsigma0, ha0eq⟩
  let L : ℝ :=
    localizedFluxDefectNegativeBesovAverageTwo Q t
      (fluxDefect (publicCoeffField Q a) (scalarMatrix (d := d) sigma0) w.u.grad) j
  have hlhs_eq :
      homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v =
        solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
          (scalarMatrix (d := d) sigma0) w.u.grad w.v.grad := by
    simpa [ha0eq] using
      homogenizationComparisonNegativeBesovLHS_eq_solutionComparisonNegativeBesovLhs_publicCoeffField
        Q a a0 s w.u w.v
  have hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q)
        (publicCoeffField Q a) (scalarMatrix (d := d) sigma0)
        w.u.grad w.v.grad := by
    simpa [ha0eq, publicH1ToCubeSet_grad] using
      w.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
  have hF :
      MemVectorL2 (cubeSet Q)
        (fluxDefect (publicCoeffField Q a) (scalarMatrix (d := d) sigma0)
          w.u.grad) := by
    have hbase :
        MemVectorL2 (cubeSet Q)
          (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) :=
      publicH1_fluxDefect_memVectorL2_descendant_cubeSet
        (Q := Q) (R := Q) (a := a) (a0 := a0) (j := 0) w.u (by simp)
    simpa [ha0eq] using hbase
  have hinternal :
      solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
          (scalarMatrix (d := d) sigma0) w.u.grad w.v.grad ≤
        Cproj * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L := by
    dsimp [L]
    exact
      solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimateExponentLoss
        hproj Q (publicCoeffField Q a) sigma0 w.u.grad w.v.grad j
        hsigma0 hs ht hts hs_lt hF hcomparison
  have hlocalized_eq :
      localizedHomogenizationFluxDefectAverage Q a a0 t j w.u = L := by
    dsimp [L]
    simpa [ha0eq] using
      localizedHomogenizationFluxDefectAverage_eq_localizedFluxDefectNegativeBesovAverageTwo_publicCoeffField
        Q a a0 t j w.u
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact localizedFluxDefectNegativeBesovAverageTwo_nonneg Q t
      (fluxDefect (publicCoeffField Q a) (scalarMatrix (d := d) sigma0) w.u.grad) j
  have hfactor_nonneg :
      0 ≤ s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ := by
    have ht_half : t < 1 / 2 := by nlinarith
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hs.le)
        (pow_nonneg (inv_nonneg.mpr ht.le) _))
      (inv_nonneg.mpr (by linarith : 0 ≤ (1 / 2 : ℝ) - t))
  calc
    homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v
        =
      solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
        (scalarMatrix (d := d) sigma0) w.u.grad w.v.grad := hlhs_eq
    _ ≤
        Cproj * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L := hinternal
    _ ≤
        C * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L := by
          have hright_nonneg :
              0 ≤ s⁻¹ * (t⁻¹) ^ (2 : ℕ) *
                ((1 / 2 : ℝ) - t)⁻¹ * L :=
            mul_nonneg hfactor_nonneg hL_nonneg
          calc
            Cproj * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L =
                Cproj *
                  (s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L) := by ring
            _ ≤
                C *
                  (s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L) :=
              mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hright_nonneg
            _ =
                C * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ * L := by ring
    _ = dualityFromFluxDefectExponentLossRHS C Q a a0 s t j w.u := by
          unfold dualityFromFluxDefectExponentLossRHS
          rw [hlocalized_eq]

private theorem fluxDefectDualityTheory_of_dirichletBesov_of_coordinateBridgeSharpLoss_of_localizedPairing
    {d : ℕ} [NeZero d] {Cdir Cbridge Cpairing : ℝ}
    (hdir : DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d Cdir)
    (hbridge : UnitFullDualCoordinateOverlappingBridgeSharpLoss d Cbridge)
    (hpair : LocalizedFluxDefectPositivePairingEstimate d Cpairing) :
    FluxDefectDualityTheory d :=
  fluxDefectDualityTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss
    ((scalarSolutionComparisonGenuineDualityEstimateSharpLoss_of_dirichletBesov_of_coordinateBridgeSharpLoss_of_localizedPairing
      hdir hbridge hpair).to_exponentLoss)

/-- Public two-exponent duality package with the Dirichlet Besov theorem and
localized positive pairing theorem discharged.  The only remaining analytic
input is the honest sharp-boundary coordinate full-dual-test/
overlapping-positive bridge. -/
private theorem fluxDefectDualityTheory_of_coordinateBridge
    {d : ℕ} [NeZero d] {Cbridge : ℝ}
    (hbridge : UnitFullDualCoordinateOverlappingBridgeSharpLoss d Cbridge) :
    FluxDefectDualityTheory d := by
  rcases Homogenization.exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform d with
    ⟨Cdir, hdir⟩
  exact
    fluxDefectDualityTheory_of_dirichletBesov_of_coordinateBridgeSharpLoss_of_localizedPairing
      hdir hbridge
      (localizedFluxDefectPositivePairingEstimate_standardOverlap d)

/-- Public two-exponent duality package with all currently formalized
analytic inputs discharged. -/
theorem fluxDefectDualityTheory
    (d : ℕ) [NeZero d] :
    FluxDefectDualityTheory d :=
  fluxDefectDualityTheory_of_coordinateBridge
    (unitFullDualCoordinateOverlappingBridgeSharpLoss d)

end

end Ch03
end Book
end Homogenization
