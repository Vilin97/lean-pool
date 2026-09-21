/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.CoefficientBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.PositiveFactors
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.QOneRoot

/-! # Solution Inputs -/

namespace Homogenization

noncomputable section

open scoped ENNReal

theorem thetaRatio_pos_of_closedCubeHarmonicFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t : ℝ) {lam Lam : ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hs : 0 < s) (ht : 0 < t)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    0 < ThetaRatio Q s t a := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hDataDesc : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hData : OpenCubeDeterministicCoarseData Q a :=
    OpenCubeDescendantDeterministicCoarseData.self hDataDesc
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) (s := t) ht hEllCube hOrigin
  have hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube ((w ρ₁ ρ₂).toCubeSet)
    simpa [scalarVariationEnergyIntegrand] using hflux
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family Q a s hfluxEnergy
  exact
    thetaRatio_pos_of_isEllipticFieldOn_of_openCubeData
      Q a hs ht hEllOpen hData hBsum_s hSigmaSum_t

end

end Homogenization
