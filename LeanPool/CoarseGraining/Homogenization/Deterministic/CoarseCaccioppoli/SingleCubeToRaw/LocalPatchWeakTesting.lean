/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalPatchCutoff
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.WeakTesting

/-! # Local Patch Weak Testing -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Weak testing with arbitrary-center local Caccioppoli cutoffs

This file specializes the parent-cube weak testing identity to the translated
local canonical cutoffs used in the boundary Caccioppoli proof.  The only
geometric input is that the local outer closed cube is still contained in the
parent open cube, so the product cutoff is an admissible compactly supported
test function in the parent cube.
-/

/-- The harmonic flux paired with the arbitrary-center local cutoff gradient
is integrable on the parent cube. -/
theorem integrableOn_vecDot_harmonicFlux_harmonicFunction_localCanonicalCutoff
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (center : Vec d) {rhoInner rhoOuter : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    MeasureTheory.IntegrableOn
      (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x •
            scalarCutoffGradientField
              (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))
      (cubeSet Q) MeasureTheory.volume := by
  exact
    integrableOn_vecDot_harmonicFlux_harmonicFunction_scalarCutoffGradientField
      Q a w hEll
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter)

/-- Local-cutoff weak testing for an arbitrary patch center whose outer local
closed cube stays inside the parent open cube. -/
theorem
    le_abs_cubeAverage_vecDot_flux_localCanonicalCutoff_of_aHarmonicFunction_of_le_localCanonicalCutoffEnergy
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam F : ℝ}
    (center : Vec d) {rhoInner rhoOuter : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsub : coarseCaccioppoliLocalClosedCube Q center rhoOuter ⊆ openCubeSet Q)
    (hlower :
      F ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x *
              scalarVariationEnergyIntegrand a w x)) :
    F ≤
      |cubeAverage Q
        (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| := by
  exact
    le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
      Q a w hEll
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_openCubeSet
        hinner hinnerOuter hsub)
      hlower

/-- Local-cutoff weak testing for a boundary-touching patch.  Instead of
requiring the outer local closed cube to sit inside the parent open cube, this
uses a localized scalar zero-trace hypothesis to make the cutoff product an
admissible `H¹₀` test function. -/
theorem
    le_abs_cubeAverage_vecDot_flux_localCanonicalCutoff_of_aHarmonicFunction_of_localizedZeroTrace_of_le_localCanonicalCutoffEnergy
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam F : ℝ}
    (center : Vec d) {rhoInner rhoOuter : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V w.toH1.toFun)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsub : coarseCaccioppoliLocalClosedCube Q center rhoOuter ⊆ V)
    (hlower :
      F ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x *
              scalarVariationEnergyIntegrand a w x)) :
    F ≤
      |cubeAverage Q
        (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| := by
  exact
    le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_localizedZeroTrace_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
      Q a w hEll hzero
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter)
      ((coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
        hinner hinnerOuter).trans hsub)
      hlower

end

end Homogenization
