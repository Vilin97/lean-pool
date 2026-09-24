/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelFinish
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP8
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.SingletonNull

/-!
# Pointwise Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

lemma heatPotentialKernel_abs_le_riesz₂ (z w : ParabolicPoint) :
    |heatPotentialKernel z w| ≤
      1000 * (parabolicRieszKernel 2 z w).toReal := by
  exact _root_.CKN.Core.HeatPotential.heatPotentialKernel_abs_le_riesz₂ z w

lemma heatPotentialSpatialKernel_abs_le_riesz₁ (i : Fin 3)
    (z w : ParabolicPoint) :
    |heatPotentialSpatialKernel i z w| ≤
      300000 * (parabolicRieszKernel 1 z w).toReal := by
  exact _root_.CKN.Core.HeatPotential.heatPotentialSpatialKernel_abs_le_riesz₁ i z w

/-- Riesz-potential majorant for the localized scalar and divergence heat sources. -/
def pointwisePotentialMajorant (g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) : ParabolicPoint → ℝ :=
  fun z =>
    3000 * (parabolicRieszPotential 2
      (fun w => vec3EuclideanNorm (g w)) z).toReal +
    900000 * ∑ j, (parabolicRieszPotential 1
      (fun w => vec3EuclideanNorm (h j w)) z).toReal

















theorem forceLqDataOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    CKN.localVecLp (CKN.spaceTimeSet Ω' J) q f := by
  exact hsol.2.2.2.2.1 Ω' J hbox

end CKN.Core.Step4
