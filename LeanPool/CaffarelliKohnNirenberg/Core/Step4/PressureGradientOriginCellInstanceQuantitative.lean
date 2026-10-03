/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstancePressure
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputs
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1Closer

/-!
# Quantitative slice gradients from suitability

The complete majorant in `eq:pressure-gradient-morrey` is retained when
constructing the local pressure gradient on one interior cylinder.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The explicit source, harmonic, and force majorant of
`eq:pressure-gradient-morrey` on one interior cylinder. -/
@[expose]
def originSliceGradientMajorant
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) : ℝ≥0∞ :=
  let c : Vec3 := fun j => average (volume.restrict (vec3Ball z.1 ρ))
    (fun y : Vec3 => u (y, s) j)
  let V : Vec3 → Vec3 := pressureDivergenceCutoffSourceCentredTensor
    (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
    (fun y => u (y, s)) (fun y => Du (y, s)) c
  ENNReal.ofReal czGradientOperatorConstant *
      (∑ i : Fin 3, eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
    ENNReal.ofReal ((1000 * harmonicInteriorDisplayConstant) *
      (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
        (9 * max czP1OperatorConstant 0) *
          (∫ y in vec3Ball z.1 ρ, (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^
            (2 / 3 : ℝ) + harmonicRemainderForceBound z hρ f s) *
      ρ ^ (-1 / 2 : ℝ)) +
    ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant
      sliceForceGradientConstant z.1 hρ f s)

/-- A suitable solution has a spatial weak pressure gradient on almost every
half-ball slice, with the complete quantitative bound (`eq:pressure-gradient-morrey`). -/
theorem origin_local_slice_gradient_bound_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
            originSliceGradientMajorant u Du p f z hρ s) := by
  let c : ℝ → Vec3 := fun s j => average (volume.restrict (vec3Ball z.1 ρ))
    (fun y : Vec3 => u (y, s) j)
  let V : ParabolicPoint → Vec3 := fun w =>
    pressureDivergenceCutoffSourceCentredTensor
      (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
      (fun y => u (y, w.2)) (fun y => Du (y, w.2)) (c w.2) w.1
  have hsource := origin_tensor_source_data_ae_of_sws hsol hρ hsub c
  have hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)) := by
    filter_upwards [hsource] with s hs
    exact ⟨hs.1, hs.2.1⟩
  have hpair := hsource.mono (fun _ hs => hs.2.2)
  have hCZ := pressureP1_thetaDecay_hCZ_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)
  have hP78 := slice_selected_gradient_hP78_input_of_sws hsol hρ hsub
  have hE : ∀ s : ℝ, 0 ≤ ∫ y in vec3Ball z.1 ρ,
      (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ) := by
    intro s
    exact integral_nonneg (fun y => Real.rpow_nonneg (by unfold utensorNorm; positivity) _)
  have hF : ∀ s, 0 ≤ harmonicRemainderForceBound z hρ f s :=
    fun _ => le_max_right _ _
  have hselected := slice_selected_gradient_ae_of_sws_of_source_data_unconditional
    (1000 * harmonicInteriorDisplayConstant) (9 * max czP1OperatorConstant 0)
    sliceForceGradientConstant le_rfl le_rfl hsol hρ hsub
    (mul_nonneg (by norm_num) (le_max_right _ _)) hE hF hCZ hP78 hV hpair
  exact hselected

end CKN.Core.Step4
