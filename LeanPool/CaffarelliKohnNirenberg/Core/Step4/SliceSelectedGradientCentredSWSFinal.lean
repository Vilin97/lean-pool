/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSSource
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1UnconditionalAssembly
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthSWS

/-!
# The centred pressure-gradient estimate from suitable-solution data

All slice inputs to the unconditional gradient selector are supplied by
`def:sws` and cylinder containment. The numerical constants precede the
solution, and the source is the force-free centred tensor source.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- Display (3.5) with the force-free centred source and every analytic slice
input extracted from the suitable weak solution and cylinder geometry. -/
theorem centredSWS_selected_gradient_ae
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hC_P1 : 0 ≤ C_P1) (hoperator : czP1OperatorConstant ≤ C_P1)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
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
          ENNReal.ofReal czGradientOperatorConstant *
              (∑ _i : Fin 3, centredSWSCentredMajorant z.1 ρ q u Du f s) +
            ENNReal.ofReal (C₁₇ *
              (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
                  (volume.restrict (euclideanBall z.1 ρ)) +
                (9 * C_P1) * (∫ y in vec3Ball z.1 ρ,
                  (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) +
                harmonicRemainderForceBound z hρ f s) * ρ ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant C₈
              z.1 hρ f s)) := by
  let V := sourceMorreyCutoffVCentredTensorSpacetime
    (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
    u Du (sourceSliceCentredMean z.1 ρ u)
  have hCZ := pressureP1_thetaDecay_hCZ_of_sws C_P1 hC_P1 hoperator hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)
  have hpair := centredSWS_pairing_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u)
  have hselected := slice_selected_gradient_ae_of_sws_of_source_data_unconditional
    (V := V) C₁₇ (9 * C_P1) C₈ hC₁₇ hC₈ hsol hρ hsub
    (mul_nonneg (by norm_num) hC_P1)
    (fun s => integral_nonneg fun y => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (fun s => le_max_right _ _) hCZ
    (slice_selected_gradient_hP78_input_of_sws_centred hsol hρ hsub)
    (centredSWS_source_data_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u))
    (by filter_upwards [hpair] with s hs; exact fun ψ hψ _ => hs ψ hψ)
  filter_upwards [hselected, centredSWS_source_bound_ae hsol hρ hsub] with s hs hbound
  obtain ⟨D, hloc, hmem, hweak, hD⟩ := hs
  refine ⟨D, hloc, hmem, hweak, fun k => (hD k).trans ?_⟩
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) bot_le) le_rfl) le_rfl

end CKN.Core.Step4
