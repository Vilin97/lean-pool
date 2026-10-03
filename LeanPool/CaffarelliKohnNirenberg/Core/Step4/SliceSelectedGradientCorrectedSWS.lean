/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.OperatorConstantNonneg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTBounds

/-!
# Corrected pressure-gradient slices from suitable-solution data

The force-free centred source and its tested identity are extracted from
suitable-solution data. The resulting quantitative slice estimate is in the
form used to transfer a doubled-scale bound to cell data.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- The corrected force-free centred-source slice estimate, with the
quantitative bound consumed by the doubled-slice cell transfer. Its only
analytic hypothesis beyond suitability and cylinder containment is the
operator bound `hCZ_p1`. -/
theorem slice_selected_gradient_corrected_ae_of_sws_data
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hCZ_p1 : czP1OperatorConstant ≤ C_P1)
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
            ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant
              C₈ z.1 hρ f s)) := by
  have hC_P1 : 0 ≤ C_P1 :=
    czP1OperatorConstant_nonneg.trans hCZ_p1
  have hselected := centredSWS_selected_gradient_ae
    C₁₇ C_P1 C₈ hC₁₇ hC_P1 hCZ_p1 hC₈ hsol hρ hsub
  exact hselected

end CKN.Core.Step4
