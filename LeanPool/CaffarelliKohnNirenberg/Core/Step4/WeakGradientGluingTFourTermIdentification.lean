/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTGapForceIncrement

/-! # Four-term identification on interior collars -/

public section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The actual weak pressure derivative is the signed raw Riesz sum, harmonic
 derivative, force increment, and signed centred-source correction. -/
theorem ae_actual_pressure_eq_four_terms_half_gap_collar
    (R₀ R₁ : ℝ) (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀one : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (T : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hT : ∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun w => (∑ k, Du w j k * u w k) - f w j) (y,s)))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hcell : r ≤ (R₀-R₁)/4)
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), ∀ i : Fin 3,
      (fun y => Dp (y,s) i) =ᵐ[volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)]
      (fun x =>
        let hρ : 0 < (R₀-R₁)/2 := by linarith only [hgap];
        let η := mollifiedBallCutoff z.1 hρ;
        let c := sourceSliceCentredMean z.1 ((R₀-R₁)/2) u;
        -(∑ j, T j i (x,s)) +
          classicalGradient (harmonicPressurePart η u c p s) x i +
          gapForceIncrement z hρ u p f i (x,s) -
          ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
            (rieszSecondL2_weak_type j i)
            (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
              (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) j) x) := by
  filter_upwards [ae_actual_pressure_eq_raw_riesz_half_gap_collar
    R₀ R₁ hR₁ hgap hR₀one hsol hdom hDp T hT hr hcell hz] with s hs
  intro i
  filter_upwards [hs i] with x hx
  rw [hx]
  dsimp only [rawCorrectedPressureRemainder, gapForceIncrement]
  ring

end CKN.Core.Step4
