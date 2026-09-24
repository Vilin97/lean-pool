/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableRiesz
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableSelection

/-! # Identification of one measurable pressure remainder

The same selected pressure derivative is decomposed into completed Riesz
fields and a measurable remainder. Weak derivative uniqueness identifies
that remainder with the classical harmonic and far-force gradient on slices.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The algebraically defined remainder of a fixed weak pressure gradient
agrees with the smooth harmonic and far-force remainder on almost every slice. -/
theorem ae_fixed_remainder_eq_classical_gradient
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJsub : J ⊆ Ioc (z.2 - ρ ^ 2) z.2)
    {Dp : ParabolicPoint → Vec3}
    (hDp : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball z.1 (ρ / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z.1 (ρ / 2)) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    {T F : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hT : ∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder z.1 z.2 ρ).indicator (fun w =>
          sourceMorreyCutoffVCentredTensorSpacetime (mollifiedBallCutoff z.1 hρ)
            (spatialDeriv (mollifiedBallCutoff z.1 hρ)) u Du
            (sourceSliceCentredMean z.1 ρ u) w j) (y, s)))
    (hF : ∀ j i, ∀ᵐ s ∂volume, (fun y => F j i (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder z.1 z.2 ρ).indicator
          (fun w => mollifiedBallCutoff z.1 hρ w.1 * f w j) (y, s))) :
    ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      (fun y => Dp (y, s) i + (∑ j, T j i (y, s)) - ∑ j, F j i (y, s))
        =ᵐ[volume.restrict (vec3Ball z.1 (ρ / 2))]
      fun y => classicalGradient
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (sourceSliceCentredMean z.1 ρ u) p s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s) y i := by
  have ht := (ae_all_iff.mpr (fun j => ae_all_iff.mpr (hT j)))
  have hf := (ae_all_iff.mpr (fun j => ae_all_iff.mpr (hF j)))
  have hid := ae_restrict_of_ae_restrict_of_subset hJsub
    (ae_weak_pressure_derivative_eq_fixed_riesz_of_sws hsol hρ hsub)
  filter_upwards [hDp, hid, ae_restrict_of_ae ht, ae_restrict_of_ae hf,
    ae_restrict_mem hJ] with s hd hi ht' hf' hs
  intro i
  have hts : ∀ᵐ y ∂volume, ∀ j, T j i (y, s) =
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => sourceMorreyCutoffVCentredTensorSpacetime (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ)) u Du
          (sourceSliceCentredMean z.1 ρ u) (y, s) j) y := by
    apply ae_all_iff.mpr
    intro j
    have hj := ht' j i
    rw [(fixed_pressure_sources_indicator_slice_eq (u := u) (Du := Du) (f := f) hρ (hJsub hs) j).1] at hj
    exact hj
  have hfs : ∀ᵐ y ∂volume, ∀ j, F j i (y, s) =
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) y := by
    apply ae_all_iff.mpr
    intro j
    have hj := hf' j i
    rw [(fixed_pressure_sources_indicator_slice_eq (u := u) (Du := Du) (f := f) hρ (hJsub hs) j).2] at hj
    exact hj
  filter_upwards [hi i _ (hd i).1 (hd i).2,
    ae_restrict_of_ae hts, ae_restrict_of_ae hfs] with y hy ht'' hf''
  simp only [ht'', hf'']
  linarith only [hy]

end CKN.Core.Step4
