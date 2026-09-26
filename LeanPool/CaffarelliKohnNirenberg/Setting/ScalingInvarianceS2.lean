/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Scaling Invariance S2

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- Space-time scaling homeomorphism used for the divergence-free weak equation. -/
def s2Homeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
      (Homeomorph.addLeft z₀.2))

private theorem s2Homeomorph_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(s2Homeomorph μ hμ z₀) = scalingParabolic μ z₀ := by
  funext z
  rfl

private theorem s2Inverse_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(s2Homeomorph μ hμ z₀).symm =
      (fun z : Vec3 × ℝ =>
        (μ⁻¹ • (z.1 - z₀.1), (μ ^ 2)⁻¹ * (z.2 - z₀.2))) := by
  ext z <;>
    simp [s2Homeomorph, Homeomorph.trans, Homeomorph.prodCongr,
      Homeomorph.smulOfNeZero, Homeomorph.addLeft,
      Equiv.addLeft, Units.smul_def] <;>
    ring

private theorem s2Homeomorph_contDiff (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) :
    ContDiff ℝ (⊤ : ℕ∞) (s2Homeomorph μ hμ z₀).symm := by
  rw [s2Inverse_eq μ hμ z₀]
  fun_prop

private theorem s2_image_spaceTimeSet (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (Ω : Set Vec3) (I : Set ℝ) :
    s2Homeomorph μ hμ z₀ ''
        spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) =
      spaceTimeSet Ω I := by
  change s2Homeomorph μ hμ z₀ ''
      ((rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I)) = Ω ×ˢ I
  rw [show (rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I) =
      (s2Homeomorph μ hμ z₀) ⁻¹' (Ω ×ˢ I) by
    rw [s2Homeomorph_eq]
    exact rescaledSpaceTimeSet_eq_preimage μ z₀ Ω I]
  exact (s2Homeomorph μ hμ z₀).image_preimage _

private theorem s2_pullback_test
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)) :
    (ψ ∘ (s2Homeomorph μ hμ z₀).symm) ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨hψdiff.comp (s2Homeomorph_contDiff μ hμ z₀),
    hψcompact.comp_homeomorph (s2Homeomorph μ hμ z₀).symm, ?_⟩
  change tsupport ψ ⊆
    (rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I) at hψsupport
  rw [tsupport_comp_eq_preimage ψ (s2Homeomorph μ hμ z₀).symm]
  rw [← (s2Homeomorph μ hμ z₀).image_eq_preimage_symm]
  exact (image_mono hψsupport).trans_eq (s2_image_spaceTimeSet μ hμ z₀ Ω I)

private theorem s2_tsupp_bridge (g : ParabolicPoint → ℝ) :
    tsupport g = parabolicHomeomorph ⁻¹'
      (tsupport (fun q : Vec3 × ℝ => g q)) := by
  have hsupp : Function.support g = parabolicHomeomorph ⁻¹'
      (Function.support (fun q : Vec3 × ℝ => g q)) := by
    ext z
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

private theorem s2_spatialPartial_zero
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ))
    (i : Fin 3) : spatialPartial ψ i z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [s2_tsupp_bridge]
    exact hmem
  have hzero := spatialPartial_zero_of_not_mem_tsupport_public hψ hq i
  change spatialPartial ψ i (z.1, z.2) = 0
  exact hzero

theorem s2_rescale
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z)
          (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I,
        ∑ i, u z i * spatialPartial ψ i z = 0)
    (z₀ : ParabolicPoint) {μ : ℝ} (hμ : 0 < μ) :
    ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) →
      IntegrableOn (fun z => ∑ i, rescaleVelocity μ z₀ u z i *
          spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I),
        ∑ i, rescaleVelocity μ z₀ u z i * spatialPartial ψ i z = 0 := by
  intro ψ hψ
  let ψhat : Vec3 × ℝ → ℝ := ψ ∘ (s2Homeomorph μ hμ z₀).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
    exact s2_pullback_test μ hμ z₀ hψ
  obtain ⟨hsource, hzero⟩ := hS2 ψhat hψhat
  have hsourceFull : Integrable
      (fun z => ∑ i, u z i * spatialPartial ψhat i z) volume := by
    apply hsource.integrable_of_forall_notMem_eq_zero
    intro z hz
    have hzero : ∀ i : Fin 3, spatialPartial ψhat i z = 0 := fun i =>
      s2_spatialPartial_zero hψhat.1 hz i
    simp [hzero]
  let G : ParabolicPoint → ℝ := fun z =>
    ∑ i, u z i * spatialPartial ψhat i z
  let Gμ : ParabolicPoint → ℝ := fun z =>
    ∑ i, rescaleVelocity μ z₀ u z i * spatialPartial ψ i z
  have hpoint : ∀ z, Gμ z = μ ^ 2 * G (scalingParabolic μ z₀ z) := by
    intro z
    have hderiv : ∀ i : Fin 3,
        spatialPartial (ψ ∘ (fun w =>
          (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) i
            (scalingParabolic μ z₀ z) =
          μ⁻¹ * spatialPartial ψ i z := by
      intro i
      exact spatialPartial_pullback μ hμ z₀ hψ.1 i z
    dsimp [Gμ, G, ψhat]
    rw [s2Inverse_eq μ hμ z₀]
    change (∑ i, (μ • u (scalingParabolic μ z₀ z)) i * spatialPartial ψ i z) =
      μ ^ 2 * (∑ i, u (scalingParabolic μ z₀ z) i *
        spatialPartial (ψ ∘ (fun w =>
          (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) i
          (scalingParabolic μ z₀ z))
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hderiv i]
    field_simp [hμ.ne']
  have hcomp : IntegrableOn (G ∘ scalingParabolic μ z₀)
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    exact integrable_comp_scaling_test (Ω := Ω) (I := I) μ hμ z₀
      hΩ hI hsourceFull.integrableOn
  have htargetFull : IntegrableOn Gμ
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    have heq : Gμ = (fun z => μ ^ 2 * (G ∘ scalingParabolic μ z₀) z) := by
      funext z
      rw [hpoint]
      rfl
    rw [heq]
    change Integrable (fun z => μ ^ 2 * (G ∘ scalingParabolic μ z₀) z)
      (volume.restrict (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)))
    exact hcomp.const_mul (μ ^ 2)
  have hts : tsupport (show ParabolicPoint → ℝ from ψ) = tsupport ψ := by
    rw [s2_tsupp_bridge, parabolicHomeomorph_preimage]
  have htargetSupport : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) := by
    rw [hts]
    exact hψ.2.2
  have htargetOn := htargetFull.mono_set htargetSupport
  refine ⟨htargetOn, ?_⟩
  have hchange := integral_comp_scaling_test (Ω := Ω) (I := I)
    μ hμ z₀ hΩ hI hsourceFull.aestronglyMeasurable.restrict
  calc
    (∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), Gμ z) =
        ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I), μ ^ 2 * G (scalingParabolic μ z₀ z) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun z => hpoint z)
    _ = μ ^ 2 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), G (scalingParabolic μ z₀ z) := by
          rw [integral_const_mul]
    _ = μ ^ 2 * ((ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
        ∫ z in spaceTimeSet Ω I, G z) := by rw [hchange]
    _ = 0 := by
      rw [show (∫ z in spaceTimeSet Ω I, G z) = 0 by simpa [G] using hzero]
      simp

end CKN
