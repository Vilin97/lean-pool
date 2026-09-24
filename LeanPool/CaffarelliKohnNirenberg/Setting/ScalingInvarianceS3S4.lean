/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Scaling Invariance S3 S4

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

def s34Homeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
      (Homeomorph.addLeft z₀.2))

private theorem s34Homeomorph_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(s34Homeomorph μ hμ z₀) = scalingParabolic μ z₀ := by
  funext z
  rfl

private theorem s34Inverse_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(s34Homeomorph μ hμ z₀).symm =
      (fun z : Vec3 × ℝ =>
        (μ⁻¹ • (z.1 - z₀.1), (μ ^ 2)⁻¹ * (z.2 - z₀.2))) := by
  ext z <;>
    simp [s34Homeomorph, Homeomorph.trans, Homeomorph.prodCongr,
      Homeomorph.smulOfNeZero, Homeomorph.addLeft, Equiv.addLeft,
      Units.smul_def] <;>
    ring

private theorem s34Homeomorph_contDiff (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) :
    ContDiff ℝ (⊤ : ℕ∞) (s34Homeomorph μ hμ z₀).symm := by
  rw [s34Inverse_eq μ hμ z₀]
  fun_prop

private theorem s34_image_spaceTimeSet (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (Ω : Set Vec3) (I : Set ℝ) :
    s34Homeomorph μ hμ z₀ ''
        spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) =
      spaceTimeSet Ω I := by
  change s34Homeomorph μ hμ z₀ ''
      ((rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I)) = Ω ×ˢ I
  rw [show (rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I) =
      (s34Homeomorph μ hμ z₀) ⁻¹' (Ω ×ˢ I) by
    rw [s34Homeomorph_eq]
    exact rescaledSpaceTimeSet_eq_preimage μ z₀ Ω I]
  exact (s34Homeomorph μ hμ z₀).image_preimage _

private theorem s34_pullback_test {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction
      (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)) :
    (φ ∘ (s34Homeomorph μ hμ z₀).symm) ∈
      spaceTimeTestFunction Ω I := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  refine ⟨hφdiff.comp (s34Homeomorph_contDiff μ hμ z₀),
    hφcompact.comp_homeomorph (s34Homeomorph μ hμ z₀).symm, ?_⟩
  change tsupport φ ⊆
    (rescaledSpace μ z₀.1 Ω) ×ˢ (rescaledTime μ z₀.2 I) at hφsupport
  rw [tsupport_comp_eq_preimage φ (s34Homeomorph μ hμ z₀).symm]
  rw [← (s34Homeomorph μ hμ z₀).image_eq_preimage_symm]
  exact (image_mono hφsupport).trans_eq (s34_image_spaceTimeSet μ hμ z₀ Ω I)

private theorem s34_tsupp_bridge {V : Type} [Zero V] (g : ParabolicPoint → V) :
    tsupport g = parabolicHomeomorph ⁻¹'
      (tsupport (fun q : Vec3 × ℝ => g q)) := by
  have hsupp : Function.support g = parabolicHomeomorph ⁻¹'
      (Function.support (fun q : Vec3 × ℝ => g q)) := by
    ext z
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

private theorem s34_scalar_zero
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ))
    (i : Fin 3) : spatialPartial ψ i z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [s34_tsupp_bridge]
    exact hmem
  have hzero := spatialPartial_zero_of_not_mem_tsupport_public hψ hq i
  change spatialPartial ψ i (z.1, z.2) = 0
  exact hzero

private theorem s34_time_zero
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
    timePartial ψ z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [s34_tsupp_bridge]
    exact hmem
  have hzero := timePartial_zero_of_not_mem_tsupport_public hψ hq
  change timePartial ψ (z.1, z.2) = 0
  exact hzero

private theorem s34_second_zero
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ))
    (i j : Fin 3) : spatialSecondPartial ψ i j z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [s34_tsupp_bridge]
    exact hmem
  have hzero := spatialSecondPartial_zero_of_not_mem_tsupport_public hψ hq i j
  change spatialSecondPartial ψ i j (z.1, z.2) = 0
  exact hzero

private theorem s34_component_contDiff
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z i) := by
  exact (contDiff_apply ℝ ℝ i).comp hφ

private theorem s34_source_support_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from φ)) :
    (-(∑ i, u z i * timePartial (fun w => φ w i) z))
      - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
      + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
      - p z * ∑ i, spatialPartial (fun w => φ w i) i z
      - ∑ i, f z i * φ z i = 0 := by
  have hφ0 : ∀ i : Fin 3, φ z i = 0 := by
    intro i
    by_contra hne
    apply hz
    apply subset_tsupport (show ParabolicPoint → Vec3 from φ)
    apply Function.mem_support.mpr
    intro hzero
    apply hne
    rw [hzero]
    rfl
  have hcomponent_not : ∀ i : Fin 3,
      z ∉ tsupport (show ParabolicPoint → ℝ from fun w => φ w i) := by
    intro i hmem
    apply hz
    change z ∈ closure (Function.support (show ParabolicPoint → ℝ from fun w => φ w i)) at hmem
    exact closure_mono
      (show Function.support (show ParabolicPoint → ℝ from fun w => φ w i) ⊆
        Function.support (show ParabolicPoint → Vec3 from φ) from by
          intro w hw
          change φ w i ≠ 0 at hw
          apply Function.mem_support.mpr
          intro hzero
          exact hw (congrFun hzero i)) hmem
  have ht : ∀ i : Fin 3, timePartial (fun w => φ w i) z = 0 := by
    intro i
    exact s34_time_zero (s34_component_contDiff hφ i) (hcomponent_not i)
  have hs : ∀ i j : Fin 3,
      spatialPartial (fun w => φ w i) j z = 0 := by
    intro i j
    exact s34_scalar_zero (s34_component_contDiff hφ i) (hcomponent_not i) j
  simp [hφ0, ht, hs]

theorem s3_rescale
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hS3 : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      IntegrableOn (fun z =>
          (-(∑ i, u z i * timePartial (fun w => φ w i) z))
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i) (tsupport φ) volume ∧
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i = 0)
    (z₀ : ParabolicPoint) {μ : ℝ} (hμ : 0 < μ) :
    ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) →
      IntegrableOn (fun z =>
          (-(∑ i, rescaleVelocity μ z₀ u z i * timePartial (fun w => φ w i) z))
            - ∑ i, ∑ j, rescaleVelocity μ z₀ u z i * rescaleVelocity μ z₀ u z j *
              spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, (rescaleGradient μ z₀ Du z i j) *
              spatialPartial (fun w => φ w i) j z
            - rescalePressure μ z₀ p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, rescaleForce μ z₀ f z i * φ z i) (tsupport φ) volume ∧
      ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I),
        (-(∑ i, rescaleVelocity μ z₀ u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, rescaleVelocity μ z₀ u z i * rescaleVelocity μ z₀ u z j *
              spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (rescaleGradient μ z₀ Du z i j) *
              spatialPartial (fun w => φ w i) j z
          - rescalePressure μ z₀ p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, rescaleForce μ z₀ f z i * φ z i = 0 := by
  intro φ hφ
  let φhat : Vec3 × ℝ → Vec3 := φ ∘ (s34Homeomorph μ hμ z₀).symm
  have hφhat : φhat ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
    exact s34_pullback_test μ hμ z₀ hφ
  obtain ⟨hsource, hzero⟩ := hS3 φhat hφhat
  have hsourceFull : Integrable (fun z =>
      (-(∑ i, u z i * timePartial (fun w => φhat w i) z))
        - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φhat w i) j z
        + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φhat w i) j z
        - p z * ∑ i, spatialPartial (fun w => φhat w i) i z
        - ∑ i, f z i * φhat z i) volume := by
    apply hsource.integrable_of_forall_notMem_eq_zero
    intro z hz
    exact s34_source_support_zero hφhat.1 hz
  let L : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, u z i * timePartial (fun w => φhat w i) z))
      - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φhat w i) j z
      + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φhat w i) j z
      - p z * ∑ i, spatialPartial (fun w => φhat w i) i z
      - ∑ i, f z i * φhat z i
  let Lμ : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, rescaleVelocity μ z₀ u z i * timePartial (fun w => φ w i) z))
      - ∑ i, ∑ j, rescaleVelocity μ z₀ u z i * rescaleVelocity μ z₀ u z j *
          spatialPartial (fun w => φ w i) j z
      + ∑ i, ∑ j, (rescaleGradient μ z₀ Du z i j) *
          spatialPartial (fun w => φ w i) j z
      - rescalePressure μ z₀ p z * ∑ i, spatialPartial (fun w => φ w i) i z
      - ∑ i, rescaleForce μ z₀ f z i * φ z i
  have hpoint : ∀ z, Lμ z = μ ^ 3 * L (scalingParabolic μ z₀ z) := by
    intro z
    have ht : ∀ i : Fin 3,
        timePartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i)
          (scalingParabolic μ z₀ z) =
          (μ ^ 2)⁻¹ * timePartial (fun w => φ w i) z := by
      intro i
      exact timePartial_pullback μ hμ z₀
        (s34_component_contDiff hφ.1 i) z
    have hs : ∀ i j : Fin 3,
        spatialPartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i) j
            (scalingParabolic μ z₀ z) =
          μ⁻¹ * spatialPartial (fun w => φ w i) j z := by
      intro i j
      exact spatialPartial_pullback μ hμ z₀
        (s34_component_contDiff hφ.1 i) j z
    dsimp [Lμ, L, φhat]
    rw [s34Inverse_eq μ hμ z₀]
    change (-(∑ i, (μ • u (scalingParabolic μ z₀ z)) i *
          timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, (μ • u (scalingParabolic μ z₀ z)) i *
            (μ • u (scalingParabolic μ z₀ z)) j * spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, ((μ ^ 2) • Du (scalingParabolic μ z₀ z) i) j *
            spatialPartial (fun w => φ w i) j z
        - (μ ^ 2 * p (scalingParabolic μ z₀ z)) *
            ∑ i, spatialPartial (fun w => φ w i) i z
        - ∑ i, (μ ^ 3 • f (scalingParabolic μ z₀ z)) i * φ z i =
      μ ^ 3 * ((-(∑ i, u (scalingParabolic μ z₀ z) i *
          timePartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
            (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i)
            (scalingParabolic μ z₀ z)))
        - ∑ i, ∑ j, u (scalingParabolic μ z₀ z) i *
            u (scalingParabolic μ z₀ z) j *
            spatialPartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
              (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i) j
              (scalingParabolic μ z₀ z)
        + ∑ i, ∑ j, Du (scalingParabolic μ z₀ z) i j *
            spatialPartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
              (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i) j
              (scalingParabolic μ z₀ z)
        - p (scalingParabolic μ z₀ z) *
            ∑ i, spatialPartial (fun w => (φ ∘ (fun v : Vec3 × ℝ =>
              (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w i) i
              (scalingParabolic μ z₀ z)
        - ∑ i, f (scalingParabolic μ z₀ z) i *
            (φ ∘ (fun v : Vec3 × ℝ =>
              (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2))))
              (scalingParabolic μ z₀ z) i)
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [ht, hs]
    have heval :
        (φ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2))))
            (scalingParabolic μ z₀ z) = φ z := by
      ext
      simp [scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
      rfl
    rw [heval]
    ring_nf
    simp only [Finset.mul_sum]
    field_simp [hμ.ne']
  have hcomp : IntegrableOn (L ∘ scalingParabolic μ z₀)
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    exact integrable_comp_scaling_test (Ω := Ω) (I := I) μ hμ z₀
      hΩ hI hsourceFull.integrableOn
  have htargetFull : IntegrableOn Lμ
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    have heq : Lμ = fun z => μ ^ 3 * (L ∘ scalingParabolic μ z₀) z := by
      funext z
      rw [hpoint]
      rfl
    rw [heq]
    change Integrable (fun z => μ ^ 3 * (L ∘ scalingParabolic μ z₀) z)
      (volume.restrict (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)))
    exact hcomp.const_mul (μ ^ 3)
  have hts : tsupport (show ParabolicPoint → Vec3 from φ) = tsupport φ := by
    rw [s34_tsupp_bridge, parabolicHomeomorph_preimage]
  have htargetSupport : tsupport (show ParabolicPoint → Vec3 from φ) ⊆
      spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) := by
    rw [hts]
    exact hφ.2.2
  have htargetOn := htargetFull.mono_set htargetSupport
  refine ⟨htargetOn, ?_⟩
  have hchange := integral_comp_scaling_test (Ω := Ω) (I := I)
    μ hμ z₀ hΩ hI hsourceFull.aestronglyMeasurable.restrict
  have hzero' : ∫ z in spaceTimeSet Ω I, L z = 0 := by
    exact hzero
  calc
    (∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), Lμ z) =
        ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I), μ ^ 3 * L (scalingParabolic μ z₀ z) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun z => hpoint z)
    _ = μ ^ 3 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), L (scalingParabolic μ z₀ z) := by
          rw [integral_const_mul]
    _ = μ ^ 3 * ((ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
        ∫ z in spaceTimeSet Ω I, L z) := by rw [hchange]
    _ = 0 := by rw [hzero']; simp

private theorem s34_energy_source_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
    spatialGradientSq u Du z * ψ z = 0 ∧
      (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
        + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψ i z
        + 2 * (∑ i, f z i * u z i) * ψ z = 0 := by
  have hψ0 : ψ z = 0 := by
    by_contra hne
    apply hz
    exact subset_tsupport (show ParabolicPoint → ℝ from ψ)
      (Function.mem_support.mpr hne)
  have ht : timePartial ψ z = 0 := s34_time_zero hψ hz
  have hs : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
    s34_scalar_zero hψ hz i
  have hss : ∀ i : Fin 3, spatialSecondPartial ψ i i z = 0 := fun i =>
    s34_second_zero hψ hz i i
  constructor
  · simp [hψ0]
  · simp [hψ0, ht, hs, hss]

theorem s4_rescale
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hS4 : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∀ z, 0 ≤ ψ z) →
      IntegrableOn (fun z => spatialGradientSq u Du z * ψ z)
          (tsupport ψ) volume ∧
      IntegrableOn (fun z =>
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)
          (tsupport ψ) volume ∧
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)
    (z₀ : ParabolicPoint) {μ : ℝ} (hμ : 0 < μ) :
    ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) →
      (∀ z, 0 ≤ ψ z) →
      IntegrableOn (fun z =>
          spatialGradientSq (rescaleVelocity μ z₀ u)
            (rescaleGradient μ z₀ Du) z * ψ z) (tsupport ψ) volume ∧
      IntegrableOn (fun z =>
          (vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 +
                2 * rescalePressure μ z₀ p z) *
                ∑ i, (rescaleVelocity μ z₀ u z i) * spatialPartial ψ i z
            + 2 * (∑ i, rescaleForce μ z₀ f z i *
                rescaleVelocity μ z₀ u z i) * ψ z)
          (tsupport ψ) volume ∧
      2 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I),
          spatialGradientSq (rescaleVelocity μ z₀ u)
            (rescaleGradient μ z₀ Du) z * ψ z ≤
        ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I),
          (vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 +
                2 * rescalePressure μ z₀ p z) *
                ∑ i, (rescaleVelocity μ z₀ u z i) * spatialPartial ψ i z
            + 2 * (∑ i, rescaleForce μ z₀ f z i *
                rescaleVelocity μ z₀ u z i) * ψ z := by
  intro ψ hψ hψnonneg
  let ψhat : Vec3 × ℝ → ℝ := ψ ∘ (s34Homeomorph μ hμ z₀).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
    exact s34_pullback_test μ hμ z₀ hψ
  have hψhatnonneg : ∀ z, 0 ≤ ψhat z := by
    intro z
    exact hψnonneg _
  obtain ⟨hDsource, hRsource, hineq⟩ := hS4 ψhat hψhat hψhatnonneg
  have hDfull : Integrable (fun z => spatialGradientSq u Du z * ψhat z) volume := by
    apply hDsource.integrable_of_forall_notMem_eq_zero
    intro z hz
    exact (s34_energy_source_zero (Du := Du) (p := p) (f := f) hψhat.1 hz).1
  have hRfull : Integrable (fun z =>
      (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
        + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψhat i z
        + 2 * (∑ i, f z i * u z i) * ψhat z) volume := by
    apply hRsource.integrable_of_forall_notMem_eq_zero
    intro z hz
    exact (s34_energy_source_zero (Du := Du) (p := p) (f := f) hψhat.1 hz).2
  let D : ParabolicPoint → ℝ := fun z => spatialGradientSq u Du z * ψhat z
  let R : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (u z)) ^ 2 *
        (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
      + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
          ∑ i, u z i * spatialPartial ψhat i z
      + 2 * (∑ i, f z i * u z i) * ψhat z
  let Dμ : ParabolicPoint → ℝ := fun z =>
    spatialGradientSq (rescaleVelocity μ z₀ u)
      (rescaleGradient μ z₀ Du) z * ψ z
  let Rμ : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
      + ((vec3EuclideanNorm (rescaleVelocity μ z₀ u z)) ^ 2 +
          2 * rescalePressure μ z₀ p z) *
          ∑ i, rescaleVelocity μ z₀ u z i * spatialPartial ψ i z
      + 2 * (∑ i, rescaleForce μ z₀ f z i *
          rescaleVelocity μ z₀ u z i) * ψ z
  have heval : ∀ z, ψhat (scalingParabolic μ z₀ z) = ψ z := by
    intro z
    dsimp [ψhat]
    rw [s34Inverse_eq μ hμ z₀]
    apply congrArg ψ
    apply Prod.ext
    · ext i
      simp [scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
    · simp [scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
  have hnorm : ∀ z,
      vec3EuclideanNorm (rescaleVelocity μ z₀ u z) =
        μ * vec3EuclideanNorm (u (scalingParabolic μ z₀ z)) := by
    intro z
    change vec3EuclideanNorm (μ • u (scalingParabolic μ z₀ z)) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos hμ]
  have hDpoint : ∀ z, Dμ z = μ ^ 4 * D (scalingParabolic μ z₀ z) := by
    intro z
    dsimp [Dμ, D, spatialGradientSq, rescaleGradient]
    rw [heval z]
    change (∑ i, ∑ j, (μ ^ 2 * Du (scalingParabolic μ z₀ z) i j) ^ 2) * ψ z =
      μ ^ 4 * ((∑ i, ∑ j, Du (scalingParabolic μ z₀ z) i j ^ 2) * ψ z)
    have hsum : ∀ i : Fin 3,
        (∑ j, (μ ^ 2 * Du (scalingParabolic μ z₀ z) i j) ^ 2) =
          μ ^ 4 * ∑ j, Du (scalingParabolic μ z₀ z) i j ^ 2 := by
      intro i
      calc
        (∑ j, (μ ^ 2 * Du (scalingParabolic μ z₀ z) i j) ^ 2) =
            ∑ j, μ ^ 4 * Du (scalingParabolic μ z₀ z) i j ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = μ ^ 4 * ∑ j, Du (scalingParabolic μ z₀ z) i j ^ 2 := by
              rw [← Finset.mul_sum]
    calc
      (∑ i, ∑ j, (μ ^ 2 * Du (scalingParabolic μ z₀ z) i j) ^ 2) * ψ z =
          (∑ i, μ ^ 4 * (∑ j, Du (scalingParabolic μ z₀ z) i j ^ 2)) * ψ z := by
            rw [show (∑ i, ∑ j,
                (μ ^ 2 * Du (scalingParabolic μ z₀ z) i j) ^ 2) =
                ∑ i, μ ^ 4 * (∑ j,
                  Du (scalingParabolic μ z₀ z) i j ^ 2) by
              apply Finset.sum_congr rfl
              intro i hi
              exact hsum i]
      _ = μ ^ 4 * ((∑ i, ∑ j, Du (scalingParabolic μ z₀ z) i j ^ 2) * ψ z) := by
            rw [← Finset.mul_sum]
            ring
  have hRpoint : ∀ z, Rμ z = μ ^ 4 * R (scalingParabolic μ z₀ z) := by
    intro z
    have ht :
        timePartial (fun w => (ψ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w)
          (scalingParabolic μ z₀ z) =
          (μ ^ 2)⁻¹ * timePartial ψ z := by
      exact timePartial_pullback μ hμ z₀ hψ.1 z
    have hs : ∀ i : Fin 3,
        spatialPartial (fun w => (ψ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w) i
            (scalingParabolic μ z₀ z) =
          μ⁻¹ * spatialPartial ψ i z := by
      intro i
      exact spatialPartial_pullback μ hμ z₀ hψ.1 i z
    have hss : ∀ i : Fin 3,
        spatialSecondPartial
            (fun w => (ψ ∘ (fun v : Vec3 × ℝ =>
              (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2)))) w) i i
              (scalingParabolic μ z₀ z) =
          (μ ^ 2)⁻¹ * spatialSecondPartial ψ i i z := by
      intro i
      exact spatialSecondPartial_pullback μ hμ z₀ hψ.1 i i z
    have heval' :
        (ψ ∘ (fun v : Vec3 × ℝ =>
          (μ⁻¹ • (v.1 - z₀.1), (μ ^ 2)⁻¹ * (v.2 - z₀.2))))
            (scalingParabolic μ z₀ z) = ψ z := by
      apply congrArg ψ
      apply Prod.ext
      · ext i
        simp [scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
      · simp [scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
    dsimp [Rμ, R, ψhat]
    rw [s34Inverse_eq μ hμ z₀]
    rw [hnorm z, ht]
    simp_rw [hs]
    simp_rw [hss]
    rw [heval']
    simp [rescaleVelocity, rescalePressure, rescaleForce,
      Pi.smul_apply, smul_eq_mul]
    simp only [scalingParabolic]
    have hforce :
        (2 * ∑ i, μ ^ 3 * f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            (μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i)) * ψ z =
          2 * ∑ i, μ ^ 4 * ψ z *
            f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i := by
      calc
        (2 * ∑ i, μ ^ 3 * f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            (μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i)) * ψ z =
            2 * ((∑ i, μ ^ 3 * f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              (μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i)) * ψ z) := by ring
        _ = 2 * ∑ i, (μ ^ 3 * f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              (μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i)) * ψ z := by
              rw [Finset.sum_mul]
        _ = 2 * ∑ i, μ ^ 4 * ψ z *
            f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i := by
              apply congrArg (fun w => 2 * w)
              apply Finset.sum_congr rfl
              intro i hi
              ring
    rw [hforce]
    ring_nf
    have hsp :
        (∑ i, μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z) =
          μ * ∑ i, u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z := by
      calc
        (∑ i, μ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z) =
            ∑ i, μ * (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              spatialPartial ψ i z) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = μ * ∑ i, u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z := by rw [Finset.mul_sum]
    have hspInv :
        (∑ i, μ⁻¹ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z) =
          μ⁻¹ * ∑ i, u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z := by
      calc
        (∑ i, μ⁻¹ * u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z) =
            ∑ i, μ⁻¹ * (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              spatialPartial ψ i z) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = μ⁻¹ * ∑ i, u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            spatialPartial ψ i z := by rw [Finset.mul_sum]
    have hssInv :
        (∑ i, μ⁻¹ ^ 2 * spatialSecondPartial ψ i i z) =
          μ⁻¹ ^ 2 * ∑ i, spatialSecondPartial ψ i i z := by
      rw [Finset.mul_sum]
    have hforce2 :
        (∑ i, μ ^ 4 * ψ z *
            f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i) =
          μ ^ 4 * ψ z *
            ∑ i, f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i := by
      calc
        (∑ i, μ ^ 4 * ψ z *
            f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
            u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i) =
            ∑ i, (μ ^ 4 * ψ z) *
              (f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
                u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
        _ = μ ^ 4 * ψ z *
            ∑ i, f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i *
              u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) i := by
                rw [Finset.mul_sum]
    rw [hsp, hspInv, hssInv]
    rw [hforce2]
    field_simp [hμ.ne']
  have hDcomp : IntegrableOn (D ∘ scalingParabolic μ z₀)
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    exact integrable_comp_scaling_test (Ω := Ω) (I := I) μ hμ z₀
      hΩ hI hDfull.integrableOn
  have hRcomp : IntegrableOn (R ∘ scalingParabolic μ z₀)
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    exact integrable_comp_scaling_test (Ω := Ω) (I := I) μ hμ z₀
      hΩ hI hRfull.integrableOn
  have hDtargetFull : IntegrableOn Dμ
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    have heq : Dμ = fun z => μ ^ 4 * (D ∘ scalingParabolic μ z₀) z := by
      funext z
      rw [hDpoint]
      rfl
    rw [heq]
    change Integrable (fun z => μ ^ 4 * (D ∘ scalingParabolic μ z₀) z)
      (volume.restrict (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)))
    exact hDcomp.const_mul (μ ^ 4)
  have hRtargetFull : IntegrableOn Rμ
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
    have heq : Rμ = fun z => μ ^ 4 * (R ∘ scalingParabolic μ z₀) z := by
      funext z
      rw [hRpoint]
      rfl
    rw [heq]
    change Integrable (fun z => μ ^ 4 * (R ∘ scalingParabolic μ z₀) z)
      (volume.restrict (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)))
    exact hRcomp.const_mul (μ ^ 4)
  have hts : tsupport (show ParabolicPoint → ℝ from ψ) = tsupport ψ := by
    rw [s34_tsupp_bridge, parabolicHomeomorph_preimage]
  have htargetSupport : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) := by
    rw [hts]
    exact hψ.2.2
  have hDtargetOn := hDtargetFull.mono_set htargetSupport
  have hRtargetOn := hRtargetFull.mono_set htargetSupport
  refine ⟨hDtargetOn,
    hRtargetOn, ?_⟩
  have hDchange := integral_comp_scaling_test (Ω := Ω) (I := I)
    μ hμ z₀ hΩ hI hDfull.aestronglyMeasurable.restrict
  have hRchange := integral_comp_scaling_test (Ω := Ω) (I := I)
    μ hμ z₀ hΩ hI hRfull.aestronglyMeasurable.restrict
  have hDchange' :
      (∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I), (D ∘ scalingParabolic μ z₀) z) =
        (ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
          ∫ z in spaceTimeSet Ω I, D z := by
    exact hDchange
  have hRchange' :
      (∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I), (R ∘ scalingParabolic μ z₀) z) =
        (ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
          ∫ z in spaceTimeSet Ω I, R z := by
    exact hRchange
  have hineq' : 2 * ∫ z in spaceTimeSet Ω I, D z ≤
      ∫ z in spaceTimeSet Ω I, R z := by
    exact hineq
  have hcoef : 0 ≤ μ ^ 4 * (ENNReal.ofReal (μ⁻¹ ^ 5)).toReal := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hineq' hcoef
  calc
    2 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), Dμ z =
        μ ^ 4 * (2 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I), (D ∘ scalingParabolic μ z₀) z) := by
            rw [integral_congr_ae (Eventually.of_forall (fun z => hDpoint z))]
            rw [integral_const_mul]
            simp only [Function.comp_apply]
            ring
    _ = μ ^ 4 * (2 * ((ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
          ∫ z in spaceTimeSet Ω I, D z)) := by
            rw [hDchange']
    _ ≤ μ ^ 4 * ((ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
          ∫ z in spaceTimeSet Ω I, R z) := by
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), Rμ z := by
            rw [integral_congr_ae (Eventually.of_forall (fun z => hRpoint z))]
            rw [integral_const_mul, ← hRchange']
            simp only [Function.comp_apply]

end CKN
