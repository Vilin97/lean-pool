/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Scaling Invariance Weak

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

def weakSpatialHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

private theorem weakSpatialHomeomorph_eq (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    ⇑(weakSpatialHomeomorph μ hμ x₀) = scalingSpace μ x₀ := by
  funext x
  rfl

private theorem weakSpatialInverse_deriv (μ : ℝ) (_ : 0 < μ) (x₀ y : Vec3) :
    fderiv ℝ (fun y : Vec3 => μ⁻¹ • (y - x₀)) y =
      μ⁻¹ • ContinuousLinearMap.id ℝ Vec3 := by
  change fderiv ℝ (μ⁻¹ • (fun y : Vec3 => y - x₀)) y = _
  rw [fderiv_const_smul, fderiv_sub_const]
  rw [show (fun y : Vec3 => y) = id from rfl, fderiv_id]
  simp

private theorem weakSpatialInverse_eq (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    ⇑(weakSpatialHomeomorph μ hμ x₀).symm =
      (fun y : Vec3 => μ⁻¹ • (y - x₀)) := by
  funext z
  ext k
  simp [weakSpatialHomeomorph, Homeomorph.trans, Homeomorph.smulOfNeZero,
    Homeomorph.addLeft, Units.smul_def]
  field_simp [hμ.ne']
  ring

private theorem integral_comp_scaling_space
    (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3)
    {Ω Ω' : Set Vec3} (hΩ : MeasurableSet Ω)
    {F : Vec3 → ℝ} (hF : AEStronglyMeasurable F (volume.restrict Ω))
    (hΩeq : Ω = scalingSpace μ x₀ '' Ω') :
    ∫ x in Ω', F (scalingSpace μ x₀ x) =
      (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal • ∫ x in Ω, F x := by
  have hmap := map_scalingSpace_restrict hμ x₀
    (Ω := Ω) hΩ
  have hres : rescaledSpace μ x₀ Ω = Ω' := by
    rw [rescaledSpace, hΩeq]
    rw [← weakSpatialHomeomorph_eq μ hμ x₀]
    exact (weakSpatialHomeomorph μ hμ x₀).preimage_image Ω'
  have hmap' : Measure.map (scalingSpace μ x₀) (volume.restrict Ω') =
      ENNReal.ofReal (μ⁻¹ ^ 3) • volume.restrict Ω := by
    rw [← hres]
    exact hmap
  have hFmap : AEStronglyMeasurable F
      (Measure.map (scalingSpace μ x₀) (volume.restrict Ω')) := by
    rw [hmap']
    exact hF.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 3))
  have hscale : AEMeasurable (scalingSpace μ x₀)
      (volume.restrict Ω') := by
      rw [← weakSpatialHomeomorph_eq μ hμ x₀]
      exact (weakSpatialHomeomorph μ hμ x₀).measurable.aemeasurable
  have hcomp := integral_map (φ := scalingSpace μ x₀) hscale hFmap
  rw [hmap', integral_smul_measure] at hcomp
  simpa [Function.comp_def] using hcomp.symm

private theorem weakDerivative_test_deriv
    (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 3) (x : Vec3) :
    (fderiv ℝ (φ ∘ (weakSpatialHomeomorph μ hμ x₀).symm)
      (scalingSpace μ x₀ x)) (basisVec j) =
      μ⁻¹ * (fderiv ℝ φ x) (basisVec j) := by
  have hinv := weakSpatialInverse_eq μ hμ x₀
  rw [hinv, fderiv_comp]
  · rw [weakSpatialInverse_deriv μ hμ]
    have hpoint : μ⁻¹ • (scalingSpace μ x₀ x - x₀) = x := by
      simp [scalingSpace, smul_smul, hμ.ne']
    rw [hpoint]
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [map_smul]
    simp [smul_eq_mul]
  · exact hφ.differentiable (by simp) _
  · fun_prop

theorem hasWeakPartialDerivOn_scaling
    (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3)
    {Ω Ω' : Set Vec3} (hΩ : MeasurableSet Ω)
    {g dg : Vec3 → ℝ} (j : Fin 3)
    (hΩeq : Ω = scalingSpace μ x₀ '' Ω')
    (hweak : HasWeakPartialDerivOn Ω j g dg)
    (hg : AEStronglyMeasurable g (volume.restrict Ω))
    (hdg : AEStronglyMeasurable dg (volume.restrict Ω)) :
    HasWeakPartialDerivOn Ω' j
      (fun x => μ * g (scalingSpace μ x₀ x))
      (fun x => μ ^ 2 * dg (scalingSpace μ x₀ x)) := by
  intro φ hφ hφcompact hφsupport
  let φhat : Vec3 → ℝ :=
    φ ∘ (weakSpatialHomeomorph μ hμ x₀).symm
  have hφhat : ContDiff ℝ (⊤ : ℕ∞) φhat :=
    hφ.comp (by
      change ContDiff ℝ (⊤ : ℕ∞) (weakSpatialHomeomorph μ hμ x₀).symm
      rw [weakSpatialInverse_eq μ hμ x₀]
      fun_prop)
  have hφhatcompact : HasCompactSupport φhat :=
    hφcompact.comp_homeomorph (weakSpatialHomeomorph μ hμ x₀).symm
  have hφhatsupport : tsupport φhat ⊆ Ω := by
    rw [show φhat = φ ∘ (weakSpatialHomeomorph μ hμ x₀).symm from rfl,
      tsupport_comp_eq_preimage φ (weakSpatialHomeomorph μ hμ x₀).symm]
    rw [← (weakSpatialHomeomorph μ hμ x₀).image_eq_preimage_symm]
    rw [hΩeq]
    exact image_mono hφsupport
  have hsource := hweak φhat hφhat hφhatcompact hφhatsupport
  have hderiv : AEMeasurable
      (fun y => (fderiv ℝ φhat y) (basisVec j))
      (volume.restrict Ω) := by
    have hc := hφhat.continuous_fderiv (by simp)
    exact (hc.clm_apply continuous_const).measurable.aemeasurable
  have hA : AEStronglyMeasurable
      (fun y => g y * (fderiv ℝ φhat y) (basisVec j))
      (volume.restrict Ω) :=
    hg.mul hderiv.aestronglyMeasurable
  have hB : AEStronglyMeasurable
      (fun y => dg y * φhat y) (volume.restrict Ω) :=
    hdg.mul hφhat.continuous.aestronglyMeasurable
  have hchangeA := integral_comp_scaling_space μ hμ x₀ hΩ hA hΩeq
  have hchangeB := integral_comp_scaling_space μ hμ x₀ hΩ hB hΩeq
  have hApoint : ∀ x : Vec3,
      g (scalingSpace μ x₀ x) *
          (fderiv ℝ φhat (scalingSpace μ x₀ x)) (basisVec j) =
        μ⁻¹ * (g (scalingSpace μ x₀ x) *
          (fderiv ℝ φ x) (basisVec j)) := by
    intro x
    rw [weakDerivative_test_deriv μ hμ x₀ hφ j x]
    ring
  have hBpoint : ∀ x : Vec3,
      dg (scalingSpace μ x₀ x) * φhat (scalingSpace μ x₀ x) =
        dg (scalingSpace μ x₀ x) * φ x := by
    intro x
    have heval : φhat (scalingSpace μ x₀ x) = φ x := by
      dsimp [φhat]
      rw [← weakSpatialHomeomorph_eq μ hμ x₀]
      simp
    rw [heval]
  let A : ℝ := ∫ x in Ω',
    g (scalingSpace μ x₀ x) * (fderiv ℝ φ x) (basisVec j)
  let B : ℝ := ∫ x in Ω',
    dg (scalingSpace μ x₀ x) * φ x
  let SA : ℝ := ∫ x in Ω, g x * (fderiv ℝ φhat x) (basisVec j)
  let SB : ℝ := ∫ x in Ω, dg x * φhat x
  have hAchange : μ⁻¹ * A =
      (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal • SA := by
    calc
      μ⁻¹ * A =
          ∫ x in Ω', g (scalingSpace μ x₀ x) *
            (fderiv ℝ φhat (scalingSpace μ x₀ x)) (basisVec j) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun x => by
                exact (hApoint x).symm)
      _ = (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal • SA := by
        simpa [A, SA, Function.comp_def] using hchangeA
  have hBchange : B =
      (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal • SB := by
    calc
      B = ∫ x in Ω', dg (scalingSpace μ x₀ x) * φhat (scalingSpace μ x₀ x) := by
        change (∫ x in Ω', dg (scalingSpace μ x₀ x) * φ x) =
          ∫ x in Ω', dg (scalingSpace μ x₀ x) * φhat (scalingSpace μ x₀ x)
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (hBpoint x).symm)
      _ = (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal • SB := by
        simpa [B, SB, Function.comp_def] using hchangeB
  have hcoef : (ENNReal.ofReal (μ⁻¹ ^ 3)).toReal = μ⁻¹ ^ 3 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [hcoef] at hAchange hBchange
  have hA' : A = μ⁻¹ ^ 2 * SA := by
    calc
      A = μ * (μ⁻¹ * A) := by field_simp [hμ.ne']
      _ = μ * (μ⁻¹ ^ 3 * SA) := by
        simpa [smul_eq_mul] using congrArg (fun z => μ * z) hAchange
      _ = μ⁻¹ ^ 2 * SA := by field_simp [hμ.ne']
  have hB' : B = μ⁻¹ ^ 3 * SB := by
    simpa [smul_eq_mul] using hBchange
  have hgoal : μ * A = -(μ ^ 2 * B) := by
    have hs : SA = -SB := by
      simpa [SA, SB] using hsource
    rw [hA', hB', hs]
    field_simp [hμ.ne']
  have hleft :
      (∫ x in Ω', μ * g (scalingSpace μ x₀ x) *
        (fderiv ℝ φ x) (basisVec j)) = μ * A := by
    rw [show (fun x => μ * g (scalingSpace μ x₀ x) *
        (fderiv ℝ φ x) (basisVec j)) =
        (fun x => μ * (g (scalingSpace μ x₀ x) *
          (fderiv ℝ φ x) (basisVec j))) by
      funext x
      ring, integral_const_mul]
  have hright :
      (∫ x in Ω', μ ^ 2 * dg (scalingSpace μ x₀ x) * φ x) = μ ^ 2 * B := by
    rw [show (fun x => μ ^ 2 * dg (scalingSpace μ x₀ x) * φ x) =
        (fun x => μ ^ 2 * (dg (scalingSpace μ x₀ x) * φ x)) by
      funext x
      ring, integral_const_mul]
  rw [hleft, hright]
  exact hgoal

end CKN
