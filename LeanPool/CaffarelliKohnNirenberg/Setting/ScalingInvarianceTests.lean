/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling

/-!
# Scaling Invariance Tests

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

def testSpatialHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

private theorem testSpatialInverse_eq (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    ⇑(testSpatialHomeomorph μ hμ x₀).symm =
      (fun y : Vec3 => μ⁻¹ • (y - x₀)) := by
  funext z
  ext k
  simp [testSpatialHomeomorph, Homeomorph.trans, Homeomorph.smulOfNeZero,
    Homeomorph.addLeft, Units.smul_def]
  field_simp [hμ.ne']
  ring

private theorem testSpatialInverse_deriv (μ : ℝ) (_ : 0 < μ) (x₀ y : Vec3) :
    fderiv ℝ (fun y : Vec3 => μ⁻¹ • (y - x₀)) y =
      μ⁻¹ • ContinuousLinearMap.id ℝ Vec3 := by
  change fderiv ℝ (μ⁻¹ • (fun y : Vec3 => y - x₀)) y = _
  rw [fderiv_const_smul, fderiv_sub_const]
  rw [show (fun y : Vec3 => y) = id from rfl, fderiv_id]
  simp

private theorem testSpatialDerivative (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 3) (x : Vec3) :
    (fderiv ℝ (φ ∘ (testSpatialHomeomorph μ hμ x₀).symm)
      (scalingSpace μ x₀ x)) (basisVec j) =
      μ⁻¹ * (fderiv ℝ φ x) (basisVec j) := by
  have hinv := testSpatialInverse_eq μ hμ x₀
  rw [hinv, fderiv_comp]
  · rw [testSpatialInverse_deriv μ hμ]
    have hpoint : μ⁻¹ • (scalingSpace μ x₀ x - x₀) = x := by
      simp [scalingSpace, smul_smul, hμ.ne']
    rw [hpoint]
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [map_smul]
    simp [smul_eq_mul]
  · exact hφ.differentiable (by simp) _
  · fun_prop

theorem spatialPartial_pullback
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (ψ ∘ (fun w =>
      (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) j
        (scalingParabolic μ z₀ z) =
      μ⁻¹ * spatialPartial ψ j z := by
  change (fderiv ℝ (fun x : Vec3 =>
      ψ ((fun w => (μ⁻¹ • (w.1 - z₀.1),
        (μ ^ 2)⁻¹ * (w.2 - z₀.2))) (x, (scalingParabolic μ z₀ z).2)))
      (scalingParabolic μ z₀ z).1) (basisVec j) = _
  have htime : (scalingParabolic μ z₀ z).2 = scalingTime μ z₀.2 z.2 := by
    rfl
  rw [htime]
  have hfun : (fun x : Vec3 =>
      ψ ((fun w => (μ⁻¹ • (w.1 - z₀.1),
        (μ ^ 2)⁻¹ * (w.2 - z₀.2))) (x, scalingTime μ z₀.2 z.2))) =
      (fun x : Vec3 => ψ (μ⁻¹ • (x - z₀.1), z.2)) := by
    funext x
    congr 1
    simp [scalingTime, hμ.ne']
  rw [hfun]
  have hspace : (scalingParabolic μ z₀ z).1 = scalingSpace μ z₀.1 z.1 := by
    rfl
  rw [hspace]
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) := by
    exact hψ.comp (contDiff_id.prodMk contDiff_const)
  have hinv : (fun x : Vec3 => ψ (μ⁻¹ • (x - z₀.1), z.2)) =
      (fun x : Vec3 => (fun y : Vec3 => ψ (y, z.2))
        (μ⁻¹ • (x - z₀.1))) := by rfl
  rw [hinv]
  change (fderiv ℝ ((fun y : Vec3 => ψ (y, z.2)) ∘
      (fun x : Vec3 => μ⁻¹ • (x - z₀.1)))
      (scalingSpace μ z₀.1 z.1)) (basisVec j) = _
  rw [fderiv_comp]
  · rw [testSpatialInverse_deriv μ hμ]
    have hpoint : μ⁻¹ • (scalingSpace μ z₀.1 z.1 - z₀.1) = z.1 := by
      simp [scalingSpace, smul_smul, hμ.ne']
    rw [hpoint]
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [map_smul]
    simp [spatialPartial, smul_eq_mul]
  · exact hslice.differentiable (by simp) _
  · fun_prop

private theorem testTimeInverse_deriv (μ : ℝ) (_ : 0 < μ) (t₀ s : ℝ) :
    fderiv ℝ (fun s : ℝ => (μ ^ 2)⁻¹ * (s - t₀)) s =
      (μ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
  change fderiv ℝ ((μ ^ 2)⁻¹ • (fun s : ℝ => s - t₀)) s = _
  rw [fderiv_const_smul, fderiv_sub_const]
  rw [show (fun s : ℝ => s) = id from rfl, fderiv_id]
  simp

theorem timePartial_pullback
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : ParabolicPoint) :
    timePartial (ψ ∘ (fun w =>
      (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2))))
        (scalingParabolic μ z₀ z) =
      (μ ^ 2)⁻¹ * timePartial ψ z := by
  change (fderiv ℝ (fun s : ℝ =>
      ψ ((fun w => (μ⁻¹ • (w.1 - z₀.1),
        (μ ^ 2)⁻¹ * (w.2 - z₀.2)))
        ((scalingParabolic μ z₀ z).1, s)))
      (scalingParabolic μ z₀ z).2) 1 = _
  have hspace : (scalingParabolic μ z₀ z).1 = scalingSpace μ z₀.1 z.1 := by
    rfl
  rw [hspace]
  have htime : (scalingParabolic μ z₀ z).2 = scalingTime μ z₀.2 z.2 := by
    rfl
  rw [htime]
  have hfun : (fun s : ℝ =>
      ψ ((fun w => (μ⁻¹ • (w.1 - z₀.1),
        (μ ^ 2)⁻¹ * (w.2 - z₀.2))) (scalingSpace μ z₀.1 z.1, s))) =
      (fun s : ℝ => ψ (z.1, (μ ^ 2)⁻¹ * (s - z₀.2))) := by
    funext s
    congr 1
    simp [scalingSpace, hμ.ne']
  rw [hfun]
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ψ (z.1, s)) := by
    exact hψ.comp (contDiff_const.prodMk contDiff_id)
  change (fderiv ℝ ((fun t : ℝ => ψ (z.1, t)) ∘
      (fun s : ℝ => (μ ^ 2)⁻¹ * (s - z₀.2)))
      (scalingTime μ z₀.2 z.2)) 1 = _
  rw [fderiv_comp]
  · rw [testTimeInverse_deriv μ hμ]
    have hpoint : (μ ^ 2)⁻¹ * (scalingTime μ z₀.2 z.2 - z₀.2) = z.2 := by
      simp [scalingTime, hμ.ne']
    rw [hpoint]
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [map_smul]
    change (μ ^ 2)⁻¹ *
        (fderiv ℝ (fun t : ℝ => ψ (z.1, t)) z.2) 1 =
      (μ ^ 2)⁻¹ * timePartial ψ z
    congr 1
  · exact hslice.differentiable (by simp) _
  · fun_prop

theorem spatialSecondPartial_pullback
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : ParabolicPoint) :
    spatialSecondPartial
        (ψ ∘ (fun w =>
          (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) i j
        (scalingParabolic μ z₀ z) =
      (μ ^ 2)⁻¹ * spatialSecondPartial ψ i j z := by
  change (fderiv ℝ (fun x : Vec3 =>
      spatialPartial (ψ ∘ (fun w =>
        (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) i
        (x, (scalingParabolic μ z₀ z).2))
      (scalingParabolic μ z₀ z).1) (basisVec j) = _
  have htime : (scalingParabolic μ z₀ z).2 = scalingTime μ z₀.2 z.2 := by
    rfl
  rw [htime]
  have hfun : (fun x : Vec3 =>
      spatialPartial (ψ ∘ (fun w =>
        (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2)))) i
        (x, scalingTime μ z₀.2 z.2)) =
      (fun x : Vec3 => μ⁻¹ * spatialPartial ψ i
        (μ⁻¹ • (x - z₀.1), z.2)) := by
    funext x
    have h := spatialPartial_pullback μ hμ z₀ hψ i
      (μ⁻¹ • (x - z₀.1), z.2)
    simpa [scalingParabolic, scalingSpace, scalingTime, parabolicTranslate,
      parabolicScale, hμ.ne'] using h
  rw [hfun]
  have hslice : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => spatialPartial ψ i (x, z.2)) := by
    exact (spatialPartial_contDiff hψ i).comp
      (contDiff_id.prodMk contDiff_const)
  have hderiv := testSpatialDerivative μ hμ z₀.1 hslice j z.1
  rw [testSpatialInverse_eq μ hμ z₀.1] at hderiv
  have hderiv' : (fderiv ℝ (fun x : Vec3 =>
      spatialPartial ψ i (μ⁻¹ • (x - z₀.1), z.2))
      (scalingSpace μ z₀.1 z.1)) (basisVec j) =
      μ⁻¹ * (fderiv ℝ (fun x : Vec3 => spatialPartial ψ i (x, z.2)) z.1)
        (basisVec j) := by
    simpa [Function.comp_def] using hderiv
  have hspace : (scalingParabolic μ z₀ z).1 = scalingSpace μ z₀.1 z.1 := by
    rfl
  rw [hspace]
  rw [show (fun x : Vec3 => μ⁻¹ * spatialPartial ψ i
      (μ⁻¹ • (x - z₀.1), z.2)) =
      μ⁻¹ • (fun x : Vec3 => spatialPartial ψ i
        (μ⁻¹ • (x - z₀.1), z.2)) by
      funext x
      simp [smul_eq_mul]]
  rw [fderiv_const_smul]
  · simp only [_root_.smul_apply]
    rw [hderiv']
    change μ⁻¹ * (μ⁻¹ *
      (fderiv ℝ (fun x : Vec3 => spatialPartial ψ i (x, z.2)) z.1)
        (basisVec j)) =
      (μ ^ 2)⁻¹ *
        (fderiv ℝ (fun x : Vec3 =>
          spatialPartial (show ParabolicPoint → ℝ from ψ) i (x, z.2)) z.1)
          (basisVec j)
    ring
  · have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
        spatialPartial ψ i (μ⁻¹ • (x - z₀.1), z.2)) := by
      exact hslice.comp (by fun_prop)
    exact hcomp.differentiable (by simp) _

theorem integral_comp_scaling_test
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet Ω I))) :
    ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), F (scalingParabolic μ z₀ z) =
      (ENNReal.ofReal (μ⁻¹ ^ 5)).toReal •
        ∫ z in spaceTimeSet Ω I, F z := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hFmap : AEStronglyMeasurable F
      (Measure.map (scalingParabolic μ z₀)
        (volume.restrict
          (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
            (rescaledTime μ z₀.2 I)))) := by
    rw [hmap]
    exact hF.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 5))
  have hmeas : AEMeasurable (scalingParabolic μ z₀)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I))) := by
    rw [scalingParabolic_eq]
    have hs : Measurable (scalingSpace μ z₀.1) := by
      exact (measurable_const_add z₀.1).comp (measurable_const_smul μ)
    have ht : Measurable (scalingTime μ z₀.2) := by
      exact (measurable_const_add z₀.2).comp
        (measurable_const_mul (μ ^ 2))
    exact ((hs.comp measurable_fst).prodMk (ht.comp measurable_snd)).aemeasurable
  have hcomp := integral_map hmeas hFmap
  rw [hmap, integral_smul_measure] at hcomp
  simpa [Function.comp_def] using hcomp.symm

theorem integrable_comp_scaling_test
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hF : IntegrableOn F (spaceTimeSet Ω I) volume) :
    IntegrableOn (F ∘ scalingParabolic μ z₀)
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I)) volume := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hs := hF.smul_measure (c := ENNReal.ofReal (μ⁻¹ ^ 5))
    ENNReal.ofReal_ne_top
  rw [← hmap] at hs
  have hmeas : Measurable (scalingParabolic μ z₀) := by
    rw [scalingParabolic_eq]
    have hs : Measurable (scalingSpace μ z₀.1) := by
      exact (measurable_const_add z₀.1).comp (measurable_const_smul μ)
    have ht : Measurable (scalingTime μ z₀.2) := by
      exact (measurable_const_add z₀.2).comp
        (measurable_const_mul (μ ^ 2))
    exact (hs.comp measurable_fst).prodMk (ht.comp measurable_snd)
  exact hs.comp_measurable hmeas

private lemma spatialPartial_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartial ψ i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => ψ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma timePartial_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartial ψ z = 0 := by
  change (fderiv ℝ (fun s : ℝ => ψ (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => ψ (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma spatialSecondPartial_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i j : Fin 3) :
    spatialSecondPartial ψ i j z = 0 := by
  change spatialPartial (fun w => spatialPartial ψ i w) j z = 0
  change (fderiv ℝ (fun x : Vec3 => spatialPartial ψ i (x, z.2)) z.1)
      (basisVec j) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hzero :
      (fun w : Vec3 × ℝ => spatialPartial ψ i w) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen] with w hw
    exact spatialPartial_zero_of_not_mem_tsupport hψ hw i
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev :
      (fun x : Vec3 => spatialPartial ψ i (x, z.2)) =ᶠ[𝓝 z.1]
        (fun _ => (0 : ℝ)) := hmap.continuousAt.preimage_mem_nhds hzero
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

theorem spatialPartial_zero_of_not_mem_tsupport_public
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartial ψ i z = 0 :=
  spatialPartial_zero_of_not_mem_tsupport hψ hz i

theorem timePartial_zero_of_not_mem_tsupport_public
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) : timePartial ψ z = 0 :=
  timePartial_zero_of_not_mem_tsupport hψ hz

theorem spatialSecondPartial_zero_of_not_mem_tsupport_public
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i j : Fin 3) :
    spatialSecondPartial ψ i j z = 0 :=
  spatialSecondPartial_zero_of_not_mem_tsupport hψ hz i j

end CKN
