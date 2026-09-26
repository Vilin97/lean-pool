/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceWeak
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS2
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceS3S4
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling

/-!
# Scaling Invariance

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- Space-time homeomorphism implementing positive parabolic scaling and translation. -/
def scalingHomeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
      (Homeomorph.addLeft z₀.2))

private theorem scalingHomeomorph_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(scalingHomeomorph μ hμ z₀) = scalingParabolic μ z₀ := by
  funext z
  rfl

private theorem scalingHomeomorph_measurable (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) : Measurable (scalingParabolic μ z₀) := by
  rw [← scalingHomeomorph_eq μ hμ z₀]
  exact (scalingHomeomorph μ hμ z₀).measurable

/-- Spatial dilation and translation as a homeomorphism. -/
def spatialHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

private theorem spatialHomeomorph_eq (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    ⇑(spatialHomeomorph μ hμ x₀) = scalingSpace μ x₀ := by
  funext x
  rfl

/-- Quadratic time dilation and translation as a homeomorphism. -/
def temporalHomeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    ℝ ≃ₜ ℝ :=
  (Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
    (Homeomorph.addLeft t₀)

private theorem temporalHomeomorph_eq (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    ⇑(temporalHomeomorph μ hμ t₀) = scalingTime μ t₀ := by
  funext s
  rfl

private theorem rescaledSpace_image_eq (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3)
    (s : Set Vec3) :
    rescaledSpace μ x₀ (scalingSpace μ x₀ '' s) = s := by
  rw [rescaledSpace, ← spatialHomeomorph_eq μ hμ x₀]
  exact (spatialHomeomorph μ hμ x₀).preimage_image s

private theorem rescaledTime_image_eq (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ)
    (s : Set ℝ) :
    rescaledTime μ t₀ (scalingTime μ t₀ '' s) = s := by
  rw [rescaledTime, ← temporalHomeomorph_eq μ hμ t₀]
  exact (temporalHomeomorph μ hμ t₀).preimage_image s

private theorem memLp_comp_scaling
    {E : Type} [TopologicalSpace E] [ContinuousENorm E]
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {g : ParabolicPoint → E} {p : ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hg : MemLp g p (volume.restrict (spaceTimeSet Ω I))) :
    MemLp (g ∘ scalingParabolic μ z₀) p
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hs := hg.smul_measure (c := ENNReal.ofReal (μ⁻¹ ^ 5)) ENNReal.ofReal_ne_top
  rw [← hmap] at hs
  exact hs.comp_of_map (scalingHomeomorph_measurable μ hμ z₀).aemeasurable

private theorem aestronglyMeasurable_comp_scaling
    {E : Type} [TopologicalSpace E]
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {g : ParabolicPoint → E}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hg : AEStronglyMeasurable g (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (g ∘ scalingParabolic μ z₀)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hs := hg.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 5))
  rw [← hmap] at hs
  exact hs.comp_measurable (scalingHomeomorph_measurable μ hμ z₀)

private theorem aemeasurable_comp_scaling
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {g : ParabolicPoint → ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hg : AEMeasurable g (volume.restrict (spaceTimeSet Ω I))) :
    AEMeasurable (g ∘ scalingParabolic μ z₀)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hs := hg.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 5))
  rw [← hmap] at hs
  exact hs.comp_measurable (scalingHomeomorph_measurable μ hμ z₀)

private theorem lintegral_comp_scaling
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hF : AEMeasurable F (volume.restrict (spaceTimeSet Ω I))) :
    ∫⁻ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), F (scalingParabolic μ z₀ z) =
      ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z in spaceTimeSet Ω I, F z := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hFmap : AEMeasurable F
      (Measure.map (scalingParabolic μ z₀)
        (volume.restrict
          (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)))) := by
    rw [hmap]
    exact hF.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 5))
  have hcomp := lintegral_map' hFmap
    (scalingHomeomorph_measurable μ hμ z₀).aemeasurable
  rw [hmap, lintegral_smul_measure] at hcomp
  simpa [Function.comp_def, smul_eq_mul] using hcomp.symm

private theorem lintegral_comp_scaling_space
    (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3)
    {Ω : Set Vec3} {F : Vec3 → ℝ≥0∞} (hΩ : MeasurableSet Ω)
    (hF : AEMeasurable F (volume.restrict Ω)) :
    ∫⁻ x in rescaledSpace μ x₀ Ω, F (scalingSpace μ x₀ x) =
      ENNReal.ofReal (μ⁻¹ ^ 3) * ∫⁻ x in Ω, F x := by
  have hmap := map_scalingSpace_restrict hμ x₀ hΩ
  have hFmap : AEMeasurable F
      (Measure.map (scalingSpace μ x₀) (volume.restrict (rescaledSpace μ x₀ Ω))) := by
    rw [hmap]
    exact hF.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 3))
  have hcomp := lintegral_map' hFmap
    (measurable_const_add x₀ |>.comp (measurable_const_smul μ)).aemeasurable
  rw [hmap, lintegral_smul_measure] at hcomp
  simpa [Function.comp_def, scalingSpace, smul_eq_mul] using hcomp.symm

private theorem ae_slice_aemeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {F : α × β → E}
    (hF : AEMeasurable F (μ.prod ν)) :
    ∀ᵐ s ∂ν, AEMeasurable (fun x => F (x, s)) μ := by
  let Fs : β × α → E := fun z => F z.swap
  have hFs : AEMeasurable Fs (ν.prod μ) := by
    simpa [Fs] using hF.prod_swap
  let G : β × α → E := AEMeasurable.mk Fs hFs
  have hG : Measurable G := hFs.measurable_mk
  have heq : ∀ᵐ s ∂ν, Function.curry Fs s =ᵐ[μ] Function.curry G s :=
    Measure.ae_ae_eq_curry_of_prod hFs.ae_eq_mk
  filter_upwards [heq] with s hs
  have hGs : AEMeasurable (fun x => G (s, x)) μ :=
    (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable
  apply hGs.congr
  exact hs.symm

private theorem ae_slice_aestronglyMeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {F : α × β → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) :
    ∀ᵐ s ∂ν, AEStronglyMeasurable (fun x => F (x, s)) μ := by
  let Fs : β × α → E := fun z => F z.swap
  have hFs : AEStronglyMeasurable Fs (ν.prod μ) := by
    simpa [Fs] using hF.prod_swap
  let G : β × α → E := AEStronglyMeasurable.mk Fs hFs
  have hG : StronglyMeasurable G := hFs.stronglyMeasurable_mk
  have heq : ∀ᵐ s ∂ν, Function.curry Fs s =ᵐ[μ] Function.curry G s :=
    Measure.ae_ae_eq_curry_of_prod hFs.ae_eq_mk
  filter_upwards [heq] with s hs
  have hGs : StronglyMeasurable (fun x => G (s, x)) := by
    simpa [Function.comp_def] using
      hG.comp_measurable (measurable_const.prodMk measurable_id)
  apply hGs.aestronglyMeasurable.congr
  exact hs.symm

private theorem rescaled_energy_pointwise
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    ‖rescaleVelocity μ z₀ u z‖ₑ ^ (2 : ℝ) +
        ‖rescaleGradient μ z₀ Du z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (μ ^ 2) *
          (‖u (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ)) +
        ENNReal.ofReal (μ ^ 4) *
          (‖Du (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ)) := by
  change ‖μ • u (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ) +
      ‖μ ^ 2 • Du (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ) = _
  rw [enorm_smul, enorm_smul]
  rw [← ofReal_norm μ, ← ofReal_norm (μ ^ 2)]
  rw [Real.norm_eq_abs, abs_of_pos hμ]
  rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hμ)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.ofReal_rpow_of_nonneg hμ.le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (sq_pos_of_pos hμ).le (by norm_num)]
  norm_num
  have hcoef : ENNReal.ofReal ((μ ^ 2) ^ 2) = ENNReal.ofReal (μ ^ 4) := by
    congr 1
    ring
  rw [hcoef]

private theorem rescaled_velocity_pointwise
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ‖rescaleVelocity μ z₀ u z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (μ ^ 2) *
        (‖u (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ)) := by
  change ‖μ • u (scalingParabolic μ z₀ z)‖ₑ ^ (2 : ℝ) = _
  rw [enorm_smul]
  rw [← ofReal_norm μ]
  rw [Real.norm_eq_abs, abs_of_pos hμ]
  rw [ENNReal.mul_rpow_of_nonneg]
  on_goal 1 => rw [ENNReal.ofReal_rpow_of_nonneg hμ.le (by norm_num)]
  on_goal 1 => norm_num
  positivity

private theorem memLp_rescale_force
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {f : ParabolicPoint → Vec3} {p : ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hf : MemLp f p (volume.restrict (spaceTimeSet Ω I))) :
    MemLp (rescaleForce μ z₀ f) p
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := memLp_comp_scaling (Ω := Ω) (I := I) μ hμ z₀ hΩ hI hf
  have heq : rescaleForce μ z₀ f = (μ ^ 3) • (f ∘ scalingParabolic μ z₀) := by
    funext w
    rfl
  rw [heq]
  exact hcomp.const_smul (μ ^ 3)

private theorem memLp_rescale_pressure
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ} {r : ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hp : MemLp p r (volume.restrict (spaceTimeSet Ω I))) :
    MemLp (rescalePressure μ z₀ p) r
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := memLp_comp_scaling (Ω := Ω) (I := I) μ hμ z₀ hΩ hI hp
  have heq : rescalePressure μ z₀ p = (μ ^ 2) • (p ∘ scalingParabolic μ z₀) := by
    funext w
    rfl
  rw [heq]
  exact hcomp.const_smul (μ ^ 2)

private theorem aestronglyMeasurable_rescale_force
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {f : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hf : AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (rescaleForce μ z₀ f)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling μ hμ z₀ hΩ hI hf
  exact hcomp.const_smul (μ ^ 3)

private theorem aestronglyMeasurable_rescale_velocity
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hu : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (rescaleVelocity μ z₀ u)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling μ hμ z₀ hΩ hI hu
  have heq : rescaleVelocity μ z₀ u = μ • (u ∘ scalingParabolic μ z₀) := by
    funext w
    rfl
  rw [heq]
  exact hcomp.const_smul μ

private theorem aestronglyMeasurable_rescale_gradient
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (rescaleGradient μ z₀ Du)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling μ hμ z₀ hΩ hI hDu
  have heq : rescaleGradient μ z₀ Du = (μ ^ 2) • (Du ∘ scalingParabolic μ z₀) := by
    funext w
    rfl
  rw [heq]
  exact hcomp.const_smul (μ ^ 2)

private theorem aestronglyMeasurable_rescale_pressure
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hp : AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (rescalePressure μ z₀ p)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling μ hμ z₀ hΩ hI hp
  exact hcomp.const_smul (μ ^ 2)

private lemma _rescale_hR_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3}
      (z₀ : ParabolicPoint) {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ),
          localBox Ω I (scalingSpace μ z₀.1 '' Ω') (scalingTime μ z₀.2 '' J) →
            let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
            let U : ParabolicPoint → ℝ≥0∞ := fun (z : ParabolicPoint) => ‖u z‖ₑ ^ (2 : ℝ);
            let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
              ∫⁻ (x : Vec3) in Ωf,
                U
                  (have this : ParabolicPoint := (x, s);
                  this);
            let R : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
              ∫⁻ (x : Vec3) in Ω', ‖rescaleVelocity μ z₀ u (x, s)‖ₑ ^ (2 : ℝ);
            (∀ᵐ (s : ℝ) ∂volume.restrict J,
                AEMeasurable
                  (fun (x : Vec3) =>
                    U
                      (have this : ParabolicPoint := (x, scalingTime μ z₀.2 s);
                      this))
                  (volume.restrict Ωf)) →
              ∀ᵐ (s : ℝ) ∂volume.restrict J,
                R s =
                  ENNReal.ofReal (μ ^ (2 : ℕ)) *
                    (ENNReal.ofReal (μ⁻¹ ^ (3 : ℕ)) * E (scalingTime μ z₀.2 s))
    := by
  intro Ω I u f z₀ μ hμ Ω' J hforward Ωf U E R hUslice'
  filter_upwards [hUslice'] with s hs
  have hsp := lintegral_comp_scaling_space μ hμ z₀.1
    (Ω := Ωf) hforward.1.measurableSet hs
  rw [rescaledSpace_image_eq μ hμ z₀.1 Ω'] at hsp
  have hmapS := map_scalingSpace_restrict hμ z₀.1
    (Ω := Ωf) hforward.1.measurableSet
  rw [rescaledSpace_image_eq μ hμ z₀.1 Ω'] at hmapS
  have hFmap : AEMeasurable
      (fun x => U (show ParabolicPoint from
        (x, scalingTime μ z₀.2 s)))
      (Measure.map (scalingSpace μ z₀.1) (volume.restrict Ω')) := by
    rw [hmapS]
    exact hs.smul_measure (ENNReal.ofReal (μ⁻¹ ^ 3))
  have hcomp : AEMeasurable
      (fun x => U (show ParabolicPoint from
        (scalingSpace μ z₀.1 x, scalingTime μ z₀.2 s)))
      (volume.restrict Ω') := by
    exact hFmap.comp_measurable (by
      rw [← spatialHomeomorph_eq μ hμ z₀.1]
      exact (spatialHomeomorph μ hμ z₀.1).measurable)
  have hconst := lintegral_const_mul''
    (μ := volume.restrict Ω')
    (f := fun x => U (scalingParabolic μ z₀ (x, s)))
    (ENNReal.ofReal (μ ^ 2)) hcomp
  calc
    R s = ENNReal.ofReal (μ ^ 2) *
        (∫⁻ x in Ω', U (scalingParabolic μ z₀ (x, s))) := by
          dsimp [R]
          rw [show (fun x =>
              ‖rescaleVelocity μ z₀ u (x, s)‖ₑ ^ (2 : ℝ)) =
              (fun x => ENNReal.ofReal (μ ^ 2) *
                U (scalingParabolic μ z₀ (x, s))) by
            funext x
            exact rescaled_velocity_pointwise μ hμ z₀ u (x, s)]
          simpa [R] using hconst
    _ = ENNReal.ofReal (μ ^ 2) *
        (ENNReal.ofReal (μ⁻¹ ^ 3) * E (scalingTime μ z₀.2 s)) := by
          have hpar : (fun x : Vec3 =>
              U (scalingParabolic μ z₀ (x, s))) =
              (fun x : Vec3 => U (show ParabolicPoint from
                (scalingSpace μ z₀.1 x, scalingTime μ z₀.2 s))) := by
            funext x
            rw [scalingParabolic_eq]
          rw [hpar]
          simpa [E] using
            congrArg (fun y => ENNReal.ofReal (μ ^ 2) * y) hsp

private lemma _rescale_hUslice'_1 :
    ∀ {u : ParabolicPoint → Vec3} (z₀ : ParabolicPoint) {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ),
          let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
          let Jf : Set ℝ := scalingTime μ z₀.2 '' J;
          let U : ParabolicPoint → ℝ≥0∞ := fun (z : ParabolicPoint) => ‖u z‖ₑ ^ (2 : ℝ);
          (∀ᵐ (s : ℝ) ∂Measure.restrict volume Jf,
              AEMeasurable (β := ℝ≥0∞) (_m := MeasureSpace.toMeasurableSpace)
                (fun (x : Vec3) => U (x, s)) (Measure.restrict volume Ωf)) →
            Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J) =
                HSMul.hSMul (β := Measure ℝ) (ENNReal.ofReal (μ ^ (2 : ℕ))⁻¹)
                  (Measure.restrict volume (scalingTime μ z₀.2 '' J)) →
              Measurable (scalingTime μ z₀.2) →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                  AEMeasurable (β := ℝ≥0∞) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) =>
                      U
                        (have this : ParabolicPoint := (x, scalingTime μ z₀.2 s);
                        this))
                    (Measure.restrict volume Ωf)
    := by
  intro u z₀ μ hμ Ω' J Ωf Jf U hUslice hmapT hTmeas
  have hc : ENNReal.ofReal ((μ ^ 2)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  dsimp [Jf] at hUslice
  rw [← Measure.ae_ennreal_smul_measure_eq hc] at hUslice
  rw [← hmapT] at hUslice
  exact ae_of_ae_map hTmeas.aemeasurable hUslice

private lemma _rescale_hres_2 :
    ∀ {u : ParabolicPoint → Vec3} (z₀ : ParabolicPoint) {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ),
          let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
          let Jf : Set ℝ := scalingTime μ z₀.2 '' J;
          let U : ParabolicPoint → ℝ≥0∞ := fun (z : ParabolicPoint) => ‖u z‖ₑ ^ (2 : ℝ);
          let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
            ∫⁻ (x : Vec3) in Ωf,
              U
                (have this : ParabolicPoint := (x, s);
                this);
          let R : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
            ∫⁻ (x : Vec3) in Ω', ‖rescaleVelocity μ z₀ u (x, s)‖ₑ ^ (2 : ℝ);
          Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J) =
              HSMul.hSMul (β := Measure ℝ) (ENNReal.ofReal (μ ^ (2 : ℕ))⁻¹)
                (Measure.restrict volume (scalingTime μ z₀.2 '' J)) →
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                (fun (s : ℝ) => ∫⁻ (x : Vec3) in Ω', ‖rescaleVelocity μ z₀ u (x, s)‖ₑ ^ (2 : ℝ)) s =
                  ENNReal.ofReal (μ ^ (2 : ℕ)) *
                    (ENNReal.ofReal (μ⁻¹ ^ (3 : ℕ)) *
                      (fun (s : ℝ) =>
                          ∫⁻ (x : Vec3) in scalingSpace μ z₀.1 '' Ω',
                            (fun (z : ParabolicPoint) => ‖u z‖ₑ ^ (2 : ℝ))
                              (have this : ParabolicPoint := (x, s);
                              this))
                        (scalingTime μ z₀.2 s))) →
              @essSup _ _ _ MeasureSpace.toMeasurableSpace E (Measure.restrict volume Jf) < ∞ →
                @essSup _ _ _ Real.measurableSpace E
                      (Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J)) =
                    @essSup _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (s : ℝ) => E (scalingTime μ z₀.2 s)) (Measure.restrict volume J) →
                  @essSup _ _ _ MeasureSpace.toMeasurableSpace R (Measure.restrict volume J) < ∞
    := by
  intro u z₀ μ hμ Ω' J Ωf Jf U E R hmapT hR hsource hess'
  rw [essSup_congr_ae hR]
  rw [ENNReal.essSup_const_mul]
  rw [ENNReal.essSup_const_mul]
  rw [← hess']
  rw [hmapT, essSup_ennreal_smul_measure]
  · exact ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsource)
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

private lemma _rescale_hsliceU_3 :
    ∀ {u : ParabolicPoint → Vec3} (z₀ : ParabolicPoint) {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ) (i : Fin (3 : ℕ)),
          let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
          let Jf : Set ℝ := scalingTime μ z₀.2 '' J;
          (∀ᵐ (s : ℝ) ∂Measure.restrict volume Jf,
              AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                (fun (x : Vec3) => u (x, s) i) (Measure.restrict volume Ωf)) →
            Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J) =
                HSMul.hSMul (β := Measure ℝ) (ENNReal.ofReal (μ ^ (2 : ℕ))⁻¹)
                  (Measure.restrict volume (scalingTime μ z₀.2 '' J)) →
              Measurable (scalingTime μ z₀.2) →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                  AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => u (x, scalingTime μ z₀.2 s) i) (Measure.restrict volume Ωf)
    := by
  intro u z₀ μ hμ Ω' J i Ωf Jf hUiSlice hmapT hTmeas
  have hc : ENNReal.ofReal ((μ ^ 2)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  dsimp [Jf] at hUiSlice
  rw [← Measure.ae_ennreal_smul_measure_eq hc] at hUiSlice
  rw [← hmapT] at hUiSlice
  exact ae_of_ae_map hTmeas.aemeasurable hUiSlice

private lemma _rescale_hsliceDu_4 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} (z₀ : ParabolicPoint) {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ) (i : Fin (3 : ℕ)),
          let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
          let Jf : Set ℝ := scalingTime μ z₀.2 '' J;
          (∀ᵐ (s : ℝ) ∂Measure.restrict volume Jf,
              AEStronglyMeasurable (β := Vec3) (m₀ := MeasureSpace.toMeasurableSpace)
                (fun (x : Vec3) => Du (x, s) i) (Measure.restrict volume Ωf)) →
            Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J) =
                HSMul.hSMul (β := Measure ℝ) (ENNReal.ofReal (μ ^ (2 : ℕ))⁻¹)
                  (Measure.restrict volume (scalingTime μ z₀.2 '' J)) →
              Measurable (scalingTime μ z₀.2) →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                  AEStronglyMeasurable (β := Vec3) (m₀ := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => Du (x, scalingTime μ z₀.2 s) i) (Measure.restrict volume Ωf)
    := by
  intro Du z₀ μ hμ Ω' J i Ωf Jf hDuiSlice hmapT hTmeas
  have hc : ENNReal.ofReal ((μ ^ 2)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  dsimp [Jf] at hDuiSlice
  rw [← Measure.ae_ennreal_smul_measure_eq hc] at hDuiSlice
  rw [← hmapT] at hDuiSlice
  exact ae_of_ae_map hTmeas.aemeasurable hDuiSlice

private lemma _rescale_hgradTarget_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} (z₀ : ParabolicPoint)
      {μ : ℝ},
      (0 : ℝ) < μ →
        ∀ (Ω' : Set Vec3) (J : Set ℝ) (i : Fin (3 : ℕ)),
          let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω';
          let Jf : Set ℝ := scalingTime μ z₀.2 '' J;
          (∀ᵐ (s : ℝ) ∂Measure.restrict volume Jf,
              HasWeakGradientOn Ωf (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
                Du (x, s) i) →
            Measure.map (scalingTime μ z₀.2) (Measure.restrict volume J) =
                HSMul.hSMul (β := Measure ℝ) (ENNReal.ofReal (μ ^ (2 : ℕ))⁻¹)
                  (Measure.restrict volume (scalingTime μ z₀.2 '' J)) →
              Measurable (scalingTime μ z₀.2) →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                  HasWeakGradientOn Ωf (fun (x : Vec (3 : ℕ)) => u (x, scalingTime μ z₀.2 s) i)
                    fun (x : Vec (3 : ℕ)) => Du (x, scalingTime μ z₀.2 s) i
    := by
  intro u Du z₀ μ hμ Ω' J i Ωf Jf hgradSource hmapT hTmeas
  have hc : ENNReal.ofReal ((μ ^ 2)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  dsimp [Jf] at hgradSource
  rw [← Measure.ae_ennreal_smul_measure_eq hc] at hgradSource
  rw [← hmapT] at hgradSource
  exact ae_of_ae_map hTmeas.aemeasurable hgradSource

private theorem rescaled_energy_finite
    (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hu : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω I)))
    (hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω I)))
    (henergy : (∫⁻ z in spaceTimeSet Ω I,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (∫⁻ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
      ‖rescaleVelocity μ z₀ u z‖ₑ ^ (2 : ℝ) +
        ‖rescaleGradient μ z₀ Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let U : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ)
  let D : ParabolicPoint → ℝ≥0∞ := fun z => ‖Du z‖ₑ ^ (2 : ℝ)
  have hU : AEMeasurable U (volume.restrict (spaceTimeSet Ω I)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hu.enorm
  have hD : AEMeasurable D (volume.restrict (spaceTimeSet Ω I)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hDu.enorm
  have hUcomp := aemeasurable_comp_scaling μ hμ z₀ hΩ hI hU
  have hDcomp := aemeasurable_comp_scaling μ hμ z₀ hΩ hI hD
  have hUfin : (∫⁻ z in spaceTimeSet Ω I, U z) < ⊤ :=
    (lintegral_mono fun z => le_add_right (le_refl (U z))).trans_lt henergy
  have hDfin : (∫⁻ z in spaceTimeSet Ω I, D z) < ⊤ :=
    (lintegral_mono fun z => le_add_left (le_refl (D z))).trans_lt henergy
  simp_rw [rescaled_energy_pointwise μ hμ z₀]
  change (∫⁻ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
    ENNReal.ofReal (μ ^ 2) * (U ∘ scalingParabolic μ z₀) z +
      ENNReal.ofReal (μ ^ 4) * (D ∘ scalingParabolic μ z₀) z) < ⊤
  rw [lintegral_add_left' (hUcomp.const_mul _),
    lintegral_const_mul'' _ hUcomp, lintegral_const_mul'' _ hDcomp]
  change ENNReal.ofReal (μ ^ 2) *
      (∫⁻ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
        U (scalingParabolic μ z₀ z)) +
    ENNReal.ofReal (μ ^ 4) *
      (∫⁻ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
        D (scalingParabolic μ z₀ z)) < ⊤
  rw [lintegral_comp_scaling μ hμ z₀ hΩ hI hU,
    lintegral_comp_scaling μ hμ z₀ hΩ hI hD]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin)⟩

theorem isSuitableWeakSolutionIntegrable_rescale
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {μ : ℝ} (hμ : 0 < μ) :
    IsSuitableWeakSolutionIntegrable (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) q
      (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
      (rescalePressure μ z₀ p) (rescaleForce μ z₀ f) := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hforce, hlocal, hS2, hS3, hS4⟩
  refine ⟨rescaledSpace_isOpen z₀.1 hΩ, rescaledTime_isOpen z₀.2 hI,
    rescaledTime_ordConnected hμ z₀.2 hIord, hq, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω' J hbox
    have hforward := localBox_forward hμ z₀ hbox
    rcases hforce _ _ hforward with hfi
    intro i
    have hfi' := hfi i
    change MemLp (fun z => f z i) (ENNReal.ofReal q)
      (volume.restrict
        (spaceTimeSet (scalingSpace μ z₀.1 '' Ω')
          (scalingTime μ z₀.2 '' J))) at hfi'
    have hcomp := memLp_comp_scaling (E := ℝ)
      (Ω := scalingSpace μ z₀.1 '' Ω')
      (I := scalingTime μ z₀.2 '' J) μ hμ z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hfi'
    rw [rescaledSpace_image_eq μ hμ z₀.1 Ω',
      rescaledTime_image_eq μ hμ z₀.2 J] at hcomp
    change MemLp (fun z => rescaleForce μ z₀ f z i) (ENNReal.ofReal q)
      (volume.restrict (spaceTimeSet Ω' J))
    have heq : (fun z => rescaleForce μ z₀ f z i) =
        (μ ^ 3) • ((fun z => f z i) ∘ scalingParabolic μ z₀) := by
      funext z
      rfl
    rw [heq]
    exact hcomp.const_smul (μ ^ 3)
  · intro Ω' J hbox
    have hforward := localBox_forward hμ z₀ hbox
    rcases hlocal _ _ hforward with hloc
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hu := aestronglyMeasurable_rescale_velocity μ hμ z₀
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet hloc.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hu
    · have hDu := aestronglyMeasurable_rescale_gradient μ hμ z₀
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet hloc.2.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hDu
    · have hp := aestronglyMeasurable_rescale_pressure μ hμ z₀
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet hloc.2.2.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hp
    · have hf := aestronglyMeasurable_rescale_force μ hμ z₀
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet hloc.2.2.2.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hf
    · let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω'
      let Jf : Set ℝ := scalingTime μ z₀.2 '' J
      let U : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ)
      let E : ℝ → ℝ≥0∞ := fun s =>
        ∫⁻ x in Ωf, U (show ParabolicPoint from (x, s))
      let R : ℝ → ℝ≥0∞ := fun s =>
        ∫⁻ x in Ω', ‖rescaleVelocity μ z₀ u (x, s)‖ₑ ^ (2 : ℝ)
      have hU : AEMeasurable U
          (volume.restrict (spaceTimeSet Ωf Jf)) := by
        exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          hloc.1.enorm
      have hUprod : AEMeasurable U
          ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
        rw [Measure.prod_restrict]
        exact hU
      have hE : AEMeasurable E (volume.restrict Jf) := by
        exact hUprod.lintegral_prod_left'
      have hUslice : ∀ᵐ s ∂volume.restrict Jf,
          AEMeasurable (fun x => U (x, s)) (volume.restrict Ωf) := by
        exact ae_slice_aemeasurable hUprod
      have hmapT := map_scalingTime_restrict hμ z₀.2
        (I := scalingTime μ z₀.2 '' J) hforward.2.2.2.1.measurableSet
      rw [rescaledTime_image_eq μ hμ z₀.2 J] at hmapT
      have hTmeas : Measurable (scalingTime μ z₀.2) := by
        rw [← temporalHomeomorph_eq μ hμ z₀.2]
        exact (temporalHomeomorph μ hμ z₀.2).measurable
      have hUslice' := @_rescale_hUslice'_1 u z₀ μ hμ Ω' J hUslice hmapT hTmeas
      have hR := @_rescale_hR_1 Ω I u f z₀ μ hμ Ω' J hforward hUslice'
      have hsource : essSup E (volume.restrict Jf) < ⊤ := by
        simpa [E, Ωf, Jf, U] using hloc.2.2.2.2.1
      have hmapE : AEMeasurable E
          (Measure.map (scalingTime μ z₀.2) (volume.restrict J)) := by
        rw [hmapT]
        exact hE.smul_measure (ENNReal.ofReal ((μ ^ 2)⁻¹))
      have hess := essSup_map_measure hmapE hTmeas.aemeasurable
        (hg_co := ⟨0, fun _ _ => bot_le⟩)
        (hgf := isBoundedUnder_of_eventually_le
          (Eventually.of_forall (fun _ => le_top)))
        (hgf_co := ⟨0, fun _ _ => bot_le⟩)
        (hg_bdd := isBoundedUnder_of_eventually_le
          (Eventually.of_forall (fun _ => le_top)))
      have hess' : essSup E
          (Measure.map (scalingTime μ z₀.2) (volume.restrict J)) =
          essSup (fun s => E (scalingTime μ z₀.2 s))
            (volume.restrict J) := by
        simpa [Function.comp_def] using hess
      have hres := @_rescale_hres_2 u z₀ μ hμ Ω' J hmapT hR hsource hess'
      exact hres
    · have henergy := rescaled_energy_finite μ hμ z₀
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet
        hloc.1 hloc.2.1 hloc.2.2.2.2.2.1
      simpa only [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using henergy
    · have hp := memLp_rescale_pressure μ hμ z₀
        (Ω := scalingSpace μ z₀.1 '' Ω')
        (I := scalingTime μ z₀.2 '' J)
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet
        hloc.2.2.2.2.2.2.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hp
    · have hf := memLp_rescale_force μ hμ z₀
        (Ω := scalingSpace μ z₀.1 '' Ω')
        (I := scalingTime μ z₀.2 '' J)
        hforward.1.measurableSet hforward.2.2.2.1.measurableSet
        hloc.2.2.2.2.2.2.2.1
      simpa [rescaledSpace_image_eq μ hμ z₀.1 Ω',
        rescaledTime_image_eq μ hμ z₀.2 J] using hf
    · intro i
      let Ωf : Set Vec3 := scalingSpace μ z₀.1 '' Ω'
      let Jf : Set ℝ := scalingTime μ z₀.2 '' J
      have hUi : AEStronglyMeasurable (fun z => u z i)
          (volume.restrict (spaceTimeSet Ωf Jf)) := by
        exact (continuous_apply i).comp_aestronglyMeasurable hloc.1
      have hDui : AEStronglyMeasurable (fun z => Du z i)
          (volume.restrict (spaceTimeSet Ωf Jf)) := by
        exact (continuous_apply i).comp_aestronglyMeasurable hloc.2.1
      have hUiProd : AEStronglyMeasurable (fun z => u z i)
          ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
        rw [Measure.prod_restrict]
        exact hUi
      have hDuiProd : AEStronglyMeasurable (fun z => Du z i)
          ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
        rw [Measure.prod_restrict]
        exact hDui
      have hUiSlice : ∀ᵐ s ∂volume.restrict Jf,
          AEStronglyMeasurable (fun x => u (x, s) i) (volume.restrict Ωf) := by
        exact ae_slice_aestronglyMeasurable hUiProd
      have hDuiSlice : ∀ᵐ s ∂volume.restrict Jf,
          AEStronglyMeasurable (fun x => Du (x, s) i) (volume.restrict Ωf) := by
        exact ae_slice_aestronglyMeasurable hDuiProd
      have hgradSource : ∀ᵐ s ∂volume.restrict Jf,
          HasWeakGradientOn Ωf (fun x => u (x, s) i)
            (fun x => Du (x, s) i) := by
        exact hloc.2.2.2.2.2.2.2.2 i
      have hmapT := map_scalingTime_restrict hμ z₀.2
        (I := scalingTime μ z₀.2 '' J) hforward.2.2.2.1.measurableSet
      rw [rescaledTime_image_eq μ hμ z₀.2 J] at hmapT
      have hTmeas : Measurable (scalingTime μ z₀.2) := by
        rw [← temporalHomeomorph_eq μ hμ z₀.2]
        exact (temporalHomeomorph μ hμ z₀.2).measurable
      have hsliceU := @_rescale_hsliceU_3 u z₀ μ hμ Ω' J i hUiSlice hmapT hTmeas
      have hsliceDu := @_rescale_hsliceDu_4 Du z₀ μ hμ Ω' J i hDuiSlice hmapT hTmeas
      have hgradTarget := @_rescale_hgradTarget_5 u Du z₀ μ hμ Ω' J i hgradSource hmapT hTmeas
      filter_upwards [hgradTarget, hsliceU, hsliceDu] with s hs hUs hDs
      change ∀ j : Fin 3, _
      intro j
      have hDsj : AEStronglyMeasurable
          (fun x => Du (x, scalingTime μ z₀.2 s) i j)
          (volume.restrict Ωf) := by
        exact (continuous_apply j).comp_aestronglyMeasurable hDs
      have hscaled := hasWeakPartialDerivOn_scaling μ hμ z₀.1
        hforward.1.measurableSet j (by rfl) (hs j) hUs hDsj
      simpa [rescaleVelocity, rescaleGradient, scalingParabolic, scalingSpace,
        scalingTime, parabolicTranslate, parabolicScale] using hscaled
  · intro ψ hψ
    exact s2_rescale hΩ.measurableSet hI.measurableSet hS2 z₀ hμ ψ hψ
  · intro φ hφ
    exact s3_rescale hΩ.measurableSet hI.measurableSet hS3 z₀ hμ φ hφ
  · intro ψ hψ hψnonneg
    exact s4_rescale hΩ.measurableSet hI.measurableSet hS4 z₀ hμ ψ hψ hψnonneg

end CKN
