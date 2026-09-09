/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatDerivative
import LeanPool.NavierStokesAndEuler.Euler.ClosedTranslationGraph
import Mathlib.Algebra.Order.Star.Real

/-! The Gaussian variance generator is one half of the genuine squared translation derivative. -/

@[expose] public section


noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
   EulerClosedTranslationGraph
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A continuous real-parameter extension of the Gaussian average, constant for negative variance.
-/
def realLineHeat (a : LiftTangent) (t : ℝ) (f : LiftL2 period) : LiftL2 period :=
  ∫ x : ℝ, lineOrbit period a f (Real.sqrt t * x) ∂gaussianReal 0 1

theorem realLineHeat_eq (a : LiftTangent) {t : ℝ} (ht : 0 ≤ t) (f : LiftL2 period) :
    realLineHeat period a t f = lineHeat period a ⟨t, ht⟩ f :=
  (lineHeat_eq_standardGaussian period a ⟨t, ht⟩ f).symm

@[simp] theorem realLineHeat_zero (a : LiftTangent) (f : LiftL2 period) : realLineHeat period a 0 f
    = f := by
  rw [realLineHeat_eq period a le_rfl]
  exact lineHeat_zero period a f

theorem realLineHeat_continuous (a : LiftTangent) (f : LiftL2 period) :
    Continuous (fun t : ℝ => realLineHeat period a t f) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro t
    exact ((lineOrbit_continuous period a f).comp (continuous_const.mul
        continuous_id)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f _).le)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x =>
      (lineOrbit_continuous period a f).comp (Real.continuous_sqrt.mul_const x))

/-- The chain-rule derivative of a scaled orbit, before Gaussian integration. -/
theorem scaledOrbit_hasDerivAt (a : LiftTangent) (f g : LiftL2 period)
    (hD : HasDerivAt (lineOrbit period a f) g 0) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => lineOrbit period a f (Real.sqrt s * x))
      ((x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x)) t := by
  have ho := translation_hasDerivAt_all period a f g hD (Real.sqrt t * x)
  have hs := (Real.hasDerivAt_sqrt ht.ne').mul_const x
  have h := ho.scomp t hs
  convert! h using 1
  change (x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x) =
    (1 / (2 * Real.sqrt t) * x) • lineOrbit period a g (Real.sqrt t * x)
  congr 1
  ring

/-- Differentiation of the Gaussian average at positive variance is justified by an integrable first
moment. -/
theorem realLineHeat_hasDerivAt_moment (a : LiftTangent) (f g : LiftL2 period)
    (hD : HasDerivAt (lineOrbit period a f) g 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realLineHeat period a s f)
      (∫ x : ℝ, (x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x) ∂gaussianReal 0 1)
          t := by
  let F : ℝ → ℝ → LiftL2 period := fun s x => lineOrbit period a f (Real.sqrt s * x)
  let F' : ℝ → ℝ → LiftL2 period := fun s x => (x / (2 * Real.sqrt s)) • lineOrbit period a g
      (Real.sqrt s * x)
  let B : ℝ → ℝ := fun x => (‖x‖ / (2 * Real.sqrt (t/2))) * ‖g‖
  have hhalf : 0 < t/2 := by linarith
  have hder (x s : ℝ) (hs : s ∈ Set.Ioi (t/2)) : HasDerivAt (fun r => F r x) (F' s x) s :=
    scaledOrbit_hasDerivAt period a f g hD x s (hhalf.trans hs)
  have hbound : ∀ x s : ℝ, s ∈ Set.Ioi (t/2) → ‖F' s x‖ ≤ B x := by
    intro x s hs
    have hspos : 0 < s := hhalf.trans hs
    dsimp [F', B]
    rw [norm_smul, lineOrbit_norm, Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hspos))]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (abs_nonneg x)
        (mul_pos (by norm_num) (Real.sqrt_pos.mpr hhalf))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs.le) (by norm_num))) (norm_nonneg g)
  have hFint : Integrable (F t) (gaussianReal 0 1) :=
    Integrable.of_bound ((lineOrbit_continuous period a f).comp (continuous_const.mul
        continuous_id)).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f _).le))
  have hBint : Integrable B (gaussianReal 0 1) :=
    ((gaussianId_integrable 1).norm.div_const (2 * Real.sqrt (t/2))).mul_const ‖g‖
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (Ioi_mem_nhds (by linarith : t/2 < t))
    (Filter.Eventually.of_forall (fun s =>
      ((lineOrbit_continuous period a f).comp (continuous_const.mul
          continuous_id)).aestronglyMeasurable))
    hFint
    (((continuous_id.div_const (2 * Real.sqrt t)).smul
      ((lineOrbit_continuous period a g).comp (continuous_const.mul
          continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound) hBint (Filter.Eventually.of_forall hder)
  exact h.2

/-- Gaussian scaling rewrites the variance derivative as one half of the averaged orbit derivative.
-/
theorem varianceMoment_eq_half_derivative (a : LiftTangent) {t : ℝ} (ht : 0 < t) (g : LiftL2
    period) :
    (∫ x : ℝ, (x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x) ∂gaussianReal 0 1) =
      (1/2 : ℝ) • lineHeatDerivative period a ⟨t, ht.le⟩ g := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hmap : Measure.map (fun x => Real.sqrt t * x) (gaussianReal 0 1) = gaussianReal 0 ⟨t, ht.le⟩
      := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt t)
    have he : NNReal.mk (Real.sqrt t ^ 2) (sq_nonneg _) * 1 = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply Subtype.ext
      change Real.sqrt t ^ 2 * 1 = t
      rw [mul_one, Real.sq_sqrt ht.le]
    rw [mul_zero, he] at h
    exact h
  change (∫ x : ℝ, (x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x) ∂gaussianReal 0
      1) =
    (1/2 : ℝ) • (t⁻¹ • ∫ x : ℝ, x • lineOrbit period a g x ∂gaussianReal 0 ⟨t, ht.le⟩)
  have hm := integral_map_of_stronglyMeasurable
    (μ := gaussianReal 0 1) (φ := fun x : ℝ => Real.sqrt t * x)
    (f := fun x : ℝ => x • lineOrbit period a g x) (by fun_prop)
    ((continuous_id.smul (lineOrbit_continuous period a g)).stronglyMeasurable)
  rw [← hmap, hm, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (x / (2 * Real.sqrt t)) • lineOrbit period a g (Real.sqrt t * x) =
    (1/2 : ℝ) • t⁻¹ • (Real.sqrt t * x) • lineOrbit period a g (Real.sqrt t * x)
  simp only [smul_smul]
  congr 1
  field_simp
  rw [Real.sq_sqrt ht.le]

/-- At every positive variance, the generator is one half of the genuine second translation
derivative. -/
theorem realLineHeat_generator_pos (a : LiftTangent) (f g h : LiftL2 period)
    (hD : HasDerivAt (lineOrbit period a f) g 0)
    (hDD : HasDerivAt (lineOrbit period a g) h 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realLineHeat period a s f) ((1/2 : ℝ) • realLineHeat period a t h) t := by
  have hd := realLineHeat_hasDerivAt_moment period a f g hD ht
  rw [varianceMoment_eq_half_derivative period a ht g,
    ← lineHeat_derivative_identity period a (show (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 by
        intro hz; have hzR := congrArg (fun z : ℝ≥0 => (z : ℝ)) hz; exact ht.ne' hzR) g h hDD,
    ← realLineHeat_eq period a ht.le h] at hd
  exact hd

/-- The generator formula also holds as a genuine right derivative at zero variance. -/
theorem realLineHeat_generator_zero (a : LiftTangent) (f g h : LiftL2 period)
    (hD : HasDerivAt (lineOrbit period a f) g 0)
    (hDD : HasDerivAt (lineOrbit period a g) h 0) :
    HasDerivWithinAt (fun s => realLineHeat period a s f) ((1/2 : ℝ) • h) (Set.Ici 0) 0 := by
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realLineHeat period a s h)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • h)) := by
    have hc : ContinuousAt (fun s => (1/2 : ℝ) • realLineHeat period a s h) 0 :=
      ((realLineHeat_continuous period a h).const_smul (1/2 : ℝ)).continuousAt
    simpa only [realLineHeat_zero] using (hc.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realLineHeat_generator_pos period a f g h hD hDD
        ht).differentiableAt.differentiableWithinAt)
    (realLineHeat_continuous period a f).continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realLineHeat_generator_pos period a f g h hD hDD ht).deriv.symm

end EulerGaussianCylinderHeat
