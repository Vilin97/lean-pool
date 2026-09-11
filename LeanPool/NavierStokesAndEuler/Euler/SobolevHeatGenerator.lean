/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable

public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeat
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureJetIdentities
public import LeanPool.NavierStokesAndEuler.Euler.MetricHeatEnergy
public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatTotal
public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatDerivative
import LeanPool.NavierStokesAndEuler.Euler.ClosedTranslationGraph

/-! A bounded actual Laplacian evaluation and the genuine heat generator on finite Sobolev data. -/

section

/-! The genuine cylinder heat semigroup solves the Laplacian evolution equation. -/

section

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
        continuous_id)).aestronglyMeasurable_of_secondCountable
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
        continuous_id)).aestronglyMeasurable_of_secondCountable
      ‖f‖ (Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f _).le))
  have hBint : Integrable B (gaussianReal 0 1) :=
    ((gaussianId_integrable 1).norm.div_const (2 * Real.sqrt (t/2))).mul_const ‖g‖
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (Ioi_mem_nhds (by linarith : t/2 < t))
    (Filter.Eventually.of_forall (fun s =>
      ((lineOrbit_continuous period a f).comp (continuous_const.mul
          continuous_id)).aestronglyMeasurable_of_secondCountable))
    hFint
    (((continuous_id.div_const (2 * Real.sqrt t)).smul
      ((lineOrbit_continuous period a g).comp (continuous_const.mul
          continuous_id))).aestronglyMeasurable_of_secondCountable)
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

end
end

end

section

/-! Differentiation of jointly continuous operator families without operator-norm differentiability.
-/

@[expose] public section

noncomputable section

namespace EulerStrongOperatorDerivative

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact slope decomposition for a varying bounded linear operator and a varying input. -/
theorem slope_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t s : ℝ) :
    slope (fun r => A r (u r)) t s = A s (slope u t s) + slope (fun r => A r (u t)) t s := by
  simp only [slope, vsub_eq_sub, map_smul, map_sub]
  rw [← smul_add]
  congr 1
  abel

/-- A product rule requiring joint strong continuity only at the limiting derivative vector. -/
theorem hasDerivAt_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t : ℝ) (u' : E) (a' : F)
    (hu : HasDerivAt u u' t) (ha : HasDerivAt (fun s => A s (u t)) a' t)
    (hc : ContinuousAt (fun p : ℝ × E => A p.1 p.2) (t, u')) :
    HasDerivAt (fun s => A s (u s)) (A t u' + a') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hfirst : Tendsto (fun s => A s (slope u t s)) (𝓝[≠] t) (𝓝 (A t u')) :=
    hc.tendsto.comp ((show Tendsto (fun r : ℝ => r) (𝓝[≠] t) (𝓝 t) from
        nhdsWithin_le_nhds).prodMk_nhds hu.tendsto_slope)
  exact (hfirst.add ha.tendsto_slope).congr'
    (Filter.Eventually.of_forall (fun s => (slope_apply A u t s).symm))

/-- The same product rule for a one-sided derivative. -/
theorem hasDerivWithinAt_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t : ℝ) (s : Set ℝ) (u' : E) (a' : F)
    (hu : HasDerivWithinAt u u' s t) (ha : HasDerivWithinAt (fun r => A r (u t)) a' s t)
    (hc : ContinuousAt (fun p : ℝ × E => A p.1 p.2) (t, u')) :
    HasDerivWithinAt (fun r => A r (u r)) (A t u' + a') s t := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hfirst : Tendsto (fun r => A r (slope u t r)) (𝓝[s \ {t}] t) (𝓝 (A t u')) :=
    hc.tendsto.comp ((show Tendsto (fun r : ℝ => r) (𝓝[s \ {t}] t) (𝓝 t) from
        nhdsWithin_le_nhds).prodMk_nhds
      (hasDerivWithinAt_iff_tendsto_slope.mp hu))
  exact (hfirst.add (hasDerivWithinAt_iff_tendsto_slope.mp ha)).congr'
    (Filter.Eventually.of_forall (fun r => (slope_apply A u t r).symm))

end EulerStrongOperatorDerivative

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
    EulerStrongOperatorDerivative
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The real extension is the nonnegative-variance heat operator evaluated at the positive part. -/
theorem realLineHeat_eq_toNNReal (a : LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realLineHeat period a t f = lineHeat period a t.toNNReal f := by
  rw [realLineHeat, lineHeat_eq_standardGaussian]
  have hs : Real.sqrt (t.toNNReal : ℝ) = Real.sqrt t := by simp only [Real.sqrt, Real.toNNReal_coe]
  rw [hs]

/-- Real-parameter version of the actual bounded heat operator. -/
def realLineHeatOperator (a : LiftTangent) (t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period :=
  lineHeatOperator period a t.toNNReal

@[simp] theorem realLineHeatOperator_apply (a : LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realLineHeatOperator period a t f = realLineHeat period a t f :=
  (realLineHeat_eq_toNNReal period a t f).symm

theorem realLineHeat_joint_continuous (a : LiftTangent) :
    Continuous (fun p : ℝ × LiftL2 period => realLineHeat period a p.1 p.2) := by
  simp_rw [realLineHeat_eq_toNNReal]
  exact (lineHeat_joint_continuous period a).comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

/-- Product rule for the real heat operator applied to a differentiable input curve. -/
theorem realLineHeat_varying_input (a : LiftTangent) (u : ℝ → LiftL2 period) (t : ℝ)
    (u' g h : LiftL2 period) (ht : 0 < t) (hu : HasDerivAt u u' t)
    (hD : HasDerivAt (lineOrbit period a (u t)) g 0)
    (hDD : HasDerivAt (lineOrbit period a g) h 0) :
    HasDerivAt (fun s => realLineHeat period a s (u s))
      (realLineHeat period a t u' + (1/2 : ℝ) • realLineHeat period a t h) t := by
  have h := hasDerivAt_apply (realLineHeatOperator period a) u t u'
    ((1/2 : ℝ) • realLineHeat period a t h) hu
    (by
        simpa only [realLineHeatOperator_apply] using realLineHeat_generator_pos period a (u t) g h
            hD hDD ht)
    (by
        simpa only [realLineHeatOperator_apply] using (realLineHeat_joint_continuous period
            a).continuousAt (x := (t,u')))
  simpa only [realLineHeatOperator_apply] using h

end EulerGaussianCylinderHeat

end
end

end

@[expose] public section

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerCylinderSobolev  EulerStrongOperatorDerivative
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The real extension of a finite commuting heat product. -/
def realHeatList (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) : LiftL2 period :=
  match directions with
  | [] => f
  | a :: tail => realLineHeat period a t (realHeatList tail t f)

theorem realHeatList_eq (directions : List LiftTangent) {t : ℝ} (ht : 0 ≤ t) (f : LiftL2 period) :
    realHeatList period directions t f = heatList period directions ⟨t, ht⟩ f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    change realLineHeat period a t (realHeatList period tail t f) =
      lineHeat period a ⟨t, ht⟩ (heatList period tail ⟨t, ht⟩ f)
    rw [realLineHeat_eq period a ht, ih]

theorem realLineHeat_add (a : LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realLineHeat period a t (f+g) = realLineHeat period a t f + realLineHeat period a t g := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_add]

theorem realLineHeat_smul (a : LiftTangent) (t c : ℝ) (f : LiftL2 period) :
    realLineHeat period a t (c • f) = c • realLineHeat period a t f := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_smul]

theorem realHeatList_add (directions : List LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realHeatList period directions t (f+g) = realHeatList period directions t f + realHeatList
        period directions t g := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_add]

theorem realHeatList_smul (directions : List LiftTangent) (t c : ℝ) (f : LiftL2 period) :
    realHeatList period directions t (c • f) = c • realHeatList period directions t f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_smul]

@[simp] theorem realHeatList_zero_field (directions : List LiftTangent) (t : ℝ) :
    realHeatList period directions t 0 = 0 := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
      simp only [realHeatList, ih, realLineHeat_eq_toNNReal, ← lineHeatOperator_apply, map_zero]

@[simp] theorem realHeatList_zero_time (directions : List LiftTangent) (f : LiftL2 period) :
    realHeatList period directions 0 f = f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, realLineHeat_zero, ih]

theorem realHeatList_eq_toNNReal (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realHeatList period directions t f = heatList period directions t.toNNReal f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    change realLineHeat period a t (realHeatList period tail t f) =
      lineHeat period a t.toNNReal (heatList period tail t.toNNReal f)
    rw [realLineHeat_eq_toNNReal, ih]

theorem realHeatList_continuous (directions : List LiftTangent) (f : LiftL2 period) :
    Continuous (fun t : ℝ => realHeatList period directions t f) := by
  simp_rw [realHeatList_eq_toNNReal]
  exact (heatList_continuous period directions f).comp continuous_real_toNNReal

/-- Every strong coordinate derivative commutes with every finite heat product. -/
theorem realHeatList_strongDerivative (directions : List LiftTangent) (a : LiftTangent) (t : ℝ)
    (f g : LiftL2 period) (hD : HasDerivAt (lineOrbit period a f) g 0) :
    HasDerivAt (lineOrbit period a (realHeatList period directions t f))
      (realHeatList period directions t g) 0 := by
  induction directions with
  | nil => exact hD
  | cons b tail ih =>
    simp only [realHeatList, realLineHeat_eq_toNNReal]
    exact lineHeat_strongDerivative period b a t.toNNReal _ _ ih

/-- The finite directional heat product has the sum of its actual second derivatives as generator.
-/
theorem realHeatList_generator_pos {ι : Type*} (indices : List ι) (direction : ι → LiftTangent)
    (f : LiftL2 period) (df ddf : ι → LiftL2 period)
    (hD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) f) (df i) 0)
    (hDD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) (df i)) (ddf i) 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realHeatList period (indices.map direction) s f)
      ((1/2 : ℝ) • realHeatList period (indices.map direction) t ((indices.map ddf).sum)) t := by
  induction indices with
  | nil =>
      simpa only [List.map_nil, List.sum_nil, realHeatList, smul_zero] using hasDerivAt_const t f
  | cons i tail ih =>
    have htailD := fun j hj => hD j (List.mem_cons_of_mem i hj)
    have htailDD := fun j hj => hDD j (List.mem_cons_of_mem i hj)
    have hinput := ih htailD htailDD
    have hfirst := realHeatList_strongDerivative period (tail.map direction) (direction i) t f (df
        i)
      (hD i (List.mem_cons_self ..))
    have hsecond := realHeatList_strongDerivative period (tail.map direction) (direction i) t (df
        i) (ddf i)
      (hDD i (List.mem_cons_self ..))
    have h := realLineHeat_varying_input period (direction i)
      (fun s => realHeatList period (tail.map direction) s f) t _ _ _ ht hinput hfirst hsecond
    have halg : realLineHeat period (direction i) t
          ((1/2 : ℝ) • realHeatList period (tail.map direction) t ((tail.map ddf).sum)) +
        (1/2 : ℝ) • realLineHeat period (direction i) t (realHeatList period (tail.map direction) t
            (ddf i)) =
        (1/2 : ℝ) • realHeatList period ((i::tail).map direction) t (((i::tail).map ddf).sum) := by
      rw [realLineHeat_smul, ← smul_add, ← realLineHeat_add, ← realHeatList_add]
      simp only [List.map_cons, List.sum_cons, realHeatList]
      rw [add_comm ((tail.map ddf).sum)]
    rw [halg] at h
    exact h

/-- The full directional generator identity holds as a right derivative at zero as well. -/
theorem realHeatList_generator_zero {ι : Type*} (indices : List ι) (direction : ι → LiftTangent)
    (f : LiftL2 period) (df ddf : ι → LiftL2 period)
    (hD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) f) (df i) 0)
    (hDD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) (df i)) (ddf i) 0) :
    HasDerivWithinAt (fun s => realHeatList period (indices.map direction) s f)
      ((1/2 : ℝ) • (indices.map ddf).sum) (Set.Ici 0) 0 := by
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realHeatList period (indices.map direction) s
      ((indices.map ddf).sum))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • (indices.map ddf).sum)) := by
    have hc : ContinuousAt (fun s => (1/2 : ℝ) • realHeatList period (indices.map direction) s
        ((indices.map ddf).sum)) 0 :=
      ((realHeatList_continuous period _ _).const_smul (1/2 : ℝ)).continuousAt
    simpa only [realHeatList_zero_time] using (hc.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realHeatList_generator_pos period indices direction f df ddf hD hDD
        ht).differentiableAt.differentiableWithinAt)
    (realHeatList_continuous period _ _).continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realHeatList_generator_pos period indices direction f df ddf hD hDD ht).deriv.symm

end EulerGaussianCylinderHeat

end
end

end

section

/-! Exact identification of the Gaussian cylinder generator with the actual strong-jet Laplacian. -/

@[expose] public section

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
    EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerMetricHeatEnergy
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every existing strong Sobolev jet is transported by the genuine heat operator. -/
def cylinderHeatJet {q : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection q f) (v :
    ℝ≥0) :
    SpatialJet period standardDirection q (cylinderHeat period v f) :=
  EulerPressureJetIdentities.SpatialJet.map (cylinderHeat period v)
    (fun a f => (cylinderHeat_translation period v a f).symm) J

/-- Heat preserves every actual derivative coordinate. -/
theorem cylinderHeatJet_word {q n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period standardDirection q f) (v : ℝ≥0) (w : Fin n → Fin 4) :
    (cylinderHeatJet period J v).word w = cylinderHeat period v (J.word w) :=
  EulerPressureJetIdentities.SpatialJet.map_word J (cylinderHeat period v) _ w

/-- The actual heat operator commutes with the true strong-jet Laplacian. -/
theorem cylinderHeatJet_laplacian {f : LiftL2 period} (J : SpatialJet period standardDirection 2 f)
    (v : ℝ≥0) :
    jetLaplacian period (cylinderHeatJet period J v) = cylinderHeat period v (jetLaplacian period
        J) := by
  simp only [jetLaplacian, cylinderHeatJet_word, map_sum]

/-- Real-time extension of the cylinder heat semigroup. -/
def realCylinderHeat (t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period := cylinderHeat period t.toNNReal

theorem realCylinderHeat_apply (t : ℝ) (f : LiftL2 period) :
    realCylinderHeat period t f = realHeatList period cylinderDirections t f :=
  (realHeatList_eq_toNNReal period cylinderDirections t f).symm

/-- The actual cylinder heat generator at positive variance is one half of the Laplacian. -/
theorem realCylinderHeat_generator_pos {f : LiftL2 period} (J : SpatialJet period standardDirection
    2 f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realCylinderHeat period s f)
      ((1/2 : ℝ) • realCylinderHeat period t (jetLaplacian period J)) t := by
  let df : Fin 4 → LiftL2 period := fun i => J.word (fun _ : Fin 1 => i)
  let ddf : Fin 4 → LiftL2 period := fun i => J.word (fun _ : Fin 2 => i)
  have hD (i : Fin 4) : HasDerivAt (lineOrbit period (standardDirection i) f) (df i) 0 := by
    have h := J.word_hasDerivAt (show 0 < 2 by omega) Fin.elim0 i
    have he : Fin.cons i Fin.elim0 = (fun _ : Fin 1 => i) := by
      funext j
      fin_cases j
      rfl
    rw [he, SpatialJet.word_zero] at h
    exact h
  have hDD (i : Fin 4) : HasDerivAt (lineOrbit period (standardDirection i) (df i)) (ddf i) 0 := by
    have h := J.word_hasDerivAt (show 1 < 2 by omega) (fun _ : Fin 1 => i) i
    have he : Fin.cons i (fun _ : Fin 1 => i) = (fun _ : Fin 2 => i) := by
      funext j
      fin_cases j <;> rfl
    rw [he] at h
    exact h
  have h := realHeatList_generator_pos period (List.ofFn (fun i : Fin 4 => i)) standardDirection f
      df ddf
    (fun i _ => hD i) (fun i _ => hDD i) ht
  simpa only [List.map_ofFn, Function.comp_def, List.sum_ofFn, realCylinderHeat_apply,
    cylinderDirections, jetLaplacian, ddf] using h

/-- The actual cylinder heat generator at zero variance is a right Laplacian derivative. -/
theorem realCylinderHeat_generator_zero {f : LiftL2 period} (J : SpatialJet period
    standardDirection 2 f) :
    HasDerivWithinAt (fun s => realCylinderHeat period s f)
      ((1/2 : ℝ) • jetLaplacian period J) (Set.Ici 0) 0 := by
  have hc : Continuous (fun t : ℝ => realCylinderHeat period t (jetLaplacian period J)) :=
    (cylinderHeat_continuous period _).comp continuous_real_toNNReal
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realCylinderHeat period s (jetLaplacian period
      J))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • jetLaplacian period J)) := by
    have h := (hc.const_smul (1/2 : ℝ)).continuousAt (x := 0)
    simpa only [Pi.smul_def, realCylinderHeat, Real.toNNReal_zero, cylinderHeat_zero] using
        (h.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realCylinderHeat_generator_pos period J
        ht).differentiableAt.differentiableWithinAt)
    (((cylinderHeat_continuous period f).comp
        continuous_real_toNNReal).continuousAt.continuousWithinAt)
    self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realCylinderHeat_generator_pos period J ht).deriv.symm

/-- Variance2νt is the genuine viscosity-ν heat evolution. -/
def viscousCylinderHeat (ν t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period := realCylinderHeat period
    (2*ν*t)

/-- The constructed heat evolution solves u_t=νΔu, with the actual strong spatial Laplacian. -/
theorem viscousCylinderHeat_equation {f : LiftL2 period} (J : SpatialJet period standardDirection 2
    f)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    HasDerivAt (fun s => viscousCylinderHeat period ν s f)
      (ν • jetLaplacian period (cylinderHeatJet period J (2*ν*t).toNNReal)) t := by
  have hp : 0 < 2*ν*t := by positivity
  have h := (realCylinderHeat_generator_pos period J hp).scomp t
    ((hasDerivAt_id t).const_mul (2*ν))
  simp only [mul_one] at h
  change HasDerivAt (fun s => viscousCylinderHeat period ν s f)
    ((2*ν) • ((1/2 : ℝ) • realCylinderHeat period (2*ν*t) (jetLaplacian period J))) t at h
  rw [smul_smul, show (2*ν)*(1/2 : ℝ)=ν by ring] at h
  rw [cylinderHeatJet_laplacian]
  exact h

end EulerGaussianCylinderHeat

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevHeatGenerator

open MeasureTheory EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerGaussianCylinderHeat EulerMetricHeatEnergy EulerSobolevHeat
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual spatial Laplacian evaluated as a bounded map from Hq to L², q≥2. -/
def laplacianEvaluation (q : ℕ) (hq : 2 ≤ q) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, wordOperator period (⟨⟨2, Nat.lt_succ_of_le hq⟩, fun _ : Fin 2 => i⟩ : SobolevWord q)

/-- The Laplacian evaluation is the sum of the four genuine second derivative coordinates. -/
theorem laplacianEvaluation_apply {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq u =
      ∑ i : Fin 4, word period u hq (fun _ : Fin 2 => i) := by
  simp only [laplacianEvaluation, sum_apply]
  rfl

/-- The actual Laplacian is bounded by four times the complete Sobolev norm. -/
theorem laplacianEvaluation_bound {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    ‖laplacianEvaluation period q hq u‖ ≤ 4 * ‖u‖ := by
  rw [laplacianEvaluation_apply]
  have h := norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun i => word period u hq (fun _ : Fin 2 => i))
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 4, ‖u‖ := Finset.sum_le_sum fun i _ =>
      word_norm_le period u ⟨⟨2, Nat.lt_succ_of_le hq⟩, fun _ : Fin 2 => i⟩
    _ = _ := by simp

/-- Bounded Laplacian evaluation agrees exactly with the existing genuine strong-jet Laplacian. -/
theorem laplacianEvaluation_eq_jet {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq u =
      jetLaplacian period (EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq) := by
  rw [laplacianEvaluation_apply, jetLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique
    (EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq) (toJet period u) rfl le_rfl hq]
  exact (toJet_word period u hq _).symm

/-- The actual Laplacian evaluation commutes with Gaussian heat. -/
theorem laplacianEvaluation_heat {q : ℕ} (hq : 2 ≤ q) (v : ℝ≥0) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq (heatOperator period q v u) =
      cylinderHeat period v (laplacianEvaluation period q hq u) := by
  rw [laplacianEvaluation_apply, laplacianEvaluation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Actual viscous heat on the complete Sobolev space, extended constantly to negative physical
time. -/
def heatFlow (q : ℕ) (ν t : ℝ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  heatOperator period q (2 * ν * t).toNNReal

/-- The Sobolev flow has exactly the original genuine L² viscous heat value. -/
@[simp]
theorem heatFlow_value {q : ℕ} (ν t : ℝ) (u : SobolevSpace period q) :
    value period (heatFlow period q ν t u) = viscousCylinderHeat period ν t (value period u) := rfl

/-- Positive-time heat is differentiable in L² with the actual bounded Laplacian evaluation. -/
theorem heatFlow_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (u : SobolevSpace period q) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => value period (heatFlow period q ν s u))
      (ν • laplacianEvaluation period q hq (heatFlow period q ν t u)) t := by
  have h := viscousCylinderHeat_equation period (EulerH6Pressure.SpatialJet.restrict (toJet period
      u) 2 hq) hν ht
  rw [cylinderHeatJet_laplacian, ← laplacianEvaluation_eq_jet period hq u] at h
  change HasDerivAt (fun s => viscousCylinderHeat period ν s (value period u))
    (ν • laplacianEvaluation period q hq (heatOperator period q (2 * ν * t).toNNReal u)) t
  rw [laplacianEvaluation_heat]
  exact h

/-- The actual L² heat orbit has the half-Laplacian derivative on the nonnegative variance
half-line. -/
theorem realHeat_value_hasDerivWithinAt {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => realCylinderHeat period s (value period u))
      ((1 / 2 : ℝ) • realCylinderHeat period t (laplacianEvaluation period q hq u)) (Set.Ici 0) t
          := by
  let J := EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq
  by_cases hzero : t = 0
  · subst t
    have h := realCylinderHeat_generator_zero period J
    rw [← laplacianEvaluation_eq_jet period hq u] at h
    simpa only [realCylinderHeat, Real.toNNReal_zero, cylinderHeat_zero] using h
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have h := (realCylinderHeat_generator_pos period J hp).hasDerivWithinAt (s := Set.Ici 0)
    rw [← laplacianEvaluation_eq_jet period hq u] at h
    exact h

/-- The heat orbit is Lipschitz in nonnegative variance with a bound from the actual Hq norm. -/
theorem heat_value_lipschitz {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    LipschitzWith (Real.nnabs (2 * ‖u‖)) (fun v : ℝ≥0 => cylinderHeat period v (value period u)) :=
        by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hb : ∀ t ∈ Set.Ici (0 : ℝ),
      ‖(1 / 2 : ℝ) • realCylinderHeat period t (laplacianEvaluation period q hq u)‖ ≤ 2 * ‖u‖ := by
    intro t _
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h := (cylinderHeat_norm_le period t.toNNReal _).trans (laplacianEvaluation_bound period hq
        u)
    change (1 / 2 : ℝ) * ‖cylinderHeat period t.toNNReal (laplacianEvaluation period q hq u)‖ ≤ _
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => realHeat_value_hasDerivWithinAt period hq u t ht) hb (convex_Ici (0 : ℝ))
    (show (w : ℝ) ∈ Set.Ici 0 from w.property) (show (v : ℝ) ∈ Set.Ici 0 from v.property)
  change dist (cylinderHeat period v (value period u)) (cylinderHeat period w (value period u)) ≤
    (Real.nnabs (2 * ‖u‖) : ℝ) * dist (v : ℝ) (w : ℝ)
  simpa only [realCylinderHeat, Real.toNNReal_coe, dist_eq_norm, Real.coe_nnabs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg u))] using h

/-- The constantly extended real-variance heat orbit is globally Lipschitz in L². -/
theorem realHeat_value_lipschitz {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    LipschitzWith (Real.nnabs (2 * ‖u‖)) (fun t : ℝ => realCylinderHeat period t (value period u))
        := by
  simpa only [mul_one, Function.comp_def, realCylinderHeat] using
    (heat_value_lipschitz period hq u).comp Real.lipschitzWith_toNNReal

/-- The actual viscous heat orbit is globally Lipschitz in L², uniformly in time. -/
theorem heatFlow_value_norm_sub_le {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (u : SobolevSpace period q) (s t : ℝ) :
    ‖value period (heatFlow period q ν s u) - value period (heatFlow period q ν t u)‖ ≤
      (4 * ν * ‖u‖) * |s - t| := by
  have h := (realHeat_value_lipschitz period hq u).dist_le_mul (2 * ν * s) (2 * ν * t)
  simp only [dist_eq_norm, Real.coe_nnabs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg u))] at h
  change ‖realCylinderHeat period (2 * ν * s) (value period u) -
    realCylinderHeat period (2 * ν * t) (value period u)‖ ≤ _
  have he : |2 * ν * s - 2 * ν * t| = (2 * ν) * |s - t| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * ν)]
  exact h.trans_eq (by rw [he]; ring)

end EulerSobolevHeatGenerator
