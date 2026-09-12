/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatGenerator
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel

import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of the actual heat Duhamel integral in L² from finite Sobolev forcing. -/

@[expose] public section


noncomputable section

namespace EulerDuhamelDifferentiation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual Sobolev heat flow is jointly continuous in real time and its initial field. -/
theorem heatFlow_joint_continuous (q : ℕ) (ν : ℝ) :
    Continuous (fun p : ℝ × SobolevSpace period q => heatFlow period q ν p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × SobolevSpace period q => ((2 * ν * p.1).toNNReal, p.2)) :=
    (continuous_real_toNNReal.comp (continuous_const.mul continuous_fst)).prodMk continuous_snd
  exact Continuous.comp
    (g := fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2)
    (f := fun p : ℝ × SobolevSpace period q => ((2 * ν * p.1).toNNReal, p.2))
    (heatOperator_joint_continuous period q) hp

/-- The chosen real-time extension is exactly the identity at nonpositive times. -/
theorem heatFlow_nonpositive {q : ℕ} (ν : ℝ) (hν : 0 < ν) (t : ℝ) (ht : t ≤ 0)
    (u : SobolevSpace period q) : heatFlow period q ν t u = u := by
  rw [heatFlow, Real.toNNReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by
      positivity) ht), heatOperator_zero]

/-- At negative times the actual clamped heat orbit has zero L² derivative. -/
theorem heatFlow_value_hasDerivAt_negative {q : ℕ} (ν : ℝ) (hν : 0 < ν)
    (u : SobolevSpace period q) (t : ℝ) (ht : t < 0) :
    HasDerivAt (fun s => value period (heatFlow period q ν s u)) 0 t := by
  apply (hasDerivAt_const t (value period u)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  rw [heatFlow_nonpositive period ν hν s hs.le]

/-- The full fixed-interval heat integrand is continuous, with the source path extended by clamping.
-/
theorem shiftedHeat_continuous {q : ℕ} (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    Continuous (fun s : ℝ => heatFlow period q ν (t - s) (extendPath T hT f s)) := by
  have hp : Continuous (fun s : ℝ => (t - s, extendPath T hT f s)) :=
    (continuous_const.sub continuous_id).prodMk (extendPath_continuous T hT f)
  exact Continuous.comp
    (g := fun p : ℝ × SobolevSpace period q => heatFlow period q ν p.1 p.2)
    (f := fun s : ℝ => (t - s, extendPath T hT f s)) (heatFlow_joint_continuous period q ν) hp

/-- The ordinary, actual Sobolev heat Duhamel integral. -/
def duhamel {q : ℕ} (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) : SobolevSpace period q :=
  ∫ s in (0 : ℝ)..t, heatFlow period q ν (t - s) (extendPath T hT f s)

/-- A fixed-interval heat integral whose L² derivative can be taken under the integral sign. -/
def fullDuhamel {q : ℕ} (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) : SobolevSpace period q :=
  ∫ s in (0 : ℝ)..T, heatFlow period q ν (t - s) (extendPath T hT f s)

/-- The underlying L² full integral is the genuine Bochner integral of the underlying heat fields.
-/
theorem fullDuhamel_value {q : ℕ} (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    value period (fullDuhamel period ν T hT f t) =
      ∫ s in Ioc 0 T, value period (heatFlow period q ν (t - s) (extendPath T hT f s)) := by
  change (valueOperator period q) (∫ s in (0 : ℝ)..T,
    heatFlow period q ν (t - s) (extendPath T hT f s)) = _
  rw [← (valueOperator period q).intervalIntegral_comp_comm ((shiftedHeat_continuous period ν T hT
      f t).intervalIntegrable 0 T),
    intervalIntegral.integral_of_le hT]
  rfl

/-- The actual parameter derivative of the full heat integrand away from its measure-zero diagonal.
-/
def derivativeIntegrand {q : ℕ} (hq : 2 ≤ q) (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t s : ℝ) : LiftL2 period :=
  (Iic t).indicator (fun s => ν • laplacianEvaluation period q hq
    (heatFlow period q ν (t - s) (extendPath T hT f s))) s

/-- The actual parameter derivative is measurable despite its jump across the time diagonal. -/
theorem derivativeIntegrand_measurable {q : ℕ} (hq : 2 ≤ q) (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    AEStronglyMeasurable (derivativeIntegrand period hq ν T hT f t) (volume.restrict (Ioc 0 T)) :=
        by
  have hc : Continuous (fun s => ν • laplacianEvaluation period q hq
      (heatFlow period q ν (t - s) (extendPath T hT f s))) :=
    ((laplacianEvaluation period q hq).continuous.comp (shiftedHeat_continuous period ν T hT f
        t)).const_smul ν
  exact hc.aestronglyMeasurable.indicator measurableSet_Iic

/-- The full integrand is uniformly Lipschitz in time in L², using two genuine source derivatives.
-/
theorem shiftedHeat_value_lipschitz {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (r : ℝ) :
    LipschitzWith (Real.nnabs (4 * ν * ‖f‖))
      (fun t : ℝ => value period (heatFlow period q ν (t - r) (extendPath T hT f r))) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (by positivity : 0 ≤ 4 * ν * ‖f‖)]
  have h := heatFlow_value_norm_sub_le period hq ν hν (extendPath T hT f r) (s - r) (t - r)
  rw [show (s - r) - (t - r) = s - t by ring] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (extendPath_norm_le T hT f r) (by
        positivity : 0 ≤ 4 * ν)) (abs_nonneg _))

/-- The actual off-diagonal parameter derivative is the positive-time heat Laplacian and zero before
the source time. -/
theorem shiftedHeat_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (t s : ℝ) (hst : s ≠ t) :
    HasDerivAt (fun r => value period (heatFlow period q ν (r - s) (extendPath T hT f s)))
      (derivativeIntegrand period hq ν T hT f t s) t := by
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hd := (heatFlow_value_hasDerivAt period hq ν hν (extendPath T hT f s) (t - s) (sub_pos.mpr
      hst)).scomp t
      ((hasDerivAt_id t).sub_const s)
    simpa only [derivativeIntegrand, indicator, mem_Iic, hst.le, ite_true, one_smul,
        Function.comp_def, id_eq] using hd
  · have hd := (heatFlow_value_hasDerivAt_negative period ν hν (extendPath T hT f s) (t - s)
      (sub_neg.mpr hts)).scomp t
      ((hasDerivAt_id t).sub_const s)
    simpa only [derivativeIntegrand, indicator, mem_Iic, not_le.mpr hts, ite_false, smul_zero,
        Function.comp_def, id_eq] using hd

/-- Differentiation under the actual Bochner integral gives the L² derivative of the fixed-interval
heat convolution. -/
theorem fullDuhamel_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    HasDerivAt (fun r => value period (fullDuhamel period ν T hT f r))
      (∫ s in Ioc 0 T, derivativeIntegrand period hq ν T hT f t s) t := by
  have hmeas (r : ℝ) : AEStronglyMeasurable
      (fun s => value period (heatFlow period q ν (r - s) (extendPath T hT f s)))
      (volume.restrict (Ioc 0 T)) :=
    ((valueOperator period q).continuous.comp (shiftedHeat_continuous period ν T hT f
        r)).aestronglyMeasurable
  have hint : Integrable (fun s => value period (heatFlow period q ν (t - s) (extendPath T hT f s)))
      (volume.restrict (Ioc 0 T)) := by
    apply Integrable.of_bound (hmeas t) ‖f‖
    exact Filter.Eventually.of_forall fun s =>
      (value_norm_le period _).trans ((heatOperator_bound period _ _).trans (extendPath_norm_le T
          hT f s))
  have hdiff : ∀ᵐ s : ℝ ∂volume.restrict (Ioc 0 T),
      HasDerivAt (fun r => value period (heatFlow period q ν (r - s) (extendPath T hT f s)))
        (derivativeIntegrand period hq ν T hT f t s) t := by
    have hne : ∀ᵐ s : ℝ ∂volume.restrict (Ioc 0 T), s ≠ t :=
      compl_mem_ae_iff.mpr (measure_singleton _)
    exact hne.mono fun s hs => shiftedHeat_value_hasDerivAt period hq ν hν T hT f t s hs
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip (s := univ) (bound := fun _ : ℝ => 4 * ν *
      ‖f‖)
    (μ := volume.restrict (Ioc 0 T)) Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint
    (derivativeIntegrand_measurable period hq ν T hT f t)
    (Filter.Eventually.of_forall fun s => (shiftedHeat_value_lipschitz period hq ν hν T hT f
        s).lipschitzOnWith)
    (integrable_const _) hdiff).2
  have he : (fun r => value period (fullDuhamel period ν T hT f r)) =
      fun r => ∫ s in Ioc 0 T, value period (heatFlow period q ν (r - s) (extendPath T hT f s)) :=
          by
    funext r
    exact fullDuhamel_value period ν T hT f r
  rw [he]
  exact h

end EulerDuhamelDifferentiation
