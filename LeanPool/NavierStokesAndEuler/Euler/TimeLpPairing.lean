/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Positivity.Finset

/-! Actual integral pairings and their strong limits for metric energy passage. -/

@[expose] public section


noncomputable section

namespace EulerTimeLpPairing

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution
open scoped Topology

/-- The actual scalar Bochner inner product is the integral of the literal product. -/
theorem inner_eq_integral (T : ℝ) (a b : TimeLp T ℝ) :
    ⟪a, b⟫_ℝ = ∫ t, a t*b t ∂timeMeasure T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by simp [RCLike.inner_apply, mul_comm]

/-- Continuous-path Bochner pairings equal the ordinary interval integral. -/
theorem path_inner_eq_integral (T : ℝ) (hT : 0 ≤ T) (a b : C(Icc (0 : ℝ) T, ℝ)) :
    ⟪pathLp T hT a, pathLp T hT b⟫_ℝ =
      ∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT b t := by
  rw [inner_eq_integral]
  have he : (∫ t, pathLp T hT a t*pathLp T hT b t ∂timeMeasure T) =
      ∫ t in Icc 0 T, extendPath T hT a t * extendPath T hT b t := by
    apply integral_congr_ae
    filter_upwards [pathLp_ae T hT a, pathLp_ae T hT b] with t h1 h2
    rw [h1, h2]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]

/-- Signed integral coefficients pass continuously through uniform scalar energy convergence. -/
theorem integral_product_path_tendsto (T : ℝ) (hT : 0 ≤ T) (a : C(Icc (0 : ℝ) T, ℝ))
    (f : ℕ → C(Icc (0 : ℝ) T, ℝ)) (g : C(Icc (0 : ℝ) T, ℝ))
    (hf : Filter.Tendsto f Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => ∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT (f n) t)
      Filter.atTop (𝓝 (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT g t)) := by
  have h : Filter.Tendsto (fun n => ⟪pathLp T hT a, pathLp T hT (f n)⟫_ℝ) Filter.atTop
      (𝓝 ⟪pathLp T hT a, pathLp T hT g⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds (pathLp_tendsto T hT f g hf)
  simpa only [path_inner_eq_integral] using h

/-- Strong Bochner convergence passes signed scalar weighted integrals to their actual limit. -/
theorem integral_product_timeLp_tendsto (T : ℝ) (a : TimeLp T ℝ)
    (f : ℕ → TimeLp T ℝ) (g : TimeLp T ℝ)
    (hf : Filter.Tendsto f Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => ∫ t, a t*f n t ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ t, a t*g t ∂timeMeasure T)) := by
  have h : Filter.Tendsto (fun n => ⟪a, f n⟫_ℝ) Filter.atTop (𝓝 ⟪a, g⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds hf
  simpa only [inner_eq_integral] using h

/-- Three continuous weighted scalar paths have the literal additive interval integral. -/
theorem integral_three_paths (T : ℝ) (hT : 0 ≤ T)
    (a b c x y f : C(Icc (0 : ℝ) T, ℝ)) :
    (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT x t +
      extendPath T hT b t * extendPath T hT y t + extendPath T hT c t * extendPath T hT f t) =
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT x t) +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT y t) +
      ∫ t in (0 : ℝ)..T, extendPath T hT c t * extendPath T hT f t := by
  have ha := ((extendPath_continuous T hT a).mul (extendPath_continuous T hT x)).intervalIntegrable
      (μ := volume) 0 T
  have hb := ((extendPath_continuous T hT b).mul (extendPath_continuous T hT y)).intervalIntegrable
      (μ := volume) 0 T
  have hc := ((extendPath_continuous T hT c).mul (extendPath_continuous T hT f)).intervalIntegrable
      (μ := volume) 0 T
  change IntervalIntegrable (fun t => extendPath T hT a t * extendPath T hT x t) volume 0 T at ha
  change IntervalIntegrable (fun t => extendPath T hT b t * extendPath T hT y t) volume 0 T at hb
  change IntervalIntegrable (fun t => extendPath T hT c t * extendPath T hT f t) volume 0 T at hc
  rw [intervalIntegral.integral_add (ha.add hb) hc, intervalIntegral.integral_add ha hb]

/-- An actual integral energy inequality survives uniform state convergence and strong L² forcing
convergence, with the signed loss term unchanged. -/
theorem integral_energy_limit (T : ℝ) (hT : 0 ≤ T)
    (a b : C(Icc (0 : ℝ) T, ℝ)) (c : TimeLp T ℝ)
    (X Y : ℕ → C(Icc (0 : ℝ) T, ℝ)) (F : ℕ → TimeLp T ℝ)
    (x y : C(Icc (0 : ℝ) T, ℝ)) (f : TimeLp T ℝ)
    (hX : Filter.Tendsto X Filter.atTop (𝓝 x)) (hY : Filter.Tendsto Y Filter.atTop (𝓝 y))
    (hF : Filter.Tendsto F Filter.atTop (𝓝 f))
    (henergy : ∀ n, X n ⟨T, hT, le_rfl⟩ - X n ⟨0, le_rfl, hT⟩ ≤
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT (X n) t) +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT (Y n) t) +
      ∫ t, c t * F n t ∂timeMeasure T) :
    x ⟨T, hT, le_rfl⟩ - x ⟨0, le_rfl, hT⟩ ≤
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT x t) +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT y t) +
      ∫ t, c t * f t ∂timeMeasure T := by
  have ht := (continuous_eval_const (⟨T, hT, le_rfl⟩ : Icc (0 : ℝ) T)).continuousAt.tendsto.comp hX
  have h0 := (continuous_eval_const (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T)).continuousAt.tendsto.comp hX
  exact le_of_tendsto_of_tendsto' (ht.sub h0)
    (((integral_product_path_tendsto T hT a X x hX).add
      (integral_product_path_tendsto T hT b Y y hY)).add
      (integral_product_timeLp_tendsto T c F f hF)) henergy

end EulerTimeLpPairing
