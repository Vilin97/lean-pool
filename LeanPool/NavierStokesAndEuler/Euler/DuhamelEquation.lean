/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DuhamelDifferentiation

/-! The actual heat Duhamel integral satisfies the inhomogeneous equation in L². -/

@[expose] public section


noncomputable section

namespace EulerDuhamelDifferentiation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The causal Duhamel integral is the full clamped heat integral minus the unevolved source tail.
-/
theorem duhamel_eq_full_sub_tail {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    duhamel period ν T hT f t = fullDuhamel period ν T hT f t - ∫ s in t..T, extendPath T hT f s :=
        by
  have hc := shiftedHeat_continuous period ν T hT f t
  have htail : (∫ s in t..T, heatFlow period q ν (t - s) (extendPath T hT f s)) =
      ∫ s in t..T, extendPath T hT f s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s hs
    rw [uIoc_of_le ht.2] at hs
    exact heatFlow_nonpositive period ν hν (t - s) (sub_nonpos.mpr hs.1.le) _
  have h := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0
      t) (hc.intervalIntegrable (μ := volume) t T)
  rw [htail] at h
  exact eq_sub_iff_add_eq.mpr h

/-- The source tail has its genuine L² derivative by the fundamental theorem of calculus. -/
theorem source_tail_value_hasDerivAt {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    HasDerivAt (fun r => value period (∫ s in r..T, extendPath T hT f s))
      (-value period (extendPath T hT f t)) t := by
  have hc := (valueOperator period q).continuous.comp (extendPath_continuous T hT f)
  have hd := (hc.integral_hasStrictDerivAt T t).hasDerivAt.fun_neg
  have he : (fun r => value period (∫ s in r..T, extendPath T hT f s)) =
      fun r => -(∫ s in T..r, value period (extendPath T hT f s)) := by
    funext r
    change (valueOperator period q) (∫ s in r..T, extendPath T hT f s) = _
    rw [← (valueOperator period q).intervalIntegral_comp_comm ((extendPath_continuous T hT
        f).intervalIntegrable r T),
      intervalIntegral.integral_symm]
    rfl
  rw [he]
  exact hd

/-- The differentiated full convolution is the actual Laplacian of the causal Duhamel integral. -/
theorem derivativeIntegral_eq_laplacian {q : ℕ} (hq : 2 ≤ q) (ν T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ s in Ioc 0 T, derivativeIntegrand period hq ν T hT f t s) =
      ν • laplacianEvaluation period q hq (duhamel period ν T hT f t) := by
  rw [← intervalIntegral.integral_of_le hT]
  change (∫ s in (0 : ℝ)..T, (Iic t).indicator
    (fun s => ν • laplacianEvaluation period q hq (heatFlow period q ν (t - s) (extendPath T hT f
        s))) s) = _
  calc
    _ = ∫ s in (0 : ℝ)..t, ν • laplacianEvaluation period q hq
        (heatFlow period q ν (t - s) (extendPath T hT f s)) :=
      intervalIntegral.integral_indicator ht
    _ = _ := (ν • laplacianEvaluation period q hq).intervalIntegral_comp_comm
      ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable 0 t)

/-- The actual Sobolev Duhamel integral is differentiable in L² and solves w′=νΔw+f. -/
theorem duhamel_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (duhamel period ν T hT f r))
      (ν • laplacianEvaluation period q hq (duhamel period ν T hT f t) +
        value period (extendPath T hT f t)) t := by
  have hfull := fullDuhamel_value_hasDerivAt period hq ν hν T hT f t
  rw [derivativeIntegral_eq_laplacian period hq ν T hT f t ⟨ht.1.le, ht.2.le⟩] at hfull
  have htail := source_tail_value_hasDerivAt period T hT f t
  have hd := hfull.fun_sub htail
  simp only [sub_neg_eq_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  rw [duhamel_eq_full_sub_tail period ν hν T hT f r ⟨hr.1.le, hr.2.le⟩]
  rfl

/-- The genuine free heat plus Duhamel candidate satisfies the actual inhomogeneous L² PDE. -/
theorem inhomogeneous_heat_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u₀ : SobolevSpace period q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (heatFlow period q ν r u₀ + duhamel period ν T hT f r))
      (ν • laplacianEvaluation period q hq (heatFlow period q ν t u₀ + duhamel period ν T hT f t) +
        value period (extendPath T hT f t)) t := by
  have hh := heatFlow_value_hasDerivAt period hq ν hν u₀ t ht.1
  have hd := duhamel_value_hasDerivAt period hq ν hν T hT f t ht
  have h := hh.fun_add hd
  change HasDerivAt (fun r => value period (heatFlow period q ν r u₀) + value period (duhamel
      period ν T hT f r)) _ t
  simpa only [map_add, smul_add, add_assoc] using h

end EulerDuhamelDifferentiation
