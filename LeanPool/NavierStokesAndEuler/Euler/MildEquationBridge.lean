/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DuhamelEquation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatVolterra

@[expose] public section

/-! The constructed gained-derivative heat fixed point satisfies the actual differential PDE in L².
  -/

noncomputable section

namespace EulerMildEquationBridge

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution EulerDuhamelDifferentiation
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Ordinary Sobolev heat commutes with forgetting the highest derivative level. -/
theorem truncate_heatOperator {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (heatOperator period (q + 1) v u) =
      heatOperator period q v (truncateOperator period q u) := by
  apply value_injective period
  simp only [value_truncateOperator, heatOperator_value]

/-- The actual Laplacian agrees under Sobolev truncation whenever both sides have two derivatives. -/
theorem laplacian_truncate {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period (q + 1)) :
    laplacianEvaluation period q hq (truncateOperator period q u) =
      laplacianEvaluation period (q + 1) (Nat.le_trans hq (Nat.le_succ q)) u := by
  rw [laplacianEvaluation_apply, laplacianEvaluation_apply]
  rfl

/-- Forgetting the gained derivative of the genuine positive-time heat kernel gives the ordinary heat flow. -/
theorem truncate_heatKernel {q : ℕ} (ν : ℝ) (hν : 0 < ν) (r : ℝ) (hr : 0 < r)
    (u : SobolevSpace period q) :
    truncateOperator period q (heatKernel period q ν hν r u) = heatFlow period q ν r u := by
  rw [heatKernel, dite_eq_left hr]
  let v : ℝ≥0 := ⟨2 * ν * r, by positivity⟩
  have hv : 0 < v := by change (0 : ℝ) < 2 * ν * r; positivity
  have he : v = (2 * ν * r).toNNReal := by
    apply Subtype.ext
    simp only [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2 * ν * r)]
    rfl
  exact (truncate_heatGain period v hv u).trans (congrArg (fun v => heatOperator period q v u) he)

/-- The genuine singular gained-derivative convolution becomes the ordinary Duhamel integral after truncation. -/
theorem truncate_heatConvolution {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    truncateOperator period q
      (convolution T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
        (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
        (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
        (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t) =
      duhamel period ν T hT f t.val := by
  let L := truncateOperator period q
  change L (∫ r in Ioc 0 T, causalIntegrand T hT (heatKernel period q ν hν) f t r) = _
  rw [← L.integral_comp_comm (causalIntegrand_integrable T hT (heatKernel period q ν hν)
    (parabolicKernelBound ν) (heatKernel_joint_continuous period q ν hν)
    (parabolicKernelBound_integrable ν T hT) (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t)]
  have he : (∫ r in Ioc 0 T, L (causalIntegrand T hT (heatKernel period q ν hν) f t r)) =
      ∫ r in Ioc 0 T, (Iic t.val).indicator (fun r => heatFlow period q ν r (extendPath T hT f
        (t.val - r))) r := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    by_cases hrt : r ≤ t.val
    · simp only [causalIntegrand, indicator, mem_Iic, hrt, ite_true]
      exact truncate_heatKernel period ν hν r hr.1 _
    · simp only [causalIntegrand, indicator, mem_Iic, hrt, ite_false, map_zero]
  rw [he, ← intervalIntegral.integral_of_le hT]
  calc
    _ = ∫ r in (0 : ℝ)..t.val, heatFlow period q ν r (extendPath T hT f (t.val - r)) :=
      intervalIntegral.integral_indicator t.property
    _ = duhamel period ν T hT f t.val := by
      have hs := intervalIntegral.integral_comp_sub_left
        (fun s => heatFlow period q ν (t.val - s) (extendPath T hT f s)) t.val (a := 0) (b := t.val)
      simpa only [sub_sub_cancel, sub_self, sub_zero, duhamel] using hs

/-- A continuous Sobolev path satisfying the actual ordinary Duhamel formula solves the inhomogeneous L² equation. -/
theorem ordinary_mild_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period q)
    (f u : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hsol : ∀ t : Icc (0 : ℝ) T, u t = heatFlow period q ν t.val u₀ + duhamel period ν T hT f t.val)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT u r))
      (ν • laplacianEvaluation period q hq (u ⟨t, ht.1.le, ht.2.le⟩) +
        value period (f ⟨t, ht.1.le, ht.2.le⟩)) t := by
  have hd := inhomogeneous_heat_value_hasDerivAt period hq ν hν T hT f u₀ t ht
  rw [← hsol ⟨t, ht.1.le, ht.2.le⟩] at hd
  have hf : extendPath T hT f t = f ⟨t, ht.1.le, ht.2.le⟩ := by
    exact congrArg f (projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩)
  rw [hf] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  have he : extendPath T hT u r = u ⟨r, hr.1.le, hr.2.le⟩ :=
    congrArg u (projIcc_of_mem hT ⟨hr.1.le, hr.2.le⟩)
  rw [he, hsol]

/-- Every actual gained-derivative viscous mild solution satisfies u′=νΔu+F(t,u) in L² at interior times. -/
theorem viscous_mild_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period (q + 1))
    (F : Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT u r))
      (ν • laplacianEvaluation period (q + 1) (Nat.le_trans hq (Nat.le_succ q))
          (u ⟨t, ht.1.le, ht.2.le⟩) + value period (F ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le,
            ht.2.le⟩))) t := by
  let f := pathNonlinearity T F hF u
  let v : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
    ⟨fun s => truncateOperator period q (u s), (truncateOperator period q).continuous.comp
      u.continuous⟩
  have hv : ∀ s : Icc (0 : ℝ) T, v s =
      heatFlow period q ν s.val (truncateOperator period q u₀) + duhamel period ν T hT f s.val := by
    intro s
    have hc := truncate_heatConvolution period ν hν T hT f s
    rw [convolution_eq_interval T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
      (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
      (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
      (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f s] at hc
    change truncateOperator period q (u s) = _
    rw [hsol s, map_add, truncate_heatOperator]
    change heatFlow period q ν s.val (truncateOperator period q u₀) +
      truncateOperator period q (∫ r in (0 : ℝ)..s.val,
        heatKernel period q ν hν r (extendPath T hT f (s.val - r))) = _
    rw [hc]
  have hd := ordinary_mild_hasDerivAt period hq ν hν T hT (truncateOperator period q u₀) f v hv t ht
  change HasDerivAt (fun r => value period (truncateOperator period q (extendPath T hT u r)))
    (ν • laplacianEvaluation period q hq (truncateOperator period q (u ⟨t, ht.1.le, ht.2.le⟩)) +
      value period (F ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩))) t at hd
  simpa only [value_truncateOperator, laplacian_truncate] using hd

end EulerMildEquationBridge
