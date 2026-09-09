/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel
import LeanPool.NavierStokesAndEuler.Euler.VolterraFixedPoint

/-! The actual cylinder heat kernel in the singular Volterra existence theorem. -/

@[expose] public section


noncomputable section

namespace EulerSobolevHeat

open EulerCylinderSobolevSpace EulerVolterraConvolution EulerGaussianCylinderHeat MeasureTheory Set
open scoped Topology NNReal

/-- Positive physical time converted to positive Gaussian variance for viscosity ν. -/
def positiveVariance (ν : ℝ) (hν : 0 < ν) (t : {t : ℝ // 0 < t}) : {v : ℝ≥0 // 0 < v} :=
  ⟨⟨2 * ν * t.val, by have ht := t.property; positivity⟩,
    by change (0 : ℝ) < 2 * ν * t.val; have ht := t.property; positivity⟩

/-- Physical time to Gaussian variance is continuous on positive times. -/
theorem positiveVariance_continuous (ν : ℝ) (hν : 0 < ν) : Continuous (positiveVariance ν hν) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

variable (period : ℝ) [Fact (0 < period)]

/-- The actual one-derivative heat kernel is jointly continuous at every positive physical time. -/
theorem heatKernel_joint_continuous (q : ℕ) (ν : ℝ) (hν : 0 < ν) :
    ContinuousOn (fun p : ℝ × SobolevSpace period q => heatKernel period q ν hν p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set (SobolevSpace period q))) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {p : ℝ × SobolevSpace period q // p ∈ Ioi 0 ×ˢ (univ : Set (SobolevSpace period q))}
  let τ : P → {t : ℝ // 0 < t} := fun p => ⟨p.val.1, p.property.1⟩
  have hτ : Continuous τ := Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  let Φ : P → {v : ℝ≥0 // 0 < v} × SobolevSpace period q :=
    fun p => (positiveVariance ν hν (τ p), p.val.2)
  have hΦ : Continuous Φ := ((positiveVariance_continuous ν hν).comp hτ).prodMk
    (continuous_snd.comp continuous_subtype_val)
  have hh := Continuous.comp
    (g := fun p : {v : ℝ≥0 // 0 < v} × SobolevSpace period q =>
      heatGain period q p.1.val p.1.property p.2)
    (f := Φ) (heatGain_joint_continuous period q) hΦ
  convert hh using 1
  funext p
  change heatKernel period q ν hν p.val.1 p.val.2 = _
  have ht : 0 < p.val.1 := p.property.1
  rw [heatKernel, dite_eq_left ht]
  rfl

/-- The free viscous heat evolution is an actual continuous path in every Sobolev space. -/
def freeHeatPath (q : ℕ) (ν T : ℝ) (u₀ : SobolevSpace period q) : C(Icc (0 : ℝ) T, SobolevSpace
    period q) where
  toFun t := heatOperator period q (2 * ν * t.val).toNNReal u₀
  continuous_toFun := (heatOperator_continuous period u₀).comp
    (continuous_real_toNNReal.comp (continuous_const.mul continuous_subtype_val))

/-- The free heat path obeys the initial-data bound in the actual uniform Sobolev norm. -/
theorem freeHeatPath_bound (q : ℕ) (ν T : ℝ) (u₀ : SobolevSpace period q) :
    ‖freeHeatPath period q ν T u₀‖ ≤ ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u₀)).mpr
  intro t
  exact heatOperator_bound period _ u₀

/-- The actual viscous heat equation has a local mild solution for every continuous locally
Lipschitz derivative-losing source satisfying the explicit time budget. -/
theorem exists_viscous_mild_solution (q : ℕ) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1))
    (F : Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (R M L : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hFM : ∀ t x, ‖x‖ ≤ R → ‖F t x‖ ≤ M)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (hbudget : ‖u₀‖ + (T + 2 * parabolicConstant ν * Real.sqrt T) * M ≤ R)
    (hsmall : (T + 2 * parabolicConstant ν * Real.sqrt T) * L < 1) :
    ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)), ‖u‖ ≤ R ∧
      ∀ t : Icc (0 : ℝ) T,
        u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
          ∫ r in (0 : ℝ)..t.val,
            heatKernel period q ν hν r
              (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))) := by
  have hmass : kernelMass T (parabolicKernelBound ν) = T + 2 * parabolicConstant ν * Real.sqrt T :=
    parabolicKernelBound_integral ν T hT
  apply exists_mild_solution T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y)
    (freeHeatPath period (q + 1) ν T u₀) F hF R M L hR hM hL hFM hFL
  · rw [hmass]
    have hf := freeHeatPath_bound period (q + 1) ν T u₀
    linarith
  · rwa [hmass]

end EulerSobolevHeat
