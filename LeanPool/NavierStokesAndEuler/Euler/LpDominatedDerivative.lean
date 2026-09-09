/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeMap
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import LeanPool.NavierStokesAndEuler.Euler.LpDominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Positivity.Finset

/-! Differentiating an actual L²-valued family by dominated ordinary derivatives. -/

@[expose] public section


noncomputable section


namespace EulerLpDerivative

open MeasureTheory Filter
open scoped Topology

variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X)

/-- A pointwise derivative and a square-integrable increment bound give a genuine L² Fréchet
derivative. -/
theorem hasFDerivAt_of_dominated (U : P → Lp V 2 μ) (F : P → X → V)
    (hU : ∀ a, U a =ᵐ[μ] F a) (D : Lp (P →L[ℝ] V) 2 μ)
    (hpoint : ∀ᵐ x ∂μ, HasFDerivAt (fun a => F a x) (D x) 0)
    (M : X → ℝ) (hM : MemLp M 2 μ) (hM0 : ∀ᵐ x ∂μ, 0 ≤ M x)
    (hbound : ∀ᶠ a in 𝓝 (0 : P), ∀ᵐ x ∂μ, ‖F a x - F 0 x‖ ≤ M x * ‖a‖) :
    HasFDerivAt U (derivativeMap μ D) 0 := by
  let R : P → Lp V 2 μ := fun a => ‖a‖⁻¹ • (U a-U 0-derivativeMap μ D a)
  let r : P → X → V := fun a x => ‖a‖⁻¹ • (F a x-F 0 x-D x a)
  have hr (a : P) : R a =ᵐ[μ] r a := by
    filter_upwards [Lp.coeFn_smul (‖a‖⁻¹) (U a-U 0-derivativeMap μ D a),
      Lp.coeFn_sub (U a-U 0) (derivativeMap μ D a), Lp.coeFn_sub (U a) (U 0),
      hU a, hU 0, derivativeMap_ae μ D a] with x hs hss hsub ha hzero hd
    change (‖a‖⁻¹ • (U a-U 0-derivativeMap μ D a)) x = _
    simp only [Pi.smul_apply, Pi.sub_apply] at hs hss hsub
    rw [hs]
    rw [hss, hsub, ha, hzero, hd]
  have hzero : (0 : Lp V 2 μ) =ᵐ[μ] (fun _ : X => (0 : V)) := Lp.coeFn_zero V 2 μ
  have hconv : Tendsto R (𝓝 (0 : P)) (𝓝 (0 : Lp V 2 μ)) := by
    apply EulerLpConvergence.tendsto_of_dominated μ R 0 r (fun _ => 0) hr hzero
      (fun x => M x + ‖D x‖) (hM.add (Lp.memLp D).norm)
    · filter_upwards [hbound] with a ha
      filter_upwards [ha, hM0] with x hx hm
      rw [sub_zero]
      change ‖‖a‖⁻¹ • (F a x-F 0 x-D x a)‖ ≤ M x+‖D x‖
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a))]
      by_cases hz : ‖a‖ = 0
      · simp only [hz, inv_zero, zero_mul]
        exact add_nonneg hm (norm_nonneg _)
      · calc
          _ ≤ ‖a‖⁻¹ * (‖F a x-F 0 x‖+‖D x a‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (norm_nonneg a))
          _ ≤ ‖a‖⁻¹ * (M x*‖a‖+‖D x‖*‖a‖) :=
            mul_le_mul_of_nonneg_left (add_le_add hx ((D x).le_opNorm a))
              (inv_nonneg.mpr (norm_nonneg a))
          _ = M x+‖D x‖ := by field_simp
    · filter_upwards [hpoint] with x hx
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h := hasFDerivAt_iff_tendsto.mp hx
      simpa only [r, sub_zero, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using h
  apply hasFDerivAt_iff_tendsto.mpr
  have hn := hconv.norm
  simpa only [R, sub_zero, norm_smul, norm_zero,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using hn

end EulerLpDerivative
