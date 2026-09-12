/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.FlowEscapeBound
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Finite-energy estimate for the radial homotopy operator

In three dimensions, the operator `u ↦ ∫₀¹ t • u(t • x) dt` has L² operator
norm at most two. The substitution `t = r²` reduces the estimate to ordinary
Cauchy--Schwarz and exactly cancels the Jacobian of dilation. Only continuity
and finite energy are needed; no derivative integrability is assumed.
-/

@[expose] public section


noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace Euler.ComparatorBridge

local notation "Space" => EuclideanSpace ℝ (Fin 3)

/-- A square substitution removes the singular weight in the radial estimate. -/
theorem radial_average_eq_quadratic (u : Space → Space) (hu : Continuous u) (x : Space) :
    (∫ t in (0 : ℝ)..1, t • u (t • x)) =
      ∫ r in (0 : ℝ)..1, (2 * r ^ 3) • u (r ^ 2 • x) := by
  have hd (r : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
    convert! (hasDerivAt_id r).pow 2 using 1
    simp
  have h := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r)
    (g := fun t => t • u (t • x)) (fun r _ => hd r)
    (by fun_prop) (by fun_prop)
  simp only [Function.comp_apply, zero_pow (by norm_num : 2 ≠ 0), one_pow,
    smul_smul] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show 2 * r * r ^ 2 = 2 * r ^ 3 by ring]

/-- Squared L² energy of a dilated field, with its compensating factor. -/
theorem quadratic_dilation_energy (u : Space → Space) {r : ℝ} (hr : r ≠ 0) :
    (∫ x : Space, ‖(2 * r ^ 3) • u (r ^ 2 • x)‖ ^ 2) =
      4 * (∫ x : Space, ‖u x‖ ^ 2) := by
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ‖u x‖ ^ 2)
      (r ^ 2) (hR := sq_nonneg r)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp
  ring

/-- The quadratic parametrization has finite total action, exactly four times
that of the original field. -/
theorem quadratic_radial_action (u : Space → Space) (hu : Continuous u)
    (hL2 : MemLp u 2) :
    Integrable (fun x : Space => ∫ r in Ioc (0 : ℝ) 1,
      ‖(2 * r ^ 3) • u (r ^ 2 • x)‖ ^ 2) ∧
    (∫ x : Space, ∫ r in Ioc (0 : ℝ) 1,
      ‖(2 * r ^ 3) • u (r ^ 2 • x)‖ ^ 2) =
        4 * (∫ x : Space, ‖u x‖ ^ 2) := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let W : ℝ → Space → Space := fun r x => (2 * r ^ 3) • u (r ^ 2 • x)
  have hm : AEStronglyMeasurable (fun rx : ℝ × Space => ‖W rx.1 rx.2‖ ^ 2)
      (ν.prod volume) := by
    have hc : Continuous (fun rx : ℝ × Space => ‖W rx.1 rx.2‖ ^ 2) := by
      dsimp [W]
      fun_prop
    exact hc.aestronglyMeasurable
  have hE : Integrable (fun x : Space => ‖u x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  have henergy : (fun r : ℝ => ∫ x : Space, ‖W r x‖ ^ 2) =ᵐ[ν]
      fun _ => 4 * (∫ x : Space, ‖u x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact quadratic_dilation_energy u (ne_of_gt hr.1)
  have houter : Integrable (fun r : ℝ => ∫ x : Space, ‖W r x‖ ^ 2) ν :=
    (integrable_const _).congr henergy.symm
  have hprod : Integrable (fun rx : ℝ × Space => ‖W rx.1 rx.2‖ ^ 2)
      (ν.prod volume) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      dsimp [W]
      simp_rw [norm_smul, mul_pow]
      exact (hE.comp_smul (pow_ne_zero 2 (ne_of_gt hr.1))).const_mul _
    · simpa only [norm_pow, norm_norm] using houter
  refine ⟨hprod.integral_prod_right, ?_⟩
  calc
    (∫ x : Space, ∫ r, ‖W r x‖ ^ 2 ∂ν) =
        ∫ r, (∫ x : Space, ‖W r x‖ ^ 2) ∂ν := (integral_integral_swap hprod).symm
    _ = ∫ _ : ℝ, 4 * (∫ x : Space, ‖u x‖ ^ 2) ∂ν := integral_congr_ae henergy
    _ = 4 * (∫ x : Space, ‖u x‖ ^ 2) := by
      simp [ν]

/-- Pointwise Cauchy--Schwarz for the regularized radial parametrization. -/
theorem radial_average_sq_le_action (u : Space → Space) (hu : Continuous u) (x : Space) :
    ‖∫ t in (0 : ℝ)..1, t • u (t • x)‖ ^ 2 ≤
      ∫ r in Ioc (0 : ℝ) 1, ‖(2 * r ^ 3) • u (r ^ 2 • x)‖ ^ 2 := by
  let W : ℝ → Space := fun r => (2 * r ^ 3) • u (r ^ 2 • x)
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hmem : MemLp W 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mpr
    exact ((hW.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h := norm_integral_sq_le_action (volume.restrict (Ioc (0 : ℝ) 1)) W hmem
  rw [radial_average_eq_quadratic u hu x,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa [W] using h

/-- The radial homotopy average preserves L², with operator norm at most two. -/
theorem radial_average_memLp_and_energy (u : Space → Space) (hu : Continuous u)
    (hL2 : MemLp u 2) :
    MemLp (fun x => ∫ t in (0 : ℝ)..1, t • u (t • x)) 2 ∧
    (∫ x : Space, ‖∫ t in (0 : ℝ)..1, t • u (t • x)‖ ^ 2) ≤
      4 * (∫ x : Space, ‖u x‖ ^ 2) := by
  obtain ⟨hact, henergy⟩ := quadratic_radial_action u hu hL2
  have hm : AEStronglyMeasurable (fun x : Space => ∫ t in (0 : ℝ)..1, t • u (t • x)) := by
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun tx : ℝ × Space => tx.1 • u (tx.1 • tx.2)) := by fun_prop
    exact hc.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hb := radial_average_sq_le_action u hu
  have hint : Integrable (fun x : Space => ‖∫ t in (0 : ℝ)..1, t • u (t • x)‖ ^ 2) := by
    apply hact.mono' (hm.norm.pow 2)
    exact Eventually.of_forall (fun x => by
        simpa only [Pi.pow_apply, norm_pow, norm_norm] using hb x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hint, ?_⟩
  exact (integral_mono hint hact hb).trans_eq henergy


end Euler.ComparatorBridge
