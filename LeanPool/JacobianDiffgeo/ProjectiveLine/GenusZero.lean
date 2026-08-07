/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
import LeanPool.JacobianDiffgeo.Forms
import Mathlib.Analysis.Complex.Liouville

/-!
# `genus (OnePoint ℂ) = 0` (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.5, proof plan P8). The coefficients
of a holomorphic 1-form on `ℙ¹`, read in `coeChart` and `invChart`, are entire functions `f`, `g`
related by `f z = -(z ^ 2)⁻¹ * g z⁻¹` for `z ≠ 0`. Since `g` is bounded near `0` (continuity), `f`
decays to `0` at infinity, hence vanishes identically by Liouville; the same transition rule then
forces `g ≡ 0`. So there are no nonzero holomorphic 1-forms on `ℙ¹` — the sphere has genus 0.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

/-- There are no nonzero holomorphic 1-forms on `ℙ¹` (Forster 5-adjacent; "the sphere has
genus 0"). -/
theorem form1_eq_zero (η : RS.Form1 (OnePoint ℂ)) : η = 0 := by
  -- Step 1: both chart coefficients are entire.
  have hf_an : AnalyticOnNhd ℂ (RS.coeffIn coeChart η) Set.univ := by
    have h := η.analyticOnNhd_coeffIn coeChart_mem_maximalAtlas
    rwa [coeChart_target] at h
  have hg_an : AnalyticOnNhd ℂ (RS.coeffIn invChart η) Set.univ := by
    have h := η.analyticOnNhd_coeffIn invChart_mem_maximalAtlas
    rwa [invChart_target] at h
  have hf_diff : Differentiable ℂ (RS.coeffIn coeChart η) :=
    fun z => (hf_an z (Set.mem_univ z)).differentiableAt
  have hg_cont : Continuous (RS.coeffIn invChart η) :=
    continuous_iff_continuousAt.2 fun z => (hg_an z (Set.mem_univ z)).continuousAt
  -- Step 2: the decay identity `f z = -(z ^ 2)⁻¹ * g z⁻¹` for `z ≠ 0`.
  have hdecay : ∀ z : ℂ, z ≠ 0 →
      RS.coeffIn coeChart η z = -(z ^ 2)⁻¹ * RS.coeffIn invChart η (z⁻¹) := by
    intro z hz
    have hzmem : (z : ℂ) ∈ ⇑coeChart '' (invChart.source ∩ coeChart.source) :=
      ⟨z, ⟨by rw [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe]; exact hz,
        by rw [coeChart_source]; simp⟩, coeChart_apply_coe z⟩
    have htrans := RS.coeffIn_trans invChart_mem_maximalAtlas coeChart_mem_maximalAtlas η hzmem
    have hderiv : deriv (⇑invChart ∘ ⇑coeChart.symm) z = -(z ^ 2)⁻¹ := by
      have hcompeq : (⇑invChart ∘ ⇑coeChart.symm : ℂ → ℂ) = Inv.inv := invChart_comp_coe
      rw [hcompeq]; exact deriv_inv
    have harg : invChart (coeChart.symm z) = z⁻¹ := by
      rw [coeChart_symm_apply]; exact invChart_apply_coe z
    rw [htrans, hderiv, harg]
  -- Step 3: `f → 0` along `cobounded ℂ`.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hg_cont.continuousOn
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  have hbound : ∀ᶠ z in Bornology.cobounded ℂ,
      ‖RS.coeffIn coeChart η z‖ ≤ M * (‖z‖ ^ 2)⁻¹ := by
    have hb : (Metric.closedBall (0 : ℂ) 1)ᶜ ∈ Bornology.cobounded ℂ :=
      Bornology.isBounded_def.mp Metric.isBounded_closedBall
    have hev : {z : ℂ | (1 : ℝ) ≤ ‖z‖} ∈ Bornology.cobounded ℂ := by
      refine Filter.mem_of_superset hb (fun z hz => ?_)
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
      exact le_of_lt hz
    filter_upwards [hev] with z hz1
    have hzne : z ≠ 0 := by
      intro h; rw [h] at hz1; norm_num at hz1
    have hzinv_le : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz1
    have hmem : z⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hzinv_le
    calc ‖RS.coeffIn coeChart η z‖
        = (‖z‖ ^ 2)⁻¹ * ‖RS.coeffIn invChart η (z⁻¹)‖ := by
          rw [hdecay z hzne, norm_mul, norm_neg, norm_inv, norm_pow]
      _ ≤ (‖z‖ ^ 2)⁻¹ * M := mul_le_mul_of_nonneg_left (hM _ hmem) (by positivity)
      _ = M * (‖z‖ ^ 2)⁻¹ := by ring
  have hsq_atTop : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_norm_cobounded_atTop
  have hinvsq_zero : Tendsto (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsq_atTop
  have hmul_zero : Tendsto (fun z : ℂ => M * (‖z‖ ^ 2)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa using hinvsq_zero.const_mul M
  have htendsto : Tendsto (RS.coeffIn coeChart η) (Bornology.cobounded ℂ) (𝓝 0) :=
    squeeze_zero_norm' hbound hmul_zero
  -- Step 4: Liouville forces `f ≡ 0`.
  rw [Metric.cobounded_eq_cocompact] at htendsto
  have hf_zero : RS.coeffIn coeChart η = Function.const ℂ 0 :=
    hf_diff.eq_const_of_tendsto_cocompact htendsto
  -- Step 5: transport back through the same transition rule to get `g ≡ 0`.
  have hg_zero_ne : ∀ w : ℂ, w ≠ 0 → RS.coeffIn invChart η w = 0 := by
    intro w hw
    have hwmem : (w : ℂ) ∈ ⇑invChart '' (coeChart.source ∩ invChart.source) :=
      ⟨((w⁻¹ : ℂ) : OnePoint ℂ),
        ⟨by rw [coeChart_source]; simp,
          by rw [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe]
             exact inv_ne_zero hw⟩,
        (invChart_apply_coe (w⁻¹)).trans (inv_inv w)⟩
    have htrans2 := RS.coeffIn_trans coeChart_mem_maximalAtlas invChart_mem_maximalAtlas η hwmem
    have hzero : RS.coeffIn coeChart η (coeChart (invChart.symm w)) = 0 := by
      rw [hf_zero]; rfl
    rw [htrans2, hzero, mul_zero]
  have hg_zero : RS.coeffIn invChart η = Function.const ℂ 0 := by
    funext w
    by_cases hw : w = 0
    · subst hw
      have heq : (RS.coeffIn invChart η) =ᶠ[𝓝[≠] (0 : ℂ)] (Function.const ℂ 0) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hg_zero_ne y hy
      have hlim : Tendsto (RS.coeffIn invChart η) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        rw [tendsto_congr' heq]; exact tendsto_const_nhds
      have hcont0 : Tendsto (RS.coeffIn invChart η) (𝓝[≠] (0 : ℂ))
          (𝓝 (RS.coeffIn invChart η 0)) :=
        Filter.Tendsto.mono_left hg_cont.continuousAt nhdsWithin_le_nhds
      exact tendsto_nhds_unique hcont0 hlim
    · exact hg_zero_ne w hw
  -- Step 6: assemble `η = 0` from the vanishing preferred-chart coefficients.
  have hcoeffAt : ∀ x : OnePoint ℂ, RS.coeffAt x η = 0 := by
    intro x
    induction x using OnePoint.rec with
    | infty =>
      change RS.coeffIn (chartAt ℂ (∞ : OnePoint ℂ)) η (chartAt ℂ (∞ : OnePoint ℂ) ∞) = 0
      rw [chartAt_infty, invChart_apply_infty]
      exact congrFun hg_zero 0
    | coe z =>
      change RS.coeffIn (chartAt ℂ ((z : ℂ) : OnePoint ℂ)) η
          (chartAt ℂ ((z : ℂ) : OnePoint ℂ) (z : OnePoint ℂ)) = 0
      rw [chartAt_coe, coeChart_apply_coe]
      exact congrFun hf_zero z
  exact RS.Form1.ext_coeffAt (fun x => by rw [hcoeffAt x, RS.coeffAt_zero])

instance : Subsingleton (RS.Form1 (OnePoint ℂ)) :=
  ⟨fun η η' => by rw [form1_eq_zero η, form1_eq_zero η']⟩

/-- `Module.finrank ℂ (RS.Form1 (OnePoint ℂ)) = 0`, i.e. the space of holomorphic 1-forms on
`ℙ¹` is trivial. -/
theorem finrank_form1 : Module.finrank ℂ (RS.Form1 (OnePoint ℂ)) = 0 :=
  Module.finrank_zero_of_subsingleton

end RS.P1

/-- `genus ℙ¹ = 0`: the Riemann sphere has genus zero. -/
theorem RS.genus_onePoint : genus (OnePoint ℂ) = 0 :=
  RS.P1.finrank_form1
