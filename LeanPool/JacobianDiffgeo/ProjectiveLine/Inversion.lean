/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Inversion on the Riemann sphere (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.1). `ℙ¹ := OnePoint ℂ`.

This file defines `inversion : OnePoint ℂ → OnePoint ℂ`, the map `z ↦ z⁻¹` extended by
`∞ ↦ 0` and `0 ↦ ∞`, proves it is a continuous involution, and packages it as a
self-inverse homeomorphism `inversionHomeomorph`. The continuity proof is the `𝓝 ∞`
filter work referenced by the design's task brief ("verify `OnePoint.nhds_infty_eq`").

Main declarations: `inversion`, `inversion_involutive`, `inversion_eq_infty_iff`,
`tendsto_coe_cocompact`, `tendsto_coe_inv_nhdsNE_zero`, `continuous_inversion`,
`inversionHomeomorph`.
-/

open scoped OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

/-- Inversion `z ↦ z⁻¹` on the Riemann sphere, with `∞ ↦ 0` and `0 ↦ ∞`. -/
noncomputable def inversion : OnePoint ℂ → OnePoint ℂ :=
  fun p => p.elim ((0 : ℂ) : OnePoint ℂ)
    fun z => if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem inversion_infty : inversion ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem inversion_coe_zero : inversion ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [inversion]

theorem inversion_coe {z : ℂ} (hz : z ≠ 0) :
    inversion (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [inversion, hz]

theorem inversion_involutive : Function.Involutive inversion := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [inversion_coe hz, inversion_coe (inv_ne_zero hz), inv_inv]

@[simp] theorem inversion_inversion (p : OnePoint ℂ) : inversion (inversion p) = p :=
  inversion_involutive p

theorem inversion_eq_infty_iff {p : OnePoint ℂ} :
    inversion p = ∞ ↔ p = ((0 : ℂ) : OnePoint ℂ) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · simp [inversion_coe hz, hz]

/-- `(↑)` sends `cocompact ℂ` to `𝓝 ∞` (mathlib's `tendsto_coe_infty` re-based off
`coclosedCompact` for downstream convenience). -/
theorem tendsto_coe_cocompact :
    Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (∞ : OnePoint ℂ)) := by
  rw [← Filter.coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

/-- The `𝓝 ∞` filter work, packaged: `z ↦ ↑(z⁻¹)` blows up at `0`. -/
theorem tendsto_coe_inv_nhdsNE_zero :
    Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (∞ : OnePoint ℂ)) := by
  have h2 : Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 ∞) := by
    rw [Metric.cobounded_eq_cocompact]
    exact tendsto_coe_cocompact
  exact h2.comp Filter.tendsto_inv₀_nhdsNE_zero

theorem continuous_inversion : Continuous inversion := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [continuousAt_infty']
    simp only [inversion_infty]
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have hmem : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ :=
      Bornology.isBounded_def.mp Bornology.isBounded_singleton
    have heq : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) =ᶠ[Bornology.cobounded ℂ]
        (((↑) : ℂ → OnePoint ℂ) ∘ Inv.inv) := by
      filter_upwards [hmem] with z hz
      have hz' : z ≠ 0 := hz
      simp only [Function.comp_apply]
      exact inversion_coe hz'
    exact (tendsto_congr' heq).2
      ((continuous_coe.tendsto (0 : ℂ)).comp Filter.tendsto_inv₀_cobounded)
  | coe z =>
    rw [continuousAt_coe]
    by_cases hz : z = 0
    · subst hz
      have hval : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) (0 : ℂ) = ∞ := by
        simp [Function.comp_apply]
      rw [ContinuousAt, hval, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
      refine ⟨?_, ?_⟩
      · have heq : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)]
            (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          have hw' : w ≠ 0 := hw
          simp only [Function.comp_apply]
          exact inversion_coe hw'
        exact (tendsto_congr' heq).2 tendsto_coe_inv_nhdsNE_zero
      · simpa [hval] using
          tendsto_pure_nhds (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) (0 : ℂ)
    · have heq : (((↑) : ℂ → OnePoint ℂ) ∘ Inv.inv) =ᶠ[𝓝 z] (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) :=
        by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp only [Function.comp_apply]
        exact (inversion_coe hw).symm
      exact (continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr heq

/-- Inversion as a self-inverse homeomorphism of the Riemann sphere. -/
noncomputable def inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion

@[simp] theorem inversionHomeomorph_apply : ⇑inversionHomeomorph = inversion := rfl

@[simp] theorem inversionHomeomorph_symm : inversionHomeomorph.symm = inversionHomeomorph := rfl

end RS.P1
