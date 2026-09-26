/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Continuity

/-!
# Nemytskii operators: Nemytskii

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

theorem IsCaratheodory.monotone_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : E, ⟪f ω s - f ω t, s - t⟫ ≥ 0)
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    0 ≤ ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ := by
  constructor
  · apply Real.HolderConjugate.integrable_memLp_inner_memLp hpq
    · apply MemLp.sub <;> apply hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC hfaCpq
      <;> assumption
    · exact MemLp.sub hup hvp
  · apply integral_nonneg_of_ae
    filter_upwards [hf0] with ω hω
    exact hω (u ω) (v ω)

theorem IsCaratheodory.monotone_integral_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ → ℝ} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : ℝ, (f ω s - f ω t) * (s - t) ≥ 0)
    {u : Ω → ℝ} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f ω (u ω) - f ω (v ω)) * (u ω - v ω)) μ ∧
    0 ≤ ∫ ω : Ω, (f ω (u ω) - f ω (v ω)) * (u ω - v ω) ∂μ := by
  simp only [←inner_eq_mul]
  refine hf.monotone_integral hpq haq hC hfaCpq ?_ hup hvp
  simpa only [inner_eq_mul] using hf0

end NemytskiiLebesgue
