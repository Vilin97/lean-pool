/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Vitali

/-!
# Nemytskii operators: WeakConvergence

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter
open scoped ENNReal Topology

/-- Sequential convergence against every continuous real linear functional. -/
@[expose] def _root_.Function.NemytskiiWeaklyConvergesTo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (v : E) :
    Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n : ℕ => f (u n)) atTop (𝓝 (f v))

theorem IsCaratheodory.strong_convergence_of_weak_convergence
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : Ω → ℝ → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {ι : X →L[ℝ] (Ω → ℝ)} (hιp : ∀ x : X, MemLp (ι x) p μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q).toReal)
    {u : ℕ → X} (hup : UnifIntegrable (ι ∘ u) p μ)
    {v : X} (huv : u.NemytskiiWeaklyConvergesTo v) :
    (fun n : ℕ => fun ω : Ω => f ω (ι (u n) ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (ι v ω)) q μ
      := by
  convert
    hf.seqContinuous_nemytskii_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    .. using 1
  any_goals tauto
  · exact (MemLp.aestronglyMeasurable <| hιp <| u ·)
  · convert tendstoInMeasure_of_tendsto_ae (MemLp.aestronglyMeasurable <| hιp <| u ·) _
    apply Eventually.of_forall
    intro ω
    have := huv ((ContinuousLinearMap.proj ω).comp ι)
    aesop

end NemytskiiLebesgue
