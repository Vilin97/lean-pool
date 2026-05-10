/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Analysis.Convex.Integral

import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.Order.Filter.Basic
import LeanPool.RlTheoryInLean.MeasureTheory.Function.L1Space.Integrable

open Filter ProbabilityTheory
open scoped RealInnerProductSpace

namespace MeasureTheory

theorem ContinuousLinearMap.condExp_comp
  {Ω α β : Type*}
  [MeasurableSpace α]
  [NormedAddCommGroup α]
  [NormedSpace ℝ α]
  [CompleteSpace α]
  [BorelSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
  [MeasurableSpace β]
  [SecondCountableTopology β]
  [BorelSpace β]
  {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} (hm : m ≤ m₀)
  [SigmaFinite (μ.trim hm)]
  {f : Ω → α} (hf : Integrable f μ) (L : α →L[ℝ] β)
  : μ[L ∘ f| m] =ᵐ[μ] L ∘ (μ[f | m]) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (g := ⇑L ∘ μ[f | m]) hm
    (L.integrable_comp hf) (fun _ _ _ => ?_) (fun s hs _ => ?_) ?_).symm
  · exact (L.integrable_comp integrable_condExp).restrict
  · simp only [Function.comp_apply]
    rw [L.integral_comp_comm integrable_condExp.restrict, setIntegral_condExp hm hf hs,
      L.integral_comp_comm hf.restrict]
  · exact (L.continuous.measurable.comp stronglyMeasurable_condExp.measurable).aestronglyMeasurable

theorem condExp_inner
  {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} {d : ℕ}
  {f g : Ω → EuclideanSpace ℝ (Fin d)}
  (hm : m ≤ m₀)
  [SigmaFinite (μ.trim hm)]
  (hgInt : Integrable g μ)
  (hfgInt : ∀ i, Integrable ((fun ω ↦ (f ω).ofLp i) * fun ω ↦ (g ω).ofLp i) μ)
  (hf : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ (f ω).ofLp i) μ) :
  μ[fun ω => ⟪f ω, g ω⟫ | m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫ := by
  -- Convert inner product to sum form
  have inner_eq : ∀ x y : EuclideanSpace ℝ (Fin d), ⟪x, y⟫ = ∑ i, x.ofLp i * y.ofLp i := by
    intro x y
    have : ⟪x, y⟫ = WithLp.ofLp y ⬝ᵥ star (WithLp.ofLp x) :=
      EuclideanSpace.inner_eq_star_dotProduct x y
    rw [this, dotProduct_comm, dotProduct]
    simp only [Pi.star_apply, star_trivial]
  simp_rw [inner_eq]
  have hgiInt : ∀ i, Integrable (fun ω => (g ω).ofLp i) μ := fun i =>
    ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (EuclideanSpace.proj i) hgInt
  -- For each component `i`, the component of the conditional expectation equals the
  -- conditional expectation of the component.
  have hproj : ∀ i, μ[fun ω => (g ω).ofLp i | m] =ᵐ[μ] fun ω => (μ[g|m] ω).ofLp i := fun i =>
    ContinuousLinearMap.condExp_comp (f := g) (L := EuclideanSpace.proj i) (μ := μ) (hm := hm) hgInt
  have heq : (fun ω => ∑ i, (f ω).ofLp i * (g ω).ofLp i)
    = ∑ i, (fun ω => (f ω).ofLp i) * (fun ω => (g ω).ofLp i) := by
    ext ω
    simp [Finset.sum_apply]
  rw [heq]
  calc μ[∑ i, (fun ω => (f ω).ofLp i) * (fun ω => (g ω).ofLp i) | m]
      =ᵐ[μ] ∑ i, μ[(fun ω => (f ω).ofLp i) * (fun ω => (g ω).ofLp i) | m] :=
        condExp_finset_sum (fun i _ => hfgInt i) m
    _ =ᵐ[μ] ∑ i, (fun ω => (f ω).ofLp i) * μ[fun ω => (g ω).ofLp i | m] :=
        EventuallyEq.finset_sum fun i _ =>
          condExp_mul_of_aestronglyMeasurable_left (hf i) (hfgInt i) (hgiInt i)
    _ =ᵐ[μ] ∑ i, (fun ω => (f ω).ofLp i) * (fun ω => (μ[g|m] ω).ofLp i) :=
        EventuallyEq.finset_sum fun i _ => EventuallyEq.mul (EventuallyEq.refl _ _) (hproj i)
    _ =ᵐ[μ] fun ω => ∑ x, (f ω).ofLp x * (μ[g|m] ω).ofLp x := by
        filter_upwards with ω
        simp only [Finset.sum_apply, Pi.mul_apply]

theorem norm_condExp_le_condExp_norm
  {Ω : Type*} {m m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {μ : Measure[m₀] Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ} {f : Ω → EuclideanSpace ℝ (Fin d)}
  (hf_i : Integrable f μ)
  (_hf_m : Measurable f)
  (_hf_bdd : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
  (hm : m ≤ m₀) :
  (fun ω => ‖μ[f | m] ω‖) ≤ᵐ[μ] fun ω => μ[fun ω => ‖f ω‖ | m] ω := by
  filter_upwards [condExp_ae_eq_integral_condExpKernel hm hf_i,
    condExp_ae_eq_integral_condExpKernel hm hf_i.norm] with ω hω hω_norm
  simp only [hω, hω_norm]
  exact norm_integral_le_integral_norm f

end MeasureTheory
