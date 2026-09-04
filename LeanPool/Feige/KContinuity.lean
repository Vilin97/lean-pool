/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KStatistic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity core for the Dirichlet statistic

This file formalizes the dominated-convergence step used to establish the
continuity needed in the proof of Theorem 2.1.  It proves that membership in
the moving halfspace stabilizes away from its boundary, and consequently
that `dirichletK` is sequentially continuous at every parameter whose
boundary hyperplane has zero product-exponential measure.
-/

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory Set Topology

namespace Feige

section

variable {ι : Type*} [Fintype ι]

/-- The affine functional defining the moving halfspace in `kEvent`. -/
def kLinear (y : ι → ℝ) (e : Option ι → NNReal) : ℝ :=
  ∑ i, (y i - 1) * (e (some i) : ℝ)

theorem continuous_kLinear (e : Option ι → NNReal) :
    Continuous (fun y : ι → ℝ ↦ kLinear y e) := by
  unfold kLinear
  fun_prop

/-- Away from the boundary, membership in `kEvent` is eventually constant
under convergence of the parameter vector. -/
theorem eventually_mem_kEvent_iff
    {L : Filter ℕ} {yseq : ℕ → ι → ℝ} {y : ι → ℝ}
    (hy : Tendsto yseq L (𝓝 y)) (e : Option ι → NNReal)
    (hne : kLinear y e ≠ (e none : ℝ)) :
    ∀ᶠ n in L, e ∈ kEvent (yseq n) ↔ e ∈ kEvent y := by
  have ht : Tendsto (fun n ↦ kLinear (yseq n) e) L (𝓝 (kLinear y e)) :=
    (continuous_kLinear e).continuousAt.tendsto.comp hy
  unfold kEvent
  change ∀ᶠ n in L,
    kLinear (yseq n) e ≤ (e none : ℝ) ↔ kLinear y e ≤ (e none : ℝ)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [ht.eventually_lt_const hlt] with n hn
    exact ⟨fun _ ↦ hlt.le, fun _ ↦ hn.le⟩
  · filter_upwards [ht.eventually_const_lt hgt] with n hn
    exact ⟨fun h ↦ False.elim ((not_lt_of_ge h) hn),
      fun h ↦ False.elim ((not_lt_of_ge h) hgt)⟩

/-- The boundary set for a fixed parameter. -/
def kBoundary (y : ι → ℝ) : Set (Option ι → NNReal) :=
  {e | kLinear y e = (e none : ℝ)}

theorem measurableSet_kBoundary (y : ι → ℝ) :
    MeasurableSet (kBoundary y) := by
  unfold kBoundary kLinear
  have hf : Measurable (fun e : Option ι → NNReal ↦
      ∑ i, (y i - 1) * (e (some i) : ℝ)) :=
    Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul ((measurable_pi_apply (some i)).coe_nnreal_real)
  have hg : Measurable (fun e : Option ι → NNReal ↦ (e none : ℝ)) :=
    (measurable_pi_apply none).coe_nnreal_real
  rw [show {e : Option ι → NNReal |
      (∑ i, (y i - 1) * (e (some i) : ℝ)) = (e none : ℝ)} =
      {e | (∑ i, (y i - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ)} ∩
        {e | (e none : ℝ) ≤ ∑ i, (y i - 1) * (e (some i) : ℝ)} by
          ext e
          simp only [mem_ofPred_eq, mem_inter_iff]
          constructor
          · intro h
            exact ⟨h.le, h.ge⟩
          · rintro ⟨h₁, h₂⟩
            exact le_antisymm h₁ h₂]
  exact (measurableSet_le hf hg).inter (measurableSet_le hg hf)

/-- Almost-everywhere stabilization of the moving indicators, assuming only
the geometrically isolated boundary-null statement. -/
theorem ae_eventually_mem_kEvent_iff
    {yseq : ℕ → ι → ℝ} {y : ι → ℝ}
    (hy : Tendsto yseq atTop (𝓝 y))
    (hboundary : expProductMeasure ι (kBoundary y) = 0) :
    ∀ᵐ e ∂expProductMeasure ι,
      ∀ᶠ n in atTop, e ∈ kEvent (yseq n) ↔ e ∈ kEvent y := by
  filter_upwards [compl_mem_ae_iff.2 hboundary] with e he
  exact eventually_mem_kEvent_iff hy e (by simpa [kBoundary] using he)

/-- Dominated convergence for the event probabilities. -/
theorem tendsto_measure_kEvent
    {yseq : ℕ → ι → ℝ} {y : ι → ℝ}
    (hy : Tendsto yseq atTop (𝓝 y))
    (hboundary : expProductMeasure ι (kBoundary y) = 0) :
    Tendsto (fun n ↦ expProductMeasure ι (kEvent (yseq n))) atTop
      (𝓝 (expProductMeasure ι (kEvent y))) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
  · exact measurableSet_kEvent y
  · exact fun n ↦ measurableSet_kEvent (yseq n)
  · exact ae_eventually_mem_kEvent_iff hy hboundary

/-- Sequential continuity of `dirichletK`, reduced to the boundary
hyperplane having measure zero. -/
theorem tendsto_dirichletK
    {yseq : ℕ → ι → ℝ} {y : ι → ℝ}
    (hy : Tendsto yseq atTop (𝓝 y))
    (hboundary : expProductMeasure ι (kBoundary y) = 0) :
    Tendsto (fun n ↦ dirichletK (yseq n)) atTop (𝓝 (dirichletK y)) := by
  unfold dirichletK Measure.real
  exact (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp
    (tendsto_measure_kEvent hy hboundary)

end

end Feige
