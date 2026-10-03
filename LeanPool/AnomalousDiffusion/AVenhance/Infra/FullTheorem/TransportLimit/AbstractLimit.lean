/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Abstract `L²` limits along a fast subsequence

A sequence that is Cauchy in `L²` has a fast subsequence converging almost everywhere; the
pointwise limit (chosen by `limUnder`) is in `L²` and is the `L²` limit of the whole sequence.
Everything here is stated for an arbitrary measure space.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

/-- `eLpNorm 2` of a square-integrable real function is the square root of its energy. -/
theorem eLpNorm_two_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ a, f a ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp [sq_abs]

/-- A square-integrable function with `eLpNorm 2 ≤ ofReal η` has energy root at most `η`. -/
theorem sqrt_integral_sq_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) {η : ℝ} (hη : 0 ≤ η)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal η) :
    Real.sqrt (∫ a, f a ^ 2 ∂μ) ≤ η := by
  rw [eLpNorm_two_eq hf] at h
  exact (ENNReal.ofReal_le_ofReal_iff hη).1 h

/-- Converse: energy root at most `η` bounds `eLpNorm 2`. -/
theorem eLpNorm_le_of_sqrt_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) {η : ℝ}
    (h : Real.sqrt (∫ a, f a ^ 2 ∂μ) ≤ η) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal η := by
  rw [eLpNorm_two_eq hf]
  exact ENNReal.ofReal_le_ofReal h

/-- A fast subsequence from a family of `∃ N, ∀ j k ≥ N` statements. -/
theorem exists_fast_index (Q : ℕ → ℕ → ℕ → Prop)
    (h : ∀ n, ∃ N, ∀ j ≥ N, ∀ k ≥ N, Q n j k) :
    ∃ s : ℕ → ℕ, Monotone s ∧ (∀ k, k ≤ s k) ∧
      ∀ n, ∀ a ≥ n, ∀ b ≥ n, Q n (s a) (s b) := by
  choose N hN using h
  refine ⟨fun k => k + ∑ i ∈ Finset.range (k + 1), N i, ?_, ?_, ?_⟩
  · intro a b hab
    change a + _ ≤ b + _
    have : ∑ i ∈ Finset.range (a + 1), N i ≤ ∑ i ∈ Finset.range (b + 1), N i :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    omega
  · intro k
    exact Nat.le_add_right _ _
  · intro n a ha b hb
    have hle : ∀ c ≥ n, N n ≤ c + ∑ i ∈ Finset.range (c + 1), N i := by
      intro c hc
      have : N n ≤ ∑ i ∈ Finset.range (c + 1), N i :=
        Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (by omega))
      omega
    exact hN n _ (hle a ha) _ (hle b hb)

/-- Geometric summability in `ℝ≥0∞`. -/
theorem tsum_geometric_ne_top :
    ∑' i : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ i) ≠ ∞ := by
  have hs : Summable fun i : ℕ => 2 * (1 / 2 : ℝ) ^ i :=
    (summable_geometric_two).mul_left 2 |>.congr (fun i => by simp)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs]
  exact ENNReal.ofReal_ne_top

/-- A.e. convergence of the fast subsequence. -/
theorem ae_tendsto_fast {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) {s : ℕ → ℕ}
    (hfast : ∀ n, ∀ a ≥ n, ∀ b ≥ n,
      eLpNorm (f (s a) - f (s b)) 2 μ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) :
    ∀ᵐ x ∂μ, Tendsto (fun k => f (s k) x) atTop
      (𝓝 (limUnder atTop (fun k => f (s k) x))) := by
  have hex := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (μ := μ) (p := 2)
    (f := fun k => f (s k)) (fun k => (hf (s k)).aestronglyMeasurable) (by norm_num)
    (B := fun i => ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ i)) tsum_geometric_ne_top
    (by
      intro N n m hn hm
      refine lt_of_le_of_lt (hfast N n hn m hm) ?_
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
      linarith)
  filter_upwards [hex] with x hx
  obtain ⟨l, hl⟩ := hx
  rw [hl.limUnder_eq]
  exact hl

/-- The pointwise limit is in `L²`, and the whole sequence converges to it in `L²` with the
`liminf` bound. -/
theorem memLp_limit_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hb : ∀ᶠ k in atTop, eLpNorm (f k) 2 μ ≤ c) :
    MemLp g 2 μ ∧ eLpNorm g 2 μ ≤ c := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  have hle := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hf g hg hlim
  have hle' : atTop.liminf (fun k => eLpNorm (f k) 2 μ) ≤ c :=
    liminf_le_of_frequently_le' hb.frequently
  have h := hle.trans hle'
  have hlt : eLpNorm g 2 μ < ∞ := lt_of_le_of_lt h hc.lt_top
  exact ⟨hlt, h⟩

end AVenhance.Infra.FullTheorem.TransportLimit
