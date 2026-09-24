/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Local integrability and continuity of translated-kernel integrals

Let `k` be a continuous kernel whose support lies in the closed ball of radius
`ε` about the origin, so that `k (· - y)` is supported in the closed ball of
radius `ε` about `y`. For a function `g` that is locally integrable on an open
set `Ω`, the product `x ↦ g x * k (x - y)` is then integrable as soon as the
ball `closedBall y ε` sits inside `Ω`, and the parametrised integral
`y ↦ ∫ x, g x * k (x - y)` is continuous wherever the translated ball still
fits inside `Ω`. These are the local-integrability and continuity inputs used
in the Caffarelli–Kohn–Nirenberg paper (CKN) when a spatially localised kernel
is slid against a locally integrable density.
-/

@[expose] public section

namespace CKN

open MeasureTheory Metric Filter


noncomputable section

/-- **Closed thickenings of a compact ball inside an open set.** If the closed
ball `closedBall y₀ ε` is contained in an open set `Ω`, then some positive
radius `δ` has the property that the closed `δ`-thickening of that ball is
still contained in `Ω`, and every translate of the ball whose centre lies
within distance `δ` of `y₀` is contained in that same thickening. This is the
uniform room around `closedBall y₀ ε` used in the Caffarelli–Kohn–Nirenberg
paper (CKN) to slide a localised kernel without leaving `Ω`. -/
theorem exists_delta_cthickening_subset {d : ℕ} {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {ε : ℝ} {y₀ : Vec d} (hy₀ : Metric.closedBall y₀ ε ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.cthickening δ (Metric.closedBall y₀ ε) ⊆ Ω ∧
      ∀ y : Vec d, dist y y₀ ≤ δ →
        Metric.closedBall y ε ⊆ Metric.cthickening δ (Metric.closedBall y₀ ε) := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_closedBall y₀ ε).exists_cthickening_subset_open hΩ hy₀
  refine ⟨δ, hδpos, hδsub, ?_⟩
  intro y hy x hx
  have hxε : dist x y ≤ ε := Metric.mem_closedBall.mp hx
  have hp : x - y + y₀ ∈ Metric.closedBall y₀ ε := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : x - y + y₀ - y₀ = x - y := by abel
    rw [hsub]
    simpa [dist_eq_norm] using hxε
  refine Metric.mem_cthickening_of_dist_le x (x - y + y₀) δ _ hp ?_
  rw [dist_eq_norm]
  have hsub : x - (x - y + y₀) = y - y₀ := by abel
  rw [hsub]
  rwa [← dist_eq_norm]

/-- **Integrability of a translated kernel against a locally integrable
function.** If `k` is continuous and vanishes outside the closed ball of radius
`ε` about the origin, and `g` is locally integrable on `Ω`, then for any closed
ball `closedBall y ε` contained in `Ω` the product `x ↦ g x * k (x - y)` is
integrable for Lebesgue measure. This is the local-integrability input in the
Caffarelli–Kohn–Nirenberg paper (CKN) for a spatially localised kernel acted
against a locally integrable density. -/
theorem integrable_mul_translate {d : ℕ} {Ω : Set (Vec d)} {g k : Vec d → ℝ}
    (hg : MeasureTheory.LocallyIntegrableOn g Ω MeasureTheory.volume)
    (hk : Continuous k) {ε : ℝ}
    (hksupp : ∀ z : Vec d, ε < ‖z‖ → k z = 0)
    {y : Vec d} (hy : Metric.closedBall y ε ⊆ Ω) :
    MeasureTheory.Integrable (fun x => g x * k (x - y)) MeasureTheory.volume := by
  have hsupp : Function.support (fun x => g x * k (x - y)) ⊆ Metric.closedBall y ε := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall]
    by_contra hcon
    rw [not_le] at hcon
    exact hx (by rw [hksupp (x - y) (by simpa [dist_eq_norm] using hcon), mul_zero])
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  have hgInt : MeasureTheory.IntegrableOn g (Metric.closedBall y ε) MeasureTheory.volume :=
    hg.integrableOn_compact_subset hy (isCompact_closedBall y ε)
  have hkCont : ContinuousOn (fun x => k (x - y)) (Metric.closedBall y ε) :=
    (hk.comp (continuous_id.sub continuous_const)).continuousOn
  simpa [smul_eq_mul] using hgInt.smul_continuousOn hkCont (isCompact_closedBall y ε)

/-- **Continuity of the translated-kernel integral.** If `k` is continuous and
vanishes outside the closed ball of radius `ε` about the origin, `g` is locally
integrable on the open set `Ω`, and `closedBall y₀ ε ⊆ Ω`, then the
parametrised integral `y ↦ ∫ x, g x * k (x - y)` is continuous at `y₀`. This is
the continuity input in the Caffarelli–Kohn–Nirenberg paper (CKN) that lets a
localised kernel be slid against a locally integrable density. -/
theorem continuousAt_integral_mul_translate {d : ℕ} {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {g k : Vec d → ℝ}
    (hg : MeasureTheory.LocallyIntegrableOn g Ω MeasureTheory.volume)
    (hk : Continuous k) {ε : ℝ}
    (hksupp : ∀ z : Vec d, ε < ‖z‖ → k z = 0)
    {y₀ : Vec d} (hy₀ : Metric.closedBall y₀ ε ⊆ Ω) :
    ContinuousAt (fun y => ∫ x, g x * k (x - y) ∂MeasureTheory.volume) y₀ := by
  obtain ⟨δ, hδpos, hδsub, hδball⟩ := exists_delta_cthickening_subset hΩ hy₀
  set K : Set (Vec d) := Metric.cthickening δ (Metric.closedBall y₀ ε) with hK
  have hKcompact : IsCompact K := (isCompact_closedBall y₀ ε).cthickening
  have hKmeas : MeasurableSet K := Metric.isClosed_cthickening.measurableSet
  have hKΩ : K ⊆ Ω := hδsub
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Vec d) (max ε 0)).exists_bound_of_continuousOn hk.continuousOn
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [Metric.mem_closedBall]))
  have hkC : ∀ z : Vec d, ‖k z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : Vec d) (max ε 0)
    · exact hC z hz
    · have hzε : ε < ‖z‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm, sub_zero] at hz
        exact lt_of_le_of_lt (le_max_left ε 0) hz
      rw [hksupp z hzε, norm_zero]
      exact hCnn
  have hboundInt :
      Integrable (Set.indicator K (fun x => C * ‖g x‖)) MeasureTheory.volume := by
    rw [integrable_indicator_iff hKmeas]
    simpa [MeasureTheory.IntegrableOn] using
      (hg.integrableOn_compact_subset hKΩ hKcompact).integrable.norm.const_mul C
  refine continuousAt_of_dominated (F := fun y x => g x * k (x - y))
    (x₀ := y₀) (bound := Set.indicator K (fun x => C * ‖g x‖)) ?_ ?_ hboundInt ?_
  · filter_upwards [Metric.closedBall_mem_nhds y₀ hδpos] with y hy
    exact (integrable_mul_translate hg hk hksupp
      ((hδball y (Metric.mem_closedBall.mp hy)).trans hKΩ)).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds y₀ hδpos] with y hy
    filter_upwards with x
    by_cases hx : x ∈ Metric.closedBall y ε
    · have hxK : x ∈ K := hδball y (Metric.mem_closedBall.mp hy) hx
      rw [Set.indicator_of_mem hxK, norm_mul]
      calc ‖g x‖ * ‖k (x - y)‖ ≤ ‖g x‖ * C := by
            gcongr
            exact hkC (x - y)
        _ = C * ‖g x‖ := by rw [mul_comm]
    · have hxε : ε < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hx
        exact hx
      rw [hksupp (x - y) hxε, mul_zero, norm_zero]
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
        exact mul_nonneg hCnn (norm_nonneg (g x))
      · rw [Set.indicator_of_notMem hxK]
  · filter_upwards with x
    exact ((hk.comp (continuous_const.sub continuous_id)).const_mul (g x)).continuousAt

end

end CKN
