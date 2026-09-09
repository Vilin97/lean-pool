/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FlowEscapeBound
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section

/-!
# No vorticity arriving from spatial infinity

The flow hypotheses below describe globally defined approximations to backward
characteristics. Their kinetic energy is uniformly bounded. On paths which
stay inside the approximation radius, nonzero endpoint vorticity must come
from the initial vorticity support. Initial support is trapped by the inverse
endpoint maps in one common ball. These hypotheses exclude all nonzero
vorticity outside that ball; no global pointwise velocity bound is needed.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Euler.ComparatorBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private theorem positive_volume_set_of_nonzero_outside
    (w : ℝ³ → ℝ³) (hw : Continuous w) (B : ℝ) (x : ℝ³)
    (hxB : B < ‖x‖) (hxw : w x ≠ 0) :
    ∃ S : Set ℝ³, MeasurableSet S ∧ volume S ≠ ⊤ ∧
      0 < volume.real S ∧ ∃ K₀ : ℝ,
      ∀ y ∈ S, ‖y‖ ≤ K₀ ∧ B < ‖y‖ ∧ w y ≠ 0 := by
  have hU : IsOpen ({y : ℝ³ | B < ‖y‖} ∩ {y : ℝ³ | w y ≠ 0}) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_ne.preimage hw)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x ⟨hxB, hxw⟩
  refine ⟨Metric.ball x r, measurableSet_ball, measure_ball_ne_top,
    ?_, ‖x‖ + r, ?_⟩
  · exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top
  · intro y hy
    exact ⟨norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hy).le, hsub hy⟩

/-- Approximate backward characteristics for a vorticity field at one time.
The parameter `R` is the spatial radius on which transport is valid. The
time parameter `s` runs backward from the endpoint (`s=0`) to the initial
time (`s=T`). -/
structure BackwardVorticityFlows
    (T energy supportRadius : ℝ) (K : Set ℝ³) (w₀ w : ℝ³ → ℝ³) where
  flow : ℝ → ℝ → ℝ³ ≃ₜ ℝ³
  velocity : ℝ → ℝ → ℝ³ → ℝ³
  time_nonneg : 0 ≤ T
  preserves_volume : ∀ R s, MeasurePreserving (flow R s) volume volume
  initial_map : ∀ R x, flow R 0 x = x
  joint_measurable : ∀ R, AEStronglyMeasurable
    (fun sx : ℝ × ℝ³ => ‖velocity R sx.1 (flow R sx.1 sx.2)‖ ^ 2)
    ((volume.restrict (Icc 0 T)).prod volume)
  velocity_memLp : ∀ R s, MemLp (velocity R s) 2 volume
  energy_bound : ∀ R s, (∫ x, ‖velocity R s x‖ ^ 2) ≤ energy
  curve_continuous : ∀ R x, ContinuousOn (fun s => flow R s x) (Icc 0 T)
  speed_continuous : ∀ R x,
    ContinuousOn (fun s => velocity R s (flow R s x)) (Icc 0 T)
  curve_derivative : ∀ R x s, s ∈ Ioo 0 T →
    HasDerivAt (fun r => flow R r x) (velocity R s (flow R s x)) s
  initial_support : Function.support w₀ ⊆ K
  transport_nonzero : ∀ R x,
    (∀ s ∈ Icc 0 T, ‖flow R s x‖ < R) → w x ≠ 0 → w₀ (flow R T x) ≠ 0
  forward_trap : ∀ R a, a ∈ K → ‖(flow R T).symm a‖ ≤ supportRadius

namespace BackwardVorticityFlows

variable {T energy supportRadius : ℝ} {K : Set ℝ³} {w₀ w : ℝ³ → ℝ³}
  (F : BackwardVorticityFlows T energy supportRadius K w₀ w)

include F

/-- A nonzero-vorticity endpoint outside the trapped support has to leave
every approximation ball when traced backward. -/
theorem escapes (R : ℝ) (x : ℝ³) (hx : supportRadius < ‖x‖) (hw : w x ≠ 0) :
    ∃ s ∈ Icc 0 T, R ≤ ‖F.flow R s x‖ := by
  by_contra hn
  have hstay : ∀ s ∈ Icc 0 T, ‖F.flow R s x‖ < R := by
    intro s hs
    exact lt_of_not_ge (fun hr => hn ⟨s, hs, hr⟩)
  have hstart : F.flow R T x ∈ K :=
    F.initial_support (F.transport_nonzero R x hstay hw)
  have htrap := F.forward_trap R (F.flow R T x) hstart
  have htrap' : ‖x‖ ≤ supportRadius := by
    simpa only [Homeomorph.symm_apply_apply] using htrap
  exact not_le_of_gt hx htrap'

/-- Every bounded measurable set of nonzero vorticity outside the support
ball has the quantitative escape bound. -/
theorem measure_nonzero_outside_le
    (S : Set ℝ³) (hS : MeasurableSet S) (hfinite : volume S ≠ ⊤)
    (K₀ R : ℝ) (hKR : K₀ < R)
    (hSbound : ∀ x ∈ S, ‖x‖ ≤ K₀)
    (hSoutside : ∀ x ∈ S, supportRadius < ‖x‖)
    (hSnonzero : ∀ x ∈ S, w x ≠ 0) :
    volume.real S ≤ energy * T ^ 2 / (R - K₀) ^ 2 := by
  apply flow_escape_measure_le volume T K₀ R energy F.time_nonneg hKR
    (fun s x => F.flow R s x) (F.velocity R)
    (F.preserves_volume R) (fun s => (F.flow R s).measurableEmbedding)
    (F.joint_measurable R) (F.velocity_memLp R) (F.energy_bound R)
    (F.curve_continuous R) (F.speed_continuous R) (F.curve_derivative R)
    S hS hfinite
  · intro x hx
    simpa only [F.initial_map] using hSbound x hx
  · intro x hx
    exact F.escapes R x (hSoutside x hx) (hSnonzero x hx)

/-- Sending the approximation radius to infinity rules out a positive
measure set of bounded nonzero-vorticity endpoints outside the trapped ball. -/
theorem measure_nonzero_outside_eq_zero
    (S : Set ℝ³) (hS : MeasurableSet S) (hfinite : volume S ≠ ⊤)
    (K₀ : ℝ) (hSbound : ∀ x ∈ S, ‖x‖ ≤ K₀)
    (hSoutside : ∀ x ∈ S, supportRadius < ‖x‖)
    (hSnonzero : ∀ x ∈ S, w x ≠ 0) : volume.real S = 0 := by
  have hlim : Tendsto (fun r : ℝ => energy * T ^ 2 / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have hz : volume.real S ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hh := F.measure_nonzero_outside_le S hS hfinite K₀ (K₀ + r)
      (by linarith) hSbound hSoutside hSnonzero
    simpa only [add_sub_cancel_left] using hh
  exact le_antisymm hz measureReal_nonneg

/-- Continuity removes the null exceptional set: vorticity vanishes
pointwise outside the common ball containing the transported initial support. -/
theorem zero_outside (hw : Continuous w) (x : ℝ³) (hx : supportRadius < ‖x‖) :
    w x = 0 := by
  by_contra hn
  obtain ⟨S, hS, hfinite, hpos, K₀, hprops⟩ :=
    positive_volume_set_of_nonzero_outside w hw supportRadius x hx hn
  have hz := F.measure_nonzero_outside_eq_zero S hS hfinite K₀
    (fun y hy => (hprops y hy).1) (fun y hy => (hprops y hy).2.1)
    (fun y hy => (hprops y hy).2.2)
  linarith

/-- The transported field is supported in one fixed compact ball. -/
theorem support_subset_closedBall (hw : Continuous w) :
    Function.support w ⊆ Metric.closedBall (0 : ℝ³) supportRadius := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt (fun hlt => hx (F.zero_outside hw x hlt))

theorem hasCompactSupport (hw : Continuous w) : HasCompactSupport w := by
  exact HasCompactSupport.intro (isCompact_closedBall (0 : ℝ³) supportRadius)
    (fun x hx => F.zero_outside hw x (by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))

end BackwardVorticityFlows
end Euler.ComparatorBridge
