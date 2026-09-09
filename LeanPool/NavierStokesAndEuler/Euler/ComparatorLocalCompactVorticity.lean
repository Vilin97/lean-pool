/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.NoIncomingVorticity
public import LeanPool.NavierStokesAndEuler.Euler.TruncationFamily
public import LeanPool.NavierStokesAndEuler.Euler.TruncatedBackwardFlow
import LeanPool.NavierStokesAndEuler.Euler.ComparatorTruncationFamily
public import LeanPool.NavierStokesAndEuler.Euler.LocalFlowTrap
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import LeanPool.NavierStokesAndEuler.Euler.ReversedVorticityTransport
import LeanPool.NavierStokesAndEuler.Euler.ScalarEulerVorticity

/-!
# Short-time compact vorticity from finite-energy truncations

The auxiliary characteristics are global flows of compact solenoidal
truncations. The construction does not require global trajectories of the
untruncated Comparator velocity.
-/

@[expose] public section


noncomputable section


open Set MeasureTheory EulerSmoothLimit EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- One compact spacetime cylinder supplies a common local speed bound and
one positive trapping time for every truncation agreeing on that cylinder. -/
theorem exists_local_trapping_constants
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ A M δ : ℝ, 0 < A ∧ 0 < M ∧ 0 < δ ∧ δ ≤ 1 ∧ δ * M < 1 ∧
      (∀ x ∈ tsupport (vectorCurl u₀), ‖x‖ ≤ A) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ A + 1 → ‖v x t‖ ≤ M) := by
  obtain ⟨A, hA, hAbound⟩ := hc.isBounded.exists_pos_norm_le
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) (A + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hv : ContinuousOn (fun z : ℝ × Space => v z.2 z.1)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) (A + 1)) :=
    h.velocity_joint_contDiffOn.continuousOn.mono (by
      intro z hz
      exact ⟨hz.1.1, mem_univ _⟩)
  obtain ⟨M, hM, hMb⟩ := (hcompact.image_of_continuousOn hv).isBounded.exists_pos_norm_le
  let δ : ℝ := min 1 (1 / (2 * M))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδM : δ * M < 1 := by
    have hm : δ * M ≤ (1 / (2 * M)) * M :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
    have he : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    rw [he] at hm
    linarith
  refine ⟨A, M, δ, hA, hM, hδ, min_le_left _ _, hδM, hAbound, ?_⟩
  intro t ht x hx
  apply hMb (v x t)
  refine ⟨(t, x), ⟨ht, ?_⟩, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx


omit h in
theorem truncation_realField_agrees
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : r ∈ Icc 0 1)
    (x : Space) (hx : ‖x‖ < R) :
    (F.coefficient R).realField 1 zero_le_one r x = v x r := by
  change (F.coefficient R).field (projIcc 0 1 zero_le_one r) x = _
  rw [F.agrees R hR _ x hx]
  simp only [projIcc_of_mem zero_le_one hr]

/-- The approximation radius is enlarged to include the one fixed trapping
ball. This gives valid approximants even for nonpositive requested radii. -/
def locallyTrappedBackwardFlows
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (A M δ T : ℝ) (hA : 0 < A) (hM : 0 < M)
    (hδ1 : δ ≤ 1) (hδM : δ * M < 1) (hT : T ∈ Icc 0 δ)
    (hAbound : ∀ x ∈ tsupport (vectorCurl u₀), ‖x‖ ≤ A)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ A + 1 → ‖v x t‖ ≤ M) :
    ComparatorBridge.BackwardVorticityFlows T F.energy (A + 1)
      (tsupport (vectorCurl u₀)) (vectorCurl u₀) (vectorCurl (v · T)) := by
  let ρ : ℝ → ℝ := fun R => max R (A + 2)
  have hρ (R : ℝ) : 0 < ρ R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT1 : T ≤ 1 := hT.2.trans hδ1
  let C (R : ℝ) := F.coefficient (ρ R)
  let X (R s : ℝ) := ComparatorBridge.TruncatedBackwardFlow.homeomorph (C R) T hT.1 hT1 s
  let V (R : ℝ) := ComparatorBridge.TruncatedBackwardFlow.velocity (C R) T hT.1 hT1
  refine {
    flow := X
    velocity := V
    time_nonneg := hT.1
    preserves_volume := ?_
    initial_map := ?_
    joint_measurable := ?_
    velocity_memLp := ?_
    energy_bound := ?_
    curve_continuous := ?_
    speed_continuous := ?_
    curve_derivative := ?_
    initial_support := subset_tsupport _
    transport_nonzero := ?_
    forward_trap := ?_ }
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.homeomorph_measurePreserving
      (C R) T hT.1 hT1 volume (F.divergence (ρ R) (hρ R)) s
  · intro R x
    exact ComparatorBridge.TruncatedBackwardFlow.homeomorph_zero (C R) T hT.1 hT1 x
  · intro R
    exact ComparatorBridge.TruncatedBackwardFlow.action_joint_measurable (C R) T hT.1 hT1 volume
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.velocity_memLp
      (C R) T hT.1 hT1 volume (F.memLp (ρ R) (hρ R)) s
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.velocity_energy
      (C R) T hT.1 hT1 volume F.energy (F.energy_bound (ρ R) (hρ R)) s
  · intro R x
    exact (ComparatorBridge.TruncatedBackwardFlow.curve_continuous (C R) T hT.1 hT1 x).continuousOn
  · intro R x
    exact (ComparatorBridge.TruncatedBackwardFlow.speed_continuous (C R) T hT.1 hT1 x).continuousOn
  · intro R x s hs
    exact ComparatorBridge.TruncatedBackwardFlow.curve_hasDerivAt (C R) T hT.1 hT1 x s hs
  · intro R x hstay hnz
    have he : (v · 0) = u₀ := funext h.initial_condition
    rw [← he]
    apply h.vorticity_ne_zero_along_reverse_trajectory
      (fun s => X R s x) T hT.1
      (ComparatorBridge.TruncatedBackwardFlow.curve_continuous (C R) T hT.1 hT1 x).continuousOn
    · intro s hs
      have hd := ComparatorBridge.TruncatedBackwardFlow.curve_hasDerivAt
        (C R) T hT.1 hT1 x s hs
      have hv : V R s (X R s x) = -v (X R s x) (T - s) := by
        change ComparatorBridge.TruncatedBackwardFlow.velocity (C R) T hT.1 hT1 s (X R s x) = _
        rw [ComparatorBridge.TruncatedBackwardFlow.velocity_eq_realField
          (C R) T hT.1 hT1 s ⟨hs.1.le, hs.2.le⟩]
        rw [truncation_realField_agrees F (ρ R) (hρ R) (T - s)
          ⟨sub_nonneg.mpr hs.2.le, by linarith [hs.1]⟩ (X R s x)
          ((hstay s ⟨hs.1.le, hs.2.le⟩).trans_le (le_max_left _ _))]
      exact hv ▸ hd
    · simpa only [X, ComparatorBridge.TruncatedBackwardFlow.homeomorph_zero] using hnz
  · intro R a ha
    let Z := ComparatorBridge.TruncatedBackwardFlow.endpointPath (C R) T hT.1 hT1 a
    have hsmall : T * M < (A + 1) - A := by
      have hm := mul_le_mul_of_nonneg_right hT.2 hM.le
      linarith
    have hz := EulerComparatorLocalFlow.norm_lt_of_local_speed_bound
      Z ((C R).realField 1 zero_le_one) hM.le (by linarith : A < A + 1) hsmall
      (ComparatorBridge.TruncatedBackwardFlow.endpointPath_continuous (C R) T hT.1 hT1
          a).continuousOn
      (ComparatorBridge.TruncatedBackwardFlow.endpointPath_hasDerivAt (C R) T hT.1 hT1 a)
      (by
          simpa only [Z, ComparatorBridge.TruncatedBackwardFlow.endpointPath_zero] using hAbound a
              ha)
      (by
        intro r hr x hx
        rw [truncation_realField_agrees F (ρ R) (hρ R) r ⟨hr.1, hr.2.trans hT1⟩ x
          (lt_of_le_of_lt hx (lt_of_lt_of_le (by linarith) (le_max_right _ _)))]
        exact hspeed r ⟨hr.1, hr.2.trans hT1⟩ x hx)
      T ⟨hT.1, le_rfl⟩
    simpa only [Z, X, ComparatorBridge.TruncatedBackwardFlow.endpointPath_end] using hz.le

/-- Finite-energy solenoidal truncations imply compact vorticity for a
uniform positive interval, using only the Comparator solution assumptions. -/
theorem local_compact_vorticity_of_truncationFamily
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ δ B : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 δ,
      tsupport (vectorCurl (v · t)) ⊆ Metric.closedBall (0 : Space) B := by
  obtain ⟨A, M, δ, hA, hM, hδ, hδ1, hδM, hAbound, hspeed⟩ :=
    h.exists_local_trapping_constants hc
  refine ⟨δ, A + 1, hδ, ?_⟩
  intro t ht
  let G := h.locallyTrappedBackwardFlows F A M δ t hA hM hδ1 hδM ht hAbound hspeed
  exact closure_minimal (G.support_subset_closedBall
    (EulerMeanVectorIdentities.vectorCurl_smooth (v · t) (h.velocity_contDiff t ht.1)).continuous)
    Metric.isClosed_closedBall


/-- Compact initial vorticity stays in one compact ball for a positive time
for every Comparator solution. The auxiliary global trajectories are those
of the explicitly constructed finite-energy solenoidal truncations. -/
theorem local_compact_vorticity (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ δ B : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 δ,
      tsupport (vectorCurl (v · t)) ⊆ Metric.closedBall (0 : Space) B :=
  h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc

end Euler.EulerExistenceAndSmoothnessR3
