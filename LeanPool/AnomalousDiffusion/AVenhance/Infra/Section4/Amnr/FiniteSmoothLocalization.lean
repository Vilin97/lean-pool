/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteMaterialCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SmoothLocalization

/-! Local smooth representatives at the finite source regularity order. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4

/-- A scalar field smooth on an open domain has a globally smooth local
representative. This does not impose any extension condition on the solution. -/
theorem amnr_finite_smooth_local_representative {U : Set AmnrSpace} (hU : IsOpen U)
    {f : AmnrSpace → ℝ} {N : ℕ} (hf : ContDiffOn ℝ N f U)
    {z : AmnrSpace} (hz : z ∈ U) :
    ∃ g : AmnrSpace → ℝ, ContDiff ℝ N g ∧ g =ᶠ[nhds z] f := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let χ : ContDiffBump z :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hs : tsupport χ ⊆ U := by rw [χ.tsupport_eq]; exact hball
  refine ⟨fun y => χ y * f y, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hs hy)))
    · have he : (fun y => χ y * f y) =ᶠ[nhds y] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with x hx
        have hxzero : χ x = 0 := by
          by_contra hh
          exact hx (subset_closure hh)
        simp only [hxzero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, one_mul]

end AVenhance.Infra.Section4
