/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.Order.Compact

/-!
# Persistence of zeros in holomorphic families

A zero inside a disc persists under small continuous changes of a holomorphic function, provided
the original function has no zeros on the boundary. The proof uses the maximum modulus principle
for the reciprocal of a hypothetically nonvanishing perturbation; no root counting is required.

## Main results

`exists_zero_of_norm_lt_boundary` persists a zero inside a disc under a small perturbation with
no boundary zeros. `eventually_exists_zero_in_fiber` is persistence of zeros in a holomorphic
family.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

/-- A holomorphic function whose value at the center is smaller in norm than all its boundary values
has a zero in the disc. -/
theorem exists_zero_of_norm_lt_boundary {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall 0 r))
    (hlt : ∀ z ∈ sphere 0 r, ‖f 0‖ < ‖f z‖) :
    ∃ z ∈ ball 0 r, f z = 0 := by
  by_contra! hn
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hz | hz
    · exact hn z hz
    · exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (hlt z hz))
  have hi : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball 0 r) := by
    refine ⟨(hf.inv hne).mono ball_subset_closedBall, ?_⟩
    rw [closure_ball (0 : ℂ) hr.ne']
    exact (hf.continuousOn.inv₀ hne)
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    isBounded_ball (nonempty_ball.mpr hr) hi
  rw [frontier_ball (0 : ℂ) hr.ne'] at hz
  have hle := hmax (subset_closure (mem_ball_self hr))
  have hpos : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0 (mem_closedBall_self hr.le))
  have hstrict := (inv_lt_inv₀ ((hpos.le).trans_lt (hlt z hz)) hpos).2 (hlt z hz)
  exact (not_le_of_gt hstrict) (by simpa [Function.comp_def, norm_inv] using hle)

/-- A zero of a continuously varying holomorphic function persists in nearby fibers if a closed disc
in the initial fiber has no boundary zeros. The parameter space only needs a topology. -/
theorem eventually_exists_zero_in_fiber {X : Type*} [TopologicalSpace X]
    {W : Set (X × ℂ)} (hW : IsOpen W) {f : X × ℂ → ℂ}
    (hf : ContinuousOn f W)
    (hd : ∀ p ∈ W, DifferentiableAt ℂ (fun z => f (p.1, z)) p.2)
    {a : X} {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ z ∈ closedBall (0 : ℂ) r, (a, z) ∈ W)
    (hzero : f (a, 0) = 0) (hboundary : ∀ z ∈ sphere (0 : ℂ) r, f (a, z) ≠ 0) :
    ∀ᶠ x in 𝓝 a, ∃ z ∈ ball (0 : ℂ) r, (x, z) ∈ W ∧ f (x, z) = 0 := by
  have hcont (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) : ContinuousAt f (a, z) :=
    hf.continuousAt (hW.mem_nhds (hdisc z hz))
  have hscont : ContinuousOn (fun z => ‖f (a, z)‖) (sphere (0 : ℂ) r) := by
    intro z hz
    exact ((hcont z (sphere_subset_closedBall hz)).comp
      (continuousAt_const.prodMk continuousAt_id)).norm.continuousWithinAt
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn
    ⟨(r : ℂ), by simp [Complex.norm_real, abs_of_pos hr]⟩ hscont
  let c := ‖f (a, b)‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr (hboundary b hb))
  have hsmall : ∀ᶠ x in 𝓝 a, ‖f (x, 0)‖ < c := by
    have hs : ContinuousAt (fun x : X => (x, (0 : ℂ))) a :=
      continuousAt_id.prodMk continuousAt_const
    apply ((hcont 0 (mem_closedBall_self hr.le)).comp
      (f := fun x : X => (x, (0 : ℂ))) hs).norm.eventually_lt continuousAt_const
    simpa [hzero] using hc
  have hlarge : ∀ᶠ x in 𝓝 a, ∀ z ∈ sphere (0 : ℂ) r, c < ‖f (x, z)‖ := by
    apply (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually
    intro z hz
    apply continuousAt_const.eventually_lt (hcont z (sphere_subset_closedBall hz)).norm
    exact (half_lt_self (norm_pos_iff.mpr (hboundary b hb))).trans_le (hmin hz)
  have hdomain : ∀ᶠ x in 𝓝 a, ∀ z ∈ closedBall (0 : ℂ) r, (x, z) ∈ W := by
    apply (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually
    exact fun z hz => hW.eventually_mem (hdisc z hz)
  filter_upwards [hsmall, hlarge, hdomain] with x hxsmall hxlarge hxdomain
  obtain ⟨z, hz, hzero⟩ := exists_zero_of_norm_lt_boundary (f := fun z => f (x, z)) hr
    (fun z hz => (hd (x, z) (hxdomain z hz)).differentiableWithinAt)
    (fun z hz => hxsmall.trans (hxlarge z hz))
  exact ⟨z, hz, hxdomain z (ball_subset_closedBall hz), hzero⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
