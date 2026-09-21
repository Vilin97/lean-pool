/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Foundation
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Stage 8: attainment of the Euclidean solution radius

The public radius is defined as an `sInf`.  In the Euclidean branch that
infimum is attained: the minimizer set is closed because the objective is
differentiable, and the literal finite-sum `lpNorm 2` is the norm transported
to the finite-dimensional `PiLp 2` space.  A closest point in that proper
space therefore gives an actual optimizer at the exact frozen radius.
-/

namespace O3.Stage8EuclideanRadius

open O3

private abbrev EuclideanLpSpace (d : ℕ) :=
  PiLp (ENNReal.ofReal (2 : ℝ)) (fun _ : Fin d ↦ ℝ)

/-- The minimizer set of an admissible Euclidean instance is closed. -/
theorem minimizerSet_isClosed {d : ℕ} (P : AdmissibleInstance d 2) :
    IsClosed (MinimizerSet P.f) := by
  have hf : Continuous P.f := continuous_iff_continuousAt.mpr fun x ↦
    (P.gradient_spec x).1.continuousAt
  change IsClosed {x | ∀ y, P.f x ≤ P.f y}
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun y ↦
      isClosed_le hf (continuous_const : Continuous (fun _ : Vec d ↦ P.f y)))

/-- The literal `lpNorm 2` is exactly distance after transport to `PiLp 2`. -/
theorem lpNorm_two_eq_transport_dist {d : ℕ} (x y : Vec d) :
    lpNorm 2 (x - y) =
      dist
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) x : EuclideanLpSpace d)
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) y : EuclideanLpSpace d) := by
  rw [Stage2RouteC.lpNorm_eq_piLpNorm (p := (2 : ℝ)) (by norm_num)]
  change
    ‖(WithLp.toLp (ENNReal.ofReal (2 : ℝ)) (x - y) : EuclideanLpSpace d)‖ =
      ‖(WithLp.toLp (ENNReal.ofReal (2 : ℝ)) x : EuclideanLpSpace d) -
        WithLp.toLp (ENNReal.ofReal (2 : ℝ)) y‖
  rfl

/-- The source `sInf` radius is attained by a genuine optimizer. -/
theorem exists_minimizer_at_radius {d : ℕ} (P : AdmissibleInstance d 2) :
    ∃ xstar : Vec d,
      xstar ∈ MinimizerSet P.f ∧ lpNorm 2 (xstar - P.x0) = P.radius := by
  let e : Vec d ≃ₜ EuclideanLpSpace d :=
    (PiLp.homeomorph (ENNReal.ofReal (2 : ℝ)) (fun _ : Fin d ↦ ℝ)).symm
  let S : Set (EuclideanLpSpace d) := e '' MinimizerSet P.f
  let _ : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let _ : ProperSpace (EuclideanLpSpace d) :=
    FiniteDimensional.proper ℝ (EuclideanLpSpace d)
  have hSclosed : IsClosed S := e.isClosedMap _ (minimizerSet_isClosed P)
  have hSne : S.Nonempty := P.minimizer_nonempty.image e
  obtain ⟨z, hzS, hz⟩ := hSclosed.exists_infDist_eq_dist hSne (e P.x0)
  rcases hzS with ⟨xstar, hxstar, rfl⟩
  refine ⟨xstar, hxstar, ?_⟩
  let distances : Set ℝ :=
    (fun x : Vec d ↦ lpNorm 2 (x - P.x0)) '' MinimizerSet P.f
  have hnonempty : distances.Nonempty := P.minimizer_nonempty.image _
  have hbelow : BddBelow distances := ⟨0, by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact lpNorm_nonneg 2 (x - P.x0)⟩
  have hle : lpNorm 2 (xstar - P.x0) ≤ sInf distances := by
    apply le_csInf hnonempty
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hxS : e x ∈ S := ⟨x, hx, rfl⟩
    change lpNorm 2 (xstar - P.x0) ≤ lpNorm 2 (x - P.x0)
    rw [lpNorm_two_eq_transport_dist, lpNorm_two_eq_transport_dist]
    change dist (e xstar) (e P.x0) ≤ dist (e x) (e P.x0)
    rw [dist_comm (e xstar) (e P.x0), dist_comm (e x) (e P.x0)]
    calc
      dist (e P.x0) (e xstar) = Metric.infDist (e P.x0) S := hz.symm
      _ ≤ dist (e P.x0) (e x) := Metric.infDist_le_dist_of_mem hxS
  have hge : sInf distances ≤ lpNorm 2 (xstar - P.x0) :=
    csInf_le hbelow ⟨xstar, hxstar, rfl⟩
  change lpNorm 2 (xstar - P.x0) = sInf distances
  exact le_antisymm hle hge

/-- Exact optimizer interface consumed by the Euclidean estimate-sequence
evaluation: no closest optimizer is added to the public instance data. -/
theorem exists_minimizer_within {d : ℕ} (P : AdmissibleInstance d 2)
    {D : ℝ} (hDR : P.radius ≤ D) :
    ∃ xstar : Vec d,
      xstar ∈ MinimizerSet P.f ∧ lpNorm 2 (xstar - P.x0) ≤ D := by
  obtain ⟨xstar, hxstar, hr⟩ := exists_minimizer_at_radius P
  exact ⟨xstar, hxstar, hr.trans_le hDR⟩

end O3.Stage8EuclideanRadius
