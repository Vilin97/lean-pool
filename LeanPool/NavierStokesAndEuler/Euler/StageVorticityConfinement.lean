/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StageDisplacementConfinement
import LeanPool.NavierStokesAndEuler.Euler.PacketCurlTransport
import LeanPool.NavierStokesAndEuler.Euler.StageDisplacementBound
import LeanPool.NavierStokesAndEuler.Euler.StageInitialSupport

/-! Every selected finite packet has vorticity supported in one fixed ball
throughout its horizon. Initial support, the actual vorticity transport law,
and the summable particle-map displacement bound supply the three ingredients. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerMeanCutoffCurl Euler.ComparatorBridge

theorem packets_vorticity_support (n : ℕ)
    (t : Icc (0 : ℝ) (packets n).parent.T) :
    tsupport (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x))) ⊆
      Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  exact support_subset_of_transport ((packets n).parent.position t)
    ((packets n).state.evolution.inverse.field t)
    (vectorCurl (fun x => (packets n).state.evolution.velocity (0,x)))
    (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x)))
    ((packets n).state.evolution.inverse.right_inverse t)
    (packets_position_mapsTo_closedBall 2 n t)
    ((subset_tsupport _).trans (packets_initial_curl_support n))
    (fun a ha => (packets n).state.evolution.curl_eq_zero_along_position a ha t)

end EulerPacketInduction
