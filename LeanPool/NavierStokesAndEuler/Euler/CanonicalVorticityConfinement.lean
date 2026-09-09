/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
public import LeanPool.NavierStokesAndEuler.Euler.StageDisplacementConfinement
import LeanPool.NavierStokesAndEuler.Euler.CanonicalPacketHorizons
import LeanPool.NavierStokesAndEuler.Euler.H3CurlConvergence
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution
import LeanPool.NavierStokesAndEuler.Euler.StageVorticityConfinement

/-!
# Uniformly compact vorticity of the canonical packet solution

All finite packet horizons contain the maximal open lifespan. H³ stability
therefore passes their common vorticity support to every shorter ordinary
Euler evolution, and hence to the canonical maximal field itself.
-/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerMeanCutoffCurl EulerSmoothL2Series
open scoped Topology

/-- Canonical vorticity ball, given by `Metric.closedBall 0 (2 + particleDisplacementCap
constructionScales le_rfl le_rfl)`. -/
def canonicalVorticityBall : Set Space :=
  Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl)

theorem canonicalVorticityBall_compact : IsCompact canonicalVorticityBall :=
  isCompact_closedBall _ _

theorem evolution_vorticity_support (S : ℝ) (hS : 0 < S) (hSL : S < lifespan.duration)
    (t : Icc (0 : ℝ) S) :
    tsupport (vectorCurl ((lifespan.evolution S hS hSL).velocity t).field) ⊆
      canonicalVorticityBall := by
  let U := lifespan.evolution S hS hSL
  let hST : ∀ n, S ≤ (packets n).parent.T :=
    fun n => hSL.le.trans (lifespan_le_packet_horizon n)
  let V : ℕ → Evolution S hS.le := fun n =>
    (packets n).state.regularity.ordinaryEvolution.restrictTime S hS.le (hST n)
  have hfield (n : ℕ) (s : Icc (0 : ℝ) S) : ((V n).velocity s).field =
      fun x => (packets n).state.evolution.velocity (s,x) := by
    funext x
    exact ((packets n).state.regularity.velocity_match
      ⟨s,s.property.1,s.property.2.trans (hST n)⟩ x).symm
  have hnorm (n : ℕ) : tensorNorm 3 (U.difference (V n) ⟨0,le_rfl,hS.le⟩) =
      derivativeSum 3 ((fun x => (packets n).state.evolution.velocity (0,x)) -
        initialDatum.field) := by
    rw [tensorNorm_eq_derivativeSum]
    congr 1
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((V n).velocity ⟨0,le_rfl,hS.le⟩).field x -
      ((lifespan.evolution S hS hSL).velocity ⟨0,le_rfl,hS.le⟩).field x = _
    rw [hfield,lifespan.evolution_initial S hS hSL]
    rfl
  have hinit : Tendsto (fun n => tensorNorm 3
      (U.difference (V n) ⟨0,le_rfl,hS.le⟩)) atTop (𝓝 0) := by
    simpa only [hnorm] using initialDatum_Hm 3
  have hsupport (n : ℕ) : tsupport (vectorCurl ((V n).velocity t).field) ⊆
      canonicalVorticityBall := by
    rw [hfield]
    exact packets_vorticity_support n ⟨t,t.property.1,t.property.2.trans (hST n)⟩
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hout
  have hz (n : ℕ) : vectorCurl ((V n).velocity t).field x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hout (hsupport n hm))
  have hzero : Tendsto (fun n => vectorCurl ((V n).velocity t).field x) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Space)) atTop (𝓝 0))
  exact hx (tendsto_nhds_unique (U.curl_tendsto_of_initial_h3 V hinit t x) hzero)

theorem canonical_vorticity_support (t : lifespan.Time) :
    tsupport (vectorCurl (lifespan.maximalVelocity t)) ⊆ canonicalVorticityBall :=
  evolution_vorticity_support (lifespan.intermediateHorizon t)
    (lifespan.intermediateHorizon_pos t) (lifespan.intermediateHorizon_lt t)
    (lifespan.intermediateTime t)

theorem canonical_vorticity_eq_zero_outside (t : lifespan.Time) (x : Space)
    (hx : x ∉ canonicalVorticityBall) : vectorCurl (lifespan.maximalVelocity t) x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hm => hx (canonical_vorticity_support t hm))

theorem canonical_vorticity_hasCompactSupport (t : lifespan.Time) :
    HasCompactSupport (vectorCurl (lifespan.maximalVelocity t)) :=
  canonicalVorticityBall_compact.of_isClosed_subset (isClosed_tsupport _)
    (canonical_vorticity_support t)

end EulerPacketInduction
