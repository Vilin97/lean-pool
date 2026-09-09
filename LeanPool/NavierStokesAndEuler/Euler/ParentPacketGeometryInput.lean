/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryJoinedBudget

/-! The actual activation geometry fills the remaining propagator input
in the parent-to-packet constructor. All three source budgets share one
radius and retain the growth profile derived from that geometry. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourceGeometry

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (J : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti TiTotal : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

/-- Geometry inputs, constructed using `L.joinedInputs`. -/
def geometryInputs :
    JoinedInputs (G.meanData H) (G.transverseData m hm R S hS) τ hτ hτT
      (G.historyOn H m hm R S hS τ hτ hτT) :=
  L.joinedInputs H m hm R S hS τ hτ hτT Ti (560*P.horizon^10/P.epsilon)
    hτ1 hTi J.growth_constant_pos.le (J.sourceGrowthProfile hball)
    (J.sourceGrowthProfile_positive hball) (J.sourceGrowthProfile_initial hball)
    Ω hΩ hΩo hsub hΩball (J.sourceGrowthProfile_propagator hball) TiTotal hT1 hTiTotal

theorem geometryInputs_growth :
    (L.geometryInputs H m hm R S hS τ hτ hτT P J hball Ti TiTotal hτ1 hTi
      hT1 hTiTotal Ω hΩ hΩo hsub hΩball).linear.g=J.sourceGrowthProfile hball := rfl

end EulerParentPacketFrames.LabelData
