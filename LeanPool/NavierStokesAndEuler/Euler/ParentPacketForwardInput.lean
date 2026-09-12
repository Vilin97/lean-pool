/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketShortTimePhysicalGrowth
public import LeanPool.NavierStokesAndEuler.Euler.PacketCommonRadius

/-! The first packet's complete source budgets come from actual parent
label fields and its short-time low strain bound. The growth profile is
the constant one, proved by the actual tangent equation. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourcePropagator
  EulerPacketParentLabelBounds EulerPacketPiola

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Forward inputs data, collecting `linear`, `normal`, `mean`. -/
structure ForwardInputs (M : EulerMeanPacketProvider.Data) (D : Data U) where
  /-- Linear of `ForwardInputs`, of type `EulerTransversePacketForward.Budget D (Fin 4) 6`. -/
  linear : EulerTransversePacketForward.Budget D (Fin 4) 6
  /-- Normal of `ForwardInputs`, of type `EulerTransversePacketJoin.NormalBudget D 6 linear.R`. -/
  normal : EulerTransversePacketJoin.NormalBudget D 6 linear.R
  /-- Mean field of `ForwardInputs`, of type `EulerMeanPacketProvider.Budget M 6 linear.R`. -/
  mean : EulerMeanPacketProvider.Budget M 6 linear.R

namespace LabelData

variable {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (CM : ℝ) (hCM : 0 ≤ CM)
  (hM : ∀ t x, ‖x‖ ≤ (1 / 2 : ℝ) → ‖G.strain.field t x‖ ≤ CM)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hshort : CM * G.T ≤ 1 / 2)

/-- Forward raw, constructed using `shortPhysicalForwardBudget`. -/
def forwardRaw : EulerTransversePacketForward.Budget (G.transverseData m hm R S hS) (Fin 4) 6 :=
  shortPhysicalForwardBudget (G.transverseData m hm R S hS) 6 L.scaledRadius
    (frameAmplitude L.K) (gradientAmplitude L.K) CM L.scaledRadius_nonneg
    (frameAmplitude_nonneg L.K) (gradientAmplitude_nonneg L.K) hCM
    G.frame_det L.frame_scaled_bound L.first_scaled_bound hM Ω hΩ hΩo hsub hΩball hshort

/-- Forward inputs as an element of `ForwardInputs (G.meanData H) (G.transverseData m hm R S
hS)`. -/
def forwardInputs (Ti : ℝ) (hT1 : G.T ≤ 1) (hTi : G.T⁻¹ ≤ Ti) :
    ForwardInputs (G.meanData H) (G.transverseData m hm R S hS) := by
  let A := L.forwardRaw m hm R S hS CM hCM hM Ω hΩ hΩo hsub hΩball hshort
  let N := L.normalBudget m hm R S hS 6
  let M := L.meanBudget H 6 Ti hT1 hTi
  let Rn := EulerPacketParentNormalBudget.radius (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K)
  let Rm := EulerPacketParentMeanBudget.radius 6 G.T Ti (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L
  let Rc := max A.R (max Rn Rm)
  exact {
    linear := A.enlargeRadius Rc (le_max_left _ _)
    normal := N.enlargeRadius Rc ((le_max_left Rn Rm).trans (le_max_right _ _))
    mean := M.enlargeRadius Rc ((le_max_right Rn Rm).trans (le_max_right _ _)) }

theorem forwardInputs_growth (Ti : ℝ) (hT1 : G.T ≤ 1) (hTi : G.T⁻¹ ≤ Ti) :
    (L.forwardInputs H m hm R S hS CM hCM hM Ω hΩ hΩo hsub hΩball hshort Ti hT1 hTi).linear.g=1 :=
        rfl

end LabelData
end EulerParentPacketFrames
