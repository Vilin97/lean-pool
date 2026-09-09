/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalAdmissible
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalDatumBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing

@[expose] public section

/-! The manuscript's literal compact wave is an admissible terminal coordinate field. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)

def initialData : InitialData period D where
  value := ⟨terminal δ hδ ξ,terminal_supported δ hδ ξ D.support D.support_measurable hs⟩
  orbit := terminal_orbit_contDiff δ hδ ξ
  mean_zero := terminal_average_zero δ hδ ξ

theorem initialData_value : ((initialData D δ hδ ξ hs).value : CylinderL2 period U) =
    terminal δ hδ ξ := rfl

theorem initialData_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hδ1 : δ ≤ 1) (n : ℕ) :
    block directions q (fun b => translate period b
      ((initialData D δ hδ ξ hs).value : CylinderL2 period U)) n 0 ≤
      sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * ‖ξ‖ * terminalMass) *
        majorant (wordRadius ι δ) 0 n :=
  terminal_block_bound directions hd q δ hδ hδ1 ξ n 0

end EulerPacketTerminalDatum
