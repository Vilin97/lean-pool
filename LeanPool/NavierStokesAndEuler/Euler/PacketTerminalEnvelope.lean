/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData

@[expose] public section

/-! A common-radius envelope for the literal compact terminal wave. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey EulerOperatorGevreyCalculus

variable {ι : Type*} [Fintype ι]

theorem wordRadius_nonneg (δ : ℝ) : 0 ≤ wordRadius ι δ :=
  sobolevCoefficientRadius_nonneg (jetRadius δ) (jetRadius_nonneg δ)

theorem wordCost_nonneg (q : ℕ) (δ : ℝ) : 0 ≤ wordCost ι q δ :=
  sobolevCoefficientAmplitude_nonneg q (jetRadius δ) (scalarJetCost δ * terminalMass)
    (jetRadius_nonneg δ) (mul_nonneg (scalarJetCost_nonneg δ) terminalMass_nonneg)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)
  (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ) (hδ1 : δ ≤ 1)

include hd hδ1

theorem initialData_word_bound (n : ℕ) :
    block directions q (fun a => translate period a
      ((initialData D δ hδ ξ hs).value : CylinderL2 period U)) n 0 ≤
      (wordCost ι q δ*‖ξ‖)*majorant (wordRadius ι δ) 0 n := by
  apply (initialData_bound D δ hδ ξ hs directions hd q hδ1 n).trans_eq
  unfold wordCost sobolevCoefficientAmplitude
  ring

theorem initialData_common_radius (R : ℝ) (hR : wordRadius ι δ ≤ R) (n : ℕ) :
    block directions q (fun a => translate period a
      ((initialData D δ hδ ξ hs).value : CylinderL2 period U)) n 0 ≤
      (wordCost ι q δ*‖ξ‖)*majorant R 0 n :=
  (initialData_word_bound D δ hδ ξ hs directions hd q hδ1 n).trans
    (mul_le_mul_of_nonneg_left (majorant_radius_mono _ R (wordRadius_nonneg δ) hR 0 n)
      (mul_nonneg (wordCost_nonneg q δ) (norm_nonneg ξ)))

end EulerPacketTerminalDatum
