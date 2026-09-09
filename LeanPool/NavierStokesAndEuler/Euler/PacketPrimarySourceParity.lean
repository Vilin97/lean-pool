/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimarySourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData

@[expose] public section

/-! Joint parity of the actual terminal-history primary and its continuation.
The compact terminal wave supplies the odd input without an additional
assumption on the constructed solution. -/

noncomputable section

namespace EulerTransversePacketPrimary

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerLpCylinderTranslation EulerCylinderFieldReflection

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))

include hcorrector hSym hF hM hH hY

theorem profileParity :
    ProfileParity D.T (primaryProfile O (vector τ hτ hτT B Y) (scalar τ hτ hτT B Y)) where
  high := vector_odd τ hτ hτT B Y hSym hF hM hH hY
  mean := JointOdd.zero D.T
  corrector := by
    intro t x θ
    change O.curlCorrector (vector τ hτ hτT B Y) (t,(-x,-θ)) =
      -O.curlCorrector (vector τ hτ hτT B Y) (t,(x,θ))
    rw [hcorrector]
    exact curlCorrector_odd τ hτ hτT B Y hSym hF hM hH hY t x θ
  pressure := scalarGradient_odd τ hτ hτT B Y hSym hF hM hH hY
  highPressure := scalar_even τ hτ hτT B Y hSym hF hM hH hY
  meanPressure _ _ _ := rfl

end EulerTransversePacketPrimary

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketPrimary

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
  (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector period)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)

include hcorrector hSym hF hM hH

theorem primary_profile_parity :
    ProfileParity D.T (primaryProfile O
      (vector τ hτ hτT B (initialData D δ hδ ξ hs))
      (scalar τ hτ hτT B (initialData D δ hδ ξ hs))) :=
  profileParity τ hτ hτT B (initialData D δ hδ ξ hs) O hcorrector hSym hF hM hH
    (terminal_reflection δ hδ ξ)

end EulerPacketTerminalDatum
