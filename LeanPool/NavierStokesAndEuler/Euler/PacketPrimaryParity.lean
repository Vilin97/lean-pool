/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureParity

/-! The actual homogeneous primary solution initializes the profile parity induction. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerLpCylinderTranslation EulerCylinderFieldReflection

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {raw : VectorField}

theorem ProfileParity.primary (G : EulerTransversePacketProvider.Forcing P D raw)
    (I : EulerTransversePacketProvider.InitialData P D) (O : Operators)
    (hcorrector : O.curlCorrector = D.curlCorrector P)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hraw : JointOdd D.T raw)
    (hI : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U)) :
    ProfileParity D.T (primaryProfile O (G.vector I) (G.scalar I)) where
  high := G.vector_odd I hSym hF hM hraw hI
  mean := JointOdd.zero D.T
  corrector := by
    intro t x θ
    change O.curlCorrector (G.vector I) (t,(-x,-θ)) = -O.curlCorrector (G.vector I) (t,(x,θ))
    rw [hcorrector,G.curlCorrector_eq I t (-x) (-θ),G.curlCorrector_eq I t x θ]
    exact G.corrector_odd_of_data I hSym hF hM hraw hI t x θ
  pressure := G.scalarGradient_odd I hSym hF hM hraw hI
  highPressure := G.scalar_even I hSym hF hM hraw hI
  meanPressure _ _ _ := rfl

theorem homogeneousPrimaryParity (D : EulerTransversePacketProvider.Data U)
    (I : EulerTransversePacketProvider.InitialData P D) (O : Operators)
    (hcorrector : O.curlCorrector = D.curlCorrector P)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hI : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U)) :
    ProfileParity D.T (homogeneousPrimary D I O) :=
  ProfileParity.primary (homogeneousForcing D) I O hcorrector hSym hF hM (JointOdd.zero D.T) hI

end EulerPacketCylinderField
