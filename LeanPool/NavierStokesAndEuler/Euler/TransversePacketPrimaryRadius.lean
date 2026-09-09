/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCommonRadius

/-!
The additional primary guards can be met by one explicit enlargement of
the common external radius. Neither source coefficients nor profile costs
are changed. The extra lower bound can include the actual terminal-wave
radius, before the recursive solve begins.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary

open EulerTransversePacketProvider EulerParameterWordGevrey EulerTransverseFixedSobolev
  EulerTimeLpGramSobolev  EulerFixedEvolutionSobolev
  EulerCylinderDirichlet.Coefficients EulerSourceCylinderForwardSobolev EulerLinearDuhamel

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q)

/-- Weak radius as an element of `ℝ`. -/
def weakRadius : ℝ :=
  2*blockCost ι q τ L.Rc L.C₀ L.C₁ L.CH (D.initial τ hτ hτT.le).frameLower
    (endpointForcingCost ι q τ L.Rc L.C₁)*(sobolevCoefficientRadius ι L.Rc+1)

/-- Strong radius as an element of `ℝ`. -/
def strongRadius : ℝ :=
  2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
    (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁ (endpointForcingCost ι q τ L.Rc L.C₁) 1) *
      (sobolevCoefficientRadius ι L.Rc+1)

/-- Uniform radius as an element of `ℝ`. -/
def uniformRadius : ℝ :=
  2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
    (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁ (endpointForcingCost ι q τ L.Rc L.C₁) (traceCost
        τ)) *
      (sobolevCoefficientRadius ι L.Rc+1)

/-- Forward radius as an element of `ℝ`. -/
def forwardRadius : ℝ :=
  2*forwardSobolevCost ι q (D.T-τ) L.C (τ⁻¹+traceCost τ)
    (forcingCost ι q L.Ri L.C₀*0) (18*L.Ri*L.C₀*L.C₁) (4*L.Ri) *
      (sobolevCoefficientRadius ι (4*L.Ri)+1)

/-- Required radius, given by `max extra (max L.R (max (weakRadius L) (max (strongRadius L) (max
(uniformRadius L) (forwardRadius L)))))`. -/
def requiredRadius (extra : ℝ) : ℝ :=
  max extra (max L.R (max (weakRadius L) (max (strongRadius L) (max (uniformRadius L)
      (forwardRadius L)))))

theorem le_requiredRadius (extra : ℝ) : L.R ≤ requiredRadius L extra :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem extra_le_requiredRadius (extra : ℝ) : extra ≤ requiredRadius L extra := le_max_left _ _

/-- Enlarge for primary, given by `L.enlargeRadius (requiredRadius L extra) (le_requiredRadius L
extra)`. -/
def enlargeForPrimary (extra : ℝ) : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q :=
  L.enlargeRadius (requiredRadius L extra) (le_requiredRadius L extra)

theorem requiredBudget (extra : ℝ) : Budget (enlargeForPrimary L extra) := {
  history_weak := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  history_strong := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  history_uniform := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  forward_radius := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) }

namespace Budget

variable {L} (H : Budget L) (R' : ℝ) (hR : L.R ≤ R')

include H in
theorem enlargeRadius : Budget (L.enlargeRadius R' hR) := {
  history_weak := H.history_weak.trans hR
  history_strong := H.history_strong.trans hR
  history_uniform := H.history_uniform.trans hR
  forward_radius := H.forward_radius.trans hR }

@[simp] theorem enlargeRadius_velocityCost : (H.enlargeRadius R' hR).velocityCost = H.velocityCost
    := rfl

@[simp] theorem enlargeRadius_derivativeCost : (H.enlargeRadius R' hR).derivativeCost =
    H.derivativeCost := rfl

end Budget
end EulerTransversePacketPrimary
