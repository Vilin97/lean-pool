/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePiola
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceConstraints

/-! Every joined high/corrector pair lies in the actual lifted solenoidal space. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerLpCylinderPaths
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

/-- Joined pair field used in packet joined source piola. -/
def joinedPairField (κ : ℝ) (p : ℕ) :
    Field P M.T (fun z => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame z
      (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high z +
        κ^(p+1) • (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector z)) :=
  (joinedSourceCoefficientData P M D τ hτ hτT B hT).inverse.multiply
    (((joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).high.smul (κ^p)).add
      ((joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).corrector.smul
          (κ^(p+1))))

theorem joinedPairField_mem
    (hc : primary.corrector = D.curlCorrector P primary.high)
    (hm : ∀ (t : Icc (0 : ℝ) M.T) x, (∫ θ in (0 : ℝ)..P, primary.high (t, (x, θ))) = 0)
    (ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)
    (κ : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (joinedPairField P M D hT τ hτ hτT B primary hprimary κ p).path t ∈
      divergenceFreeSpace P κ D.m₀ := by
  let W := joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p
  let G := W.high.changeTime hT
  let C := (W.corrector.congr (fun _ _ _ => by
    rw [joinedSource_corrector_eq P M D τ hτ hτT B primary hc p hp])).changeTime hT
  let V := piolaPairField D G C κ p
  have hs : G.path (sourceTime M D hT t) ∈ Supported P Space D.support D.support_measurable :=
    G.supported_of_raw_zero D.support D.support_measurable
      (raw_zero_changeTime hT D.support W.high_zero) _
  have hm' : ∀ x, (∫ θ in (0 : ℝ)..P,
      (joinedSourceProfiles P M D τ hτ hτT B primary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    joinedSource_high_mean_zero P M D hT τ hτ hτT B primary hprimary hm p hp t
  have ht' : ∀ x θ, inner ℝ (D.normalField (sourceTime M D hT t,(x,θ)))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    joinedSource_high_tangent_all P M D hT τ hτ hτT B primary hprimary ht p hp t
  have hV : V.path (sourceTime M D hT t) ∈ divergenceFreeSpace P κ D.m₀ :=
    piolaPairField_mem D G C κ p (sourceTime M D hT t) Ξ hΞ hF hdet hs hm' ht'
  let H := joinedPairField P M D hT τ hτ hτT B primary hprimary κ p
  have he : (H.changeTime hT).path = V.path := by
    apply Field.path_eq_of_raw_eq
    intro r x θ
    change D.FInv.field (D.clamp r) x
        (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high (r,(x,θ)) +
          κ^(p+1) • D.curlCorrector P (joinedSourceProfiles P M D τ hτ hτT B primary p).high
              (r,(x,θ))) =
      D.FInv.field (D.clamp r) x
        (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high (r,(x,θ)) +
          κ^(p+1) • (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector (r,(x,θ)))
    rw [joinedSource_corrector_eq P M D τ hτ hτT B primary hc p hp]
  have hev : H.path t = V.path (sourceTime M D hT t) :=
    (H.changeTime_apply hT t).symm.trans (congrArg (fun q => q (sourceTime M D hT t)) he)
  rw [hev]
  exact hV

end EulerPacketCylinderField
