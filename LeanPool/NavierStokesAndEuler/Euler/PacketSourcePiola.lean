/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPiolaPair
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceMeanZero
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique

@[expose] public section

/-! The genuine Piola constraint for every generated source high/corrector pair. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerLpCylinderPaths
open scoped ContDiff

theorem Field.changeTime_apply {P T T' : ℝ} [Fact (0 < P)] {raw : VectorField}
    (G : Field P T raw) (h : T = T') (t : Icc (0 : ℝ) T) :
    (G.changeTime h).path ⟨t,by rw [← h]; exact t.property⟩ = G.path t := by
  subst T'
  rfl

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

def sourceTime (t : Icc (0 : ℝ) M.T) : Icc (0 : ℝ) D.T :=
  ⟨t,by rw [← hT]; exact t.property⟩

def sourcePairField (κ : ℝ) (p : ℕ) :
    Field P M.T (fun z => (sourceOperators P M D I).inverseFrame z
      (κ^p • (sourceProfiles P M D I Iprimary p).high z +
        κ^(p+1) • (sourceProfiles P M D I Iprimary p).corrector z)) :=
  (sourceCoefficientData P M D I hT).inverse.multiply
    (((sourceProfileWitness P M D hT I Iprimary p).high.smul (κ^p)).add
      ((sourceProfileWitness P M D hT I Iprimary p).corrector.smul (κ^(p+1))))

theorem sourcePairField_mem (κ : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (sourcePairField P M D hT I Iprimary κ p).path t ∈ divergenceFreeSpace P κ D.m₀ := by
  let W := sourceProfileWitness P M D hT I Iprimary p
  let G := W.high.changeTime hT
  let C := (W.corrector.congr (fun _ _ _ => by rw [source_corrector_eq P M D I Iprimary p
    hp])).changeTime hT
  let V := piolaPairField D G C κ p
  have hs : G.path (sourceTime M D hT t) ∈ Supported P Space D.support D.support_measurable :=
    G.supported_of_raw_zero D.support D.support_measurable
      (raw_zero_changeTime hT D.support W.high_zero) _
  have hm : ∀ x, (∫ θ in (0 : ℝ)..P,
      (sourceProfiles P M D I Iprimary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    source_high_mean_zero P M D hT I Iprimary p _
  have ht : ∀ x θ, inner ℝ (D.normalField (sourceTime M D hT t,(x,θ)))
      ((sourceProfiles P M D I Iprimary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    source_high_tangent P M D hT I Iprimary p _
  have hV : V.path (sourceTime M D hT t) ∈ divergenceFreeSpace P κ D.m₀ :=
    piolaPairField_mem D G C κ p (sourceTime M D hT t) Ξ hΞ hF hdet hs hm ht
  let H := sourcePairField P M D hT I Iprimary κ p
  have he : (H.changeTime hT).path = V.path := by
    apply Field.path_eq_of_raw_eq
    intro r x θ
    change D.FInv.field (D.clamp r) x
        (κ^p • (sourceProfiles P M D I Iprimary p).high (r,(x,θ)) +
          κ^(p+1) • D.curlCorrector P (sourceProfiles P M D I Iprimary p).high (r,(x,θ))) =
      D.FInv.field (D.clamp r) x
        (κ^p • (sourceProfiles P M D I Iprimary p).high (r,(x,θ)) +
          κ^(p+1) • (sourceProfiles P M D I Iprimary p).corrector (r,(x,θ)))
    rw [source_corrector_eq P M D I Iprimary p hp]
  have hev : H.path t = V.path (sourceTime M D hT t) :=
    (H.changeTime_apply hT t).symm.trans (congrArg (fun q => q (sourceTime M D hT t)) he)
  rw [hev]
  exact hV

end EulerPacketCylinderField
