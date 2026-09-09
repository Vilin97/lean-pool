/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPiolaCorrector
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldSupport

@[expose] public section

/-! Every actual compact high/corrector pair is a member of the closed lifted solenoidal space. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSmoothOrbit EulerLpCylinderPaths EulerPacketProfileRecursion
  EulerPacketConstructedPiola
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

def packetInverseCoefficient : MatrixCoefficient D.T
    (fun z => D.FInv.field (D.clamp z.1) z.2.1) where
  path := D.FInv.field
  orbit := D.FInv.translation_contDiff
  raw_eq t _ _ := by rw [EulerTransversePacketProvider.Data.clamp_coe]

def piolaPairRaw (κ : ℝ) (raw : VectorField) (p : ℕ) : VectorField := fun z =>
  D.FInv.field (D.clamp z.1) z.2.1 (κ^p • raw z+κ^(p+1) • D.curlCorrector P raw z)

def piolaPairField {raw : VectorField} (G : Field P D.T raw)
    (C : Field P D.T (D.curlCorrector P raw)) (κ : ℝ) (p : ℕ) :
    Field P D.T (piolaPairRaw (P := P) D κ raw p) :=
  (packetInverseCoefficient D).multiply ((G.smul (κ^p)).add (C.smul (κ^(p+1))))

theorem piolaPairField_mem {raw : VectorField} (G : Field P D.T raw)
    (C : Field P D.T (D.curlCorrector P raw)) (κ : ℝ) (p : ℕ) (t : Icc (0 : ℝ) D.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field t x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (hs : G.path t ∈ Supported P Space D.support D.support_measurable)
    (hm : ∀ x, (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0)
    (htan : ∀ x θ, inner ℝ (D.normalField (t,(x,θ))) (raw (t,(x,θ))) = 0) :
    (piolaPairField D G C κ p).path t ∈ divergenceFreeSpace P κ D.m₀ := by
  let A := pointField P G.path G.orbit t
  have hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x) := pointField_smooth P G.path G.orbit t
  have hAc : HasCompactSupport A := by
    change HasCompactSupport (pointField P G.path G.orbit t)
    rw [pointField_eq_representative]
    exact representative_hasCompactSupport P D.support D.support_measurable D.support_compact
      (G.path t) (path_evaluation_smooth P G.path G.orbit t) hs
  have hAm : ∀ x, (∫ θ in (0 : ℝ)..P, A (x,(θ : AddCircle P))) = 0 :=
    rawMean_pointField D G t hm
  have hN : ContDiff ℝ ∞ (EulerPacketConstructedPiola.normal (D.deformationEquiv t) D.m₀) :=
    D.normal.smooth t
  have hAt : ∀ z, inner ℝ (EulerPacketConstructedPiola.normal (D.deformationEquiv t) D.m₀ z.1)
      (A z) = 0 := by
    intro z
    obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
    have ht := htan z.1 θ
    rw [EulerTransversePacketProvider.Data.normalField,
      EulerTransversePacketProvider.Data.clamp_coe,G.raw_eq,hθ] at ht
    exact ht
  let L := pairLp P κ D.m₀ Ξ A hΞ hAc (D.deformationEquiv t) hN D.initialNormal_ne_zero hA hAm p
  have hL : L ∈ divergenceFreeSpace P κ D.m₀ :=
    pairLp_mem P κ D.m₀ Ξ A hΞ hAc (D.deformationEquiv t) hN D.initialNormal_ne_zero hA hAm p
  have hLrep := pairLp_ae P κ D.m₀ Ξ A hΞ hAc (D.deformationEquiv t) hN
    D.initialNormal_ne_zero hA hAm hF hdet hAt p
  let H := piolaPairField D G C κ p
  have he : H.path t = L := by
    apply Lp.ext
    filter_upwards [pointField_ae P H.path H.orbit t,hLrep] with z hp' hl
    obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
    have hh := H.raw_eq t z.1 θ
    rw [hθ] at hh
    calc
      H.path t z = pointField P H.path H.orbit t z := hp'
      _ = piolaPairRaw (P := P) D κ raw p (t,(z.1,θ)) := hh.symm
      _ = (D.deformationEquiv t z.1).symm
          (κ^p • A z+κ^(p+1) • EulerPacketConstructedPiola.corrector P
            (D.deformationEquiv t) D.m₀ A z) := by
        change D.FInv.field (D.clamp t) z.1
          (κ^p • raw (t,(z.1,θ))+κ^(p+1) • D.curlCorrector P raw (t,(z.1,θ))) = _
        rw [EulerTransversePacketProvider.Data.clamp_coe,G.raw_eq,
          rawCorrector_eq_lifted D G t hm,hθ]
        rfl
      _ = L z := hl.symm
  rw [show (piolaPairField D G C κ p).path t = L from he]
  exact hL

end EulerPacketCylinderField
