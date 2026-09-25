/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteBadScaleTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal

/-! # Absolute Minimal Scale -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# Absolute quantitative minimal scale

This file converts the absolute bad-tail estimate into the corresponding
localized quenched estimate above an explicit absolute minimal scale.
-/

noncomputable section

theorem exists_quantitative_absolute_quenchedLocalizedEstimate_interpolated
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct CcrudeShift Csmall Centry a : ℝ,
      0 < Cfluct ∧ 0 < CcrudeShift ∧ 0 < Csmall ∧
      0 < Centry ∧ 0 < a ∧
      ∀ {t α : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let ctop : ℝ :=
          min (t - α)
            (min (b - α)
              (min ((t - α) * (1 + b / a))
                (b - α * (1 + b / a))))
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - α) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - α)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
        let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
        let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
        let Mshift : ℝ :=
          max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
            max 0 ((S.card : ℝ) * Kcrude))
        let ρgap : ℝ := (3 : ℝ) ^ η
        0 < t →
        t ≤ b →
        0 ≤ α →
        α < t →
        α < b →
        α * (1 + b / a) < b →
        α < a →
        ∃ Rshift Rsmall Runion : ℕ,
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let H : ℕ → ℕ → RegCoeffField d → ℝ :=
              quenchedProbeEnvelope hP hStruct
            let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
            let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
            let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
            let Ohigh : ℝ := (τ * b * (L + 1)) / η
            let Ocrude : ℝ := (σ * t * (L + 1)) / η
            let BleadShift : ℝ :=
              max (DenShift * (3 : ℝ) ^ Ohigh)
                (DenShift * (3 : ℝ) ^ Ocrude)
            let BtailShift : ℝ := 2 * BleadShift
            let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
            let QprefShift : ℕ :=
              max (Nat.ceil (max 0 (Real.log Mshift)))
                (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
                  Real.log ρgap)))
            let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
            let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
            let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
            let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
            let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
            let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
            let prefSmall : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
            let Msmall : ℝ := max 1 (max 0 (prefSmall * Ksmall))
            let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
            let BtailSmall : ℝ := 2 * BleadSmall
            let cgapSmall : ℝ := BleadSmall ^ (-η) - BtailSmall ^ (-η)
            let QprefSmall : ℕ :=
              max (Nat.ceil (max 0 (Real.log Msmall)))
                (max Rsmall (Nat.ceil ((2 * max 0 (-(Real.log cgapSmall))) /
                  Real.log ρgap)))
            let QleadSmall : ℕ := Nat.ceil (Real.log BleadSmall / Real.log 3)
            let Qsmall : ℕ := max QprefSmall QleadSmall
            let BleadUnion : ℝ := max BtailShift BtailSmall
            let BtailUnion : ℝ := 2 * BleadUnion
            let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
            let Qunion : ℕ :=
              max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
                (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
                  Real.log ρgap)))
            let Q : ℕ := max Qshift (max Qsmall Qunion)
            let B : ℝ := max 1 BtailUnion
            let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent H t α
            let X : RegCoeffField d → ℝ := quenchedMinimalScale (N0 + Q) Bad
            IsBigO P (gammaSigma η) X
              (3 * ((3 : ℝ) ^ (N0 + Q)) * B) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Cfluct, CcrudeShift, Csmall, Centry, a,
      hCfluct, hCcrudeShift, hCsmall, hCentry, ha, htailBase⟩ :=
    exists_quantitative_threshold_absoluteBadTail_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, CcrudeShift, Csmall, Centry, a,
    hCfluct, hCcrudeShift, hCsmall, hCentry, ha, ?_⟩
  intro t α
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - α)
      (min (b - α)
        (min ((t - α) * (1 + b / a))
          (b - α * (1 + b / a))))
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - α) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - α)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let Ctop : ℝ :=
    (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
  let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
  let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
  let Mshift : ℝ :=
    max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
      max 0 ((S.card : ℝ) * Kcrude))
  let ρgap : ℝ := (3 : ℝ) ^ η
  obtain ⟨Rshift, Rsmall, Runion, htailLaw⟩ :=
    htailBase (t := t) (α := α)
      ht htb hα_nonneg hαt hαb hαharm hαa
  refine ⟨Rshift, Rsmall, Runion, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let H : ℕ → ℕ → RegCoeffField d → ℝ :=
    quenchedProbeEnvelope hP hStruct
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
  let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let BleadShift : ℝ :=
    max (DenShift * (3 : ℝ) ^ Ohigh) (DenShift * (3 : ℝ) ^ Ocrude)
  let BtailShift : ℝ := 2 * BleadShift
  let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
  let QprefShift : ℕ :=
    max (Nat.ceil (max 0 (Real.log Mshift)))
      (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
        Real.log ρgap)))
  let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
  let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
  let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
  let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
  let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
  let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
  let prefSmall : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
  let Msmall : ℝ := max 1 (max 0 (prefSmall * Ksmall))
  let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
  let BtailSmall : ℝ := 2 * BleadSmall
  let cgapSmall : ℝ := BleadSmall ^ (-η) - BtailSmall ^ (-η)
  let QprefSmall : ℕ :=
    max (Nat.ceil (max 0 (Real.log Msmall)))
      (max Rsmall (Nat.ceil ((2 * max 0 (-(Real.log cgapSmall))) /
        Real.log ρgap)))
  let QleadSmall : ℕ := Nat.ceil (Real.log BleadSmall / Real.log 3)
  let Qsmall : ℕ := max QprefSmall QleadSmall
  let BleadUnion : ℝ := max BtailShift BtailSmall
  let BtailUnion : ℝ := 2 * BleadUnion
  let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
  let Qunion : ℕ :=
    max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
      (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
        Real.log ρgap)))
  let Q : ℕ := max Qshift (max Qsmall Qunion)
  let B : ℝ := max 1 BtailUnion
  let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent H t α
  let X : RegCoeffField d → ℝ := quenchedMinimalScale (N0 + Q) Bad
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hBtailUnion_pos : 0 < BtailUnion := by
    have hDenShift_pos : 0 < DenShift := by
      simpa [DenShift] using
        mixedBottomTailDenominator_pos
          (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
    have hBleadShift_pos : 0 < BleadShift := by
      have hleft : 0 < DenShift * (3 : ℝ) ^ Ohigh :=
        mul_pos hDenShift_pos
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh)
      exact hleft.trans_le (le_max_left _ _)
    have hBtailShift_pos : 0 < BtailShift := by
      dsimp [BtailShift]
      positivity
    have hBleadUnion_pos : 0 < BleadUnion :=
      hBtailShift_pos.trans_le (le_max_left _ _)
    dsimp [BtailUnion]
    positivity
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact le_max_left 1 BtailUnion
  have htail_abs :
      ∀ N : ℕ, N0 + Q ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - (N0 + Q) : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hN
    let q : ℕ := N - N0
    have hN0q : N0 + q = N := by
      dsimp [q]
      exact Nat.add_sub_of_le (le_trans (Nat.le_add_right N0 Q) hN)
    have hQq : Q ≤ q := by
      dsimp [q]
      omega
    have htail_q :
        P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
          Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) := by
      simpa [K, S, b, L, ctop, τ, η, w, ρtop, ρbottom, ρcrude,
        Cbottom, Ctop, Kbottom, Kcrude, Mshift, ρgap, N0, H, Dhigh,
        Dcrude, DenShift, Ohigh, Ocrude, BleadShift, BtailShift,
        cgapShift, QprefShift, QleadShift, QcutShift, Qshift,
        scaleSmall, ρsmall, Ksmall, prefSmall, Msmall, BleadSmall,
        BtailSmall, cgapSmall, QprefSmall, QleadSmall, Qsmall,
        BleadUnion, BtailUnion, cgapUnion, Qunion, Q] using
        htailLaw hP hStruct hΓ hσ_eq hparams q hQq
    have hcompare :
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - (N0 + Q) : ℕ) : ℝ)) / B) ^ η)) := by
      have hshift :=
        exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
          (Q := Q) (N := q) (B := BtailUnion) (η := η)
          hBtailUnion_pos hη_pos
      have hdiff : (q - Q : ℕ) = N - (N0 + Q) := by
        dsimp [q]
        omega
      simpa [B, hdiff] using hshift
    simpa [Bad, hN0q] using htail_q.trans hcompare
  have hlocalized :=
    quenchedLocalizedEstimate_shifted_from_badTailBound
      hP hStruct hΓ (t := t) (α := α) (η := η) (B := B)
      (Nentry := 0) (Nmin := N0 + Q)
      hη_pos hB_one (by simpa [H, Bad] using htail_abs)
  change
    IsBigO P (gammaSigma η) X
        (3 * ((3 : ℝ) ^ (N0 + Q)) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-α)
  simpa [H, Bad, X] using hlocalized

/-- Uniform-in-`σ` version of
`exists_quantitative_absolute_quenchedLocalizedEstimate_interpolated`. -/
theorem exists_quantitative_absolute_quenchedLocalizedEstimate_interpolated_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct CcrudeShift Csmall : ℝ,
          0 < Cfluct ∧ 0 < CcrudeShift ∧ 0 < Csmall ∧
          ∀ {t α : ℝ},
            let K : ℝ := quenchedProbeEnvelopeConst d
            let S : Finset (NormalizedProbeIndex d) := Finset.univ
            let b : ℝ := (d : ℝ) / 2
            let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
            let ctop : ℝ :=
              min (t - α)
                (min (b - α)
                  (min ((t - α) * (1 + b / a))
                    (b - α * (1 + b / a))))
            let τ : ℝ := finiteQuenchedTailTau σ
            let η : ℝ := finiteQuenchedTailExponent d σ t
            let w : ℝ := ((3 ^ d : ℕ) : ℝ)
            let ρtop : ℝ := (3 : ℝ) ^ ctop
            let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - α) / η)
            let ρcrude : ℝ := (3 : ℝ) ^ (t - α)
            let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
            let Ctop : ℝ :=
              (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
            let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
            let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
            let Mshift : ℝ :=
              max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
                max 0 ((S.card : ℝ) * Kcrude))
            let ρgap : ℝ := (3 : ℝ) ^ η
            0 < t →
            t ≤ b →
            0 ≤ α →
            α < t →
            α < b →
            α * (1 + b / a) < b →
            α < a →
            ∃ Rshift Rsmall Runion : ℕ,
              ∀ {P : Ch04.RestrictionCoeffLaw d}
                (hP : Ch04.RestrictionLawCarrier P)
                (hStruct : Ch04.RestrictionStructuralLaw P)
                (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
                hΓ.sigma = σ → hΓ.params = params →
                let N0 : ℕ :=
                  annealedAlgebraicEntryScale P
                    hΓ.toQuantitativeCoarseGrainedEllipticity Centry
                let H : ℕ → ℕ → RegCoeffField d → ℝ :=
                  quenchedProbeEnvelope hP hStruct
                let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
                let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
                let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
                let Ohigh : ℝ := (τ * b * (L + 1)) / η
                let Ocrude : ℝ := (σ * t * (L + 1)) / η
                let BleadShift : ℝ :=
                  max (DenShift * (3 : ℝ) ^ Ohigh)
                    (DenShift * (3 : ℝ) ^ Ocrude)
                let BtailShift : ℝ := 2 * BleadShift
                let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
                let QprefShift : ℕ :=
                  max (Nat.ceil (max 0 (Real.log Mshift)))
                    (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
                      Real.log ρgap)))
                let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
                let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
                let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
                let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
                let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
                let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
                let prefSmall : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
                let Msmall : ℝ := max 1 (max 0 (prefSmall * Ksmall))
                let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
                let BtailSmall : ℝ := 2 * BleadSmall
                let cgapSmall : ℝ := BleadSmall ^ (-η) - BtailSmall ^ (-η)
                let QprefSmall : ℕ :=
                  max (Nat.ceil (max 0 (Real.log Msmall)))
                    (max Rsmall (Nat.ceil ((2 * max 0 (-(Real.log cgapSmall))) /
                      Real.log ρgap)))
                let QleadSmall : ℕ := Nat.ceil (Real.log BleadSmall / Real.log 3)
                let Qsmall : ℕ := max QprefSmall QleadSmall
                let BleadUnion : ℝ := max BtailShift BtailSmall
                let BtailUnion : ℝ := 2 * BleadUnion
                let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
                let Qunion : ℕ :=
                  max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
                    (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
                      Real.log ρgap)))
                let Q : ℕ := max Qshift (max Qsmall Qunion)
                let B : ℝ := max 1 BtailUnion
                let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent H t α
                let X : RegCoeffField d → ℝ := quenchedMinimalScale (N0 + Q) Bad
                IsBigO P (gammaSigma η) X
                  (3 * ((3 : ℝ) ^ (N0 + Q)) * B) ∧
                  (∀ aω, 1 ≤ X aω) ∧
                    ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                      ∀ᵐ aω ∂P,
                        ∀ {m n : ℕ},
                          X aω ≤ (3 : ℝ) ^ m →
                          n < m →
                          (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                              localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                            ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Centry, a, hCentry, ha, htailBaseUniform⟩ :=
    exists_quantitative_threshold_absoluteBadTail_quenchedProbeEnvelope_le_interpolated_tail_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, CcrudeShift, Csmall,
      hCfluct, hCcrudeShift, hCsmall, htailBase⟩ :=
    htailBaseUniform hσ_pos
  refine ⟨Cfluct, CcrudeShift, Csmall,
    hCfluct, hCcrudeShift, hCsmall, ?_⟩
  intro t α
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - α)
      (min (b - α)
        (min ((t - α) * (1 + b / a))
          (b - α * (1 + b / a))))
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - α) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - α)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let Ctop : ℝ :=
    (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
  let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
  let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
  let Mshift : ℝ :=
    max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
      max 0 ((S.card : ℝ) * Kcrude))
  let ρgap : ℝ := (3 : ℝ) ^ η
  obtain ⟨Rshift, Rsmall, Runion, htailLaw⟩ :=
    htailBase (t := t) (α := α)
      ht htb hα_nonneg hαt hαb hαharm hαa
  refine ⟨Rshift, Rsmall, Runion, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let H : ℕ → ℕ → RegCoeffField d → ℝ :=
    quenchedProbeEnvelope hP hStruct
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
  let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let BleadShift : ℝ :=
    max (DenShift * (3 : ℝ) ^ Ohigh) (DenShift * (3 : ℝ) ^ Ocrude)
  let BtailShift : ℝ := 2 * BleadShift
  let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
  let QprefShift : ℕ :=
    max (Nat.ceil (max 0 (Real.log Mshift)))
      (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
        Real.log ρgap)))
  let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
  let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
  let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
  let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
  let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
  let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
  let prefSmall : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
  let Msmall : ℝ := max 1 (max 0 (prefSmall * Ksmall))
  let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
  let BtailSmall : ℝ := 2 * BleadSmall
  let cgapSmall : ℝ := BleadSmall ^ (-η) - BtailSmall ^ (-η)
  let QprefSmall : ℕ :=
    max (Nat.ceil (max 0 (Real.log Msmall)))
      (max Rsmall (Nat.ceil ((2 * max 0 (-(Real.log cgapSmall))) /
        Real.log ρgap)))
  let QleadSmall : ℕ := Nat.ceil (Real.log BleadSmall / Real.log 3)
  let Qsmall : ℕ := max QprefSmall QleadSmall
  let BleadUnion : ℝ := max BtailShift BtailSmall
  let BtailUnion : ℝ := 2 * BleadUnion
  let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
  let Qunion : ℕ :=
    max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
      (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
        Real.log ρgap)))
  let Q : ℕ := max Qshift (max Qsmall Qunion)
  let B : ℝ := max 1 BtailUnion
  let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent H t α
  let X : RegCoeffField d → ℝ := quenchedMinimalScale (N0 + Q) Bad
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hBtailUnion_pos : 0 < BtailUnion := by
    have hDenShift_pos : 0 < DenShift := by
      simpa [DenShift] using
        mixedBottomTailDenominator_pos
          (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
    have hBleadShift_pos : 0 < BleadShift := by
      have hleft : 0 < DenShift * (3 : ℝ) ^ Ohigh :=
        mul_pos hDenShift_pos
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh)
      exact hleft.trans_le (le_max_left _ _)
    have hBtailShift_pos : 0 < BtailShift := by
      dsimp [BtailShift]
      positivity
    have hBleadUnion_pos : 0 < BleadUnion :=
      hBtailShift_pos.trans_le (le_max_left _ _)
    dsimp [BtailUnion]
    positivity
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact le_max_left 1 BtailUnion
  have htail_abs :
      ∀ N : ℕ, N0 + Q ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - (N0 + Q) : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hN
    let q : ℕ := N - N0
    have hN0q : N0 + q = N := by
      dsimp [q]
      exact Nat.add_sub_of_le (le_trans (Nat.le_add_right N0 Q) hN)
    have hQq : Q ≤ q := by
      dsimp [q]
      omega
    have htail_q :
        P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
          Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) := by
      simpa [K, S, b, L, ctop, τ, η, w, ρtop, ρbottom, ρcrude,
        Cbottom, Ctop, Kbottom, Kcrude, Mshift, ρgap, N0, H, Dhigh,
        Dcrude, DenShift, Ohigh, Ocrude, BleadShift, BtailShift,
        cgapShift, QprefShift, QleadShift, QcutShift, Qshift,
        scaleSmall, ρsmall, Ksmall, prefSmall, Msmall, BleadSmall,
        BtailSmall, cgapSmall, QprefSmall, QleadSmall, Qsmall,
        BleadUnion, BtailUnion, cgapUnion, Qunion, Q] using
        htailLaw hP hStruct hΓ hσ_eq hparams q hQq
    have hcompare :
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - (N0 + Q) : ℕ) : ℝ)) / B) ^ η)) := by
      have hshift :=
        exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
          (Q := Q) (N := q) (B := BtailUnion) (η := η)
          hBtailUnion_pos hη_pos
      have hdiff : (q - Q : ℕ) = N - (N0 + Q) := by
        dsimp [q]
        omega
      simpa [B, hdiff] using hshift
    simpa [Bad, hN0q] using htail_q.trans hcompare
  have hlocalized :=
    quenchedLocalizedEstimate_shifted_from_badTailBound
      hP hStruct hΓ (t := t) (α := α) (η := η) (B := B)
      (Nentry := 0) (Nmin := N0 + Q)
      hη_pos hB_one (by simpa [H, Bad] using htail_abs)
  change
    IsBigO P (gammaSigma η) X
        (3 * ((3 : ℝ) ^ (N0 + Q)) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-α)
  simpa [H, Bad, X] using hlocalized

end

end Section57
end Ch05
end Book
end Homogenization
