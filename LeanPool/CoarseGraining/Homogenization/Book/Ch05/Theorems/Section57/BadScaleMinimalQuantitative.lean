/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinalQuantitative

/-! # Bad Scale Minimal Quantitative -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Quantitative minimal scale from the interpolated bad-scale tail

This file keeps the deterministic prefactor threshold selected before the
probability law.  It is the quantitative replacement for the eventual
minimal-scale theorem, and is the layer used in the final compression to the
manuscript stochastic-integrability statement.
-/

noncomputable section

/-- The finite-`sigma` interpolated bad-scale tail yields the shifted
localized estimate above an explicit quantitative minimal scale.  The
constant `R` controlling the deterministic prefactor is selected before the
probability law. -/
theorem exists_quantitative_shifted_quenchedLocalizedEstimate_interpolated
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
        let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
        let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
        let W : ℝ := max 1 w
        let M : ℝ :=
          max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
            max 0 ((S.card : ℝ) * Kcrude))
        let ρgap : ℝ := (3 : ℝ) ^ η
        let C₀ : ℝ := 2 + Real.log W
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        ∃ R : ℕ,
          (∀ q : ℕ, R ≤ q →
            C₀ * (q : ℝ) ≤
              Real.exp ((Real.log ρgap / 2) * (q : ℝ))) ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
              fun M N aω =>
                quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
            let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
            let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
            let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
            let Ohigh : ℝ := (τ * b * (L + 1)) / η
            let Ocrude : ℝ := (σ * t * (L + 1)) / η
            let Blead : ℝ :=
              max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
            let Btail : ℝ := 2 * Blead
            let B : ℝ := max 1 Btail
            let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
            let Qpref : ℕ :=
              max (Nat.ceil (max 0 (Real.log M)))
                (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
                  Real.log ρgap)))
            let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
            let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
            let Q : ℕ := max Qpref (max Qlead Qcut)
            let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t αbad
            let X : RegCoeffField d → ℝ := quenchedMinimalScale Q Bad
            IsBigO P (gammaSigma η) X
              (3 * ((3 : ℝ) ^ Q) * B) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct
                            (N0 + m) (N0 + n) e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-αbad) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hbad⟩ :=
    exists_quantitative_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad K S b L ctop τ η w ρtop ρbottom ρcrude Cbottom Ctop Kbottom Kcrude
    W M ρgap C₀ ht htb hα_nonneg hαt hαb hαharm hαa
  classical
  obtain ⟨R, hR, hbadR⟩ :=
    hbad (t := t) (αbad := αbad)
      ht htb hα_nonneg hαt hαb hαharm hαa
  refine ⟨R, ?_, ?_⟩
  · simpa [K, S, b, L, ctop, τ, η, w, ρtop, ρbottom, ρcrude,
      Cbottom, Ctop, Kbottom, Kcrude, W, M, ρgap, C₀] using hR
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let Blead : ℝ :=
    max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
  let Btail : ℝ := 2 * Blead
  let B : ℝ := max 1 Btail
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
  let Q : ℕ := max Qpref (max Qlead Qcut)
  let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t αbad
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hBlead_pos : 0 < Blead := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hleft : 0 < Den * (3 : ℝ) ^ Ohigh :=
      mul_pos hDen_pos (Real.rpow_pos_of_pos h3 Ohigh)
    exact hleft.trans_le (le_max_left _ _)
  have hBtail_pos : 0 < Btail := by
    dsimp [Btail]
    positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_max_left 1 Btail
  have hQ :
      ∀ q : ℕ, Q ≤ q →
        P.real (badScaleEvent Hshift t αbad q) ≤
          Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
    exact hbadR hP hStruct hΓ hσ_eq hparams
  have htail :
      ∀ N : ℕ, Q ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hQN
    have hmono :
        P.real (badTailEvent Bad N) ≤ P.real (Bad N) :=
      measureReal_mono (μ := P)
        (badTailEvent_badScaleEvent_subset
          (H := Hshift) (t := t) (α := αbad) hα_nonneg)
    have hscale :
        P.real (Bad N) ≤
          Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) := by
      simpa [Bad] using hQ N hQN
    have hcompare :
        Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
      simpa [B] using
        exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
          (Q := Q) (N := N) (B := Btail) (η := η)
          hBtail_pos hη_pos
    exact hmono.trans (hscale.trans hcompare)
  have hlocalized :=
    quenchedLocalizedEstimate_shifted_from_badTailBound
      hP hStruct hΓ (t := t) (α := αbad) (η := η) (B := B)
      (Nentry := N0) (Nmin := Q)
      hη_pos hB (by simpa [Hshift, Bad, B] using htail)
  change
    IsBigO P (gammaSigma η) (quenchedMinimalScale Q Bad)
        (3 * ((3 : ℝ) ^ Q) * B) ∧
      (∀ aω, 1 ≤ quenchedMinimalScale Q Bad aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              quenchedMinimalScale Q Bad aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct
                    (N0 + m) (N0 + n) e aω ≤
                ((3 : ℝ) ^ m / quenchedMinimalScale Q Bad aω) ^ (-αbad)
  simpa [Hshift, Bad] using hlocalized

end

end Section57
end Ch05
end Book
end Homogenization
