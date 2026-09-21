/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailFinal

/-! # Uniform Bad Scale Minimal Quantitative -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Quantitative minimal scale from the uniform-endpoint bad-scale tail

This is the `Γ∞` endpoint analogue of the finite-`σ` quantitative minimal
scale.  The bad-scale tail has exponent `d`, so the resulting random scale is
`O_{Γ_d}`.
-/

noncomputable section

/-- The uniform-endpoint bad-scale tail yields the shifted localized estimate
above an explicit quantitative minimal scale.  The deterministic prefactor
threshold is selected before the probability law. -/
theorem exists_quantitative_shifted_quenchedLocalizedEstimate_uniformEndpoint
    {d : ℕ} [NeZero d]
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
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))
        let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
        let W : ℝ := max 1 w
        let M : ℝ := max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom))
        let ρgap : ℝ := (3 : ℝ) ^ η
        let C₀ : ℝ := 2 + Real.log W
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        ∃ R : ℕ,
          (∀ q : ℕ, R ≤ q →
            C₀ * (q : ℝ) ≤
              Real.exp ((Real.log ρgap / 2) * (q : ℝ))) ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hInf.toQuantitativeCoarseGrainedEllipticity Centry
            let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
              fun M N aω =>
                quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
            let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
            let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
            let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
            let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
            let Btail : ℝ := 2 * Blead
            let B : ℝ := max 1 Btail
            let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
            let Qpref : ℕ :=
              max (Nat.ceil (max 0 (Real.log M)))
                (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
                  Real.log ρgap)))
            let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
            let Qcrude : ℕ :=
              Nat.ceil
                ((Real.log Dcrude + (t * (L + 1)) * Real.log (3 : ℝ)) /
                  (t * Real.log (3 : ℝ)))
            let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
            let Q : ℕ := max Qpref (max Qlead (max Qcrude Qcut))
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
    exists_quantitative_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad
  dsimp only
  intro ht hα_nonneg hαt hαb hαharm hαa htb
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let Ctop : ℝ :=
    (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))
  let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
  let W : ℝ := max 1 w
  let M : ℝ := max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom))
  let ρgap : ℝ := (3 : ℝ) ^ η
  let C₀ : ℝ := 2 + Real.log W
  obtain ⟨R, hR, hbadR⟩ :=
    hbad (t := t) (αbad := αbad)
      ht hα_nonneg hαt hαb hαharm hαa htb
  refine ⟨R, ?_, ?_⟩
  · simpa [K, S, b, L, ctop, η, w, ρtop, ρbottom,
      Cbottom, Ctop, Kbottom, W, M, ρgap, C₀] using hR
  intro P hP hStruct hInf hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
  let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
  let Btail : ℝ := 2 * Blead
  let B : ℝ := max 1 Btail
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Qcrude : ℕ :=
    Nat.ceil
      ((Real.log Dcrude + (t * (L + 1)) * Real.log (3 : ℝ)) /
        (t * Real.log (3 : ℝ)))
  let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
  let Q : ℕ := max Qpref (max Qlead (max Qcrude Qcut))
  let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t αbad
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      uniformEndpointHighDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
  have hBlead_pos : 0 < Blead := by
    dsimp [Blead]
    exact mul_pos hDen_pos
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (L + 1))
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
    exact hbadR hP hStruct hInf hparams
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
      hP hStruct (hInf.toGammaSigma 1 zero_lt_one)
      (t := t) (α := αbad) (η := η) (B := B)
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
