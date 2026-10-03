/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedLocalizedEstimate

/-! # Bad Scale Minimal -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Minimal scale from the interpolated bad-scale tail

This file converts the eventual one-scale bad-scale estimate into the
quantitative triadic minimal scale used in the quenched theorem.  The only
extra deterministic step is that the absolute tail at scale `N` dominates the
shifted tail at `N - Q`, with the harmless replacement of the denominator by
`max 1 B`.
-/

noncomputable section

theorem rpow_three_sub_div_max_one_le_rpow_three_nat_div
    {Q N : ℕ} {B η : ℝ}
    (hB : 0 < B) (hη : 0 < η) :
    ((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / max 1 B) ^ η ≤
      (((3 : ℝ) ^ (N : ℝ) / B) ^ η) := by
  have hsub_le : ((N - Q : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N Q
  have hpow_le :
      Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ) ≤ (3 : ℝ) ^ (N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hsub_le
  have hpow_sub_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hpow_N_nonneg : 0 ≤ (3 : ℝ) ^ (N : ℝ) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hmax_pos : 0 < max 1 B :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 B)
  have hB_le_max : B ≤ max 1 B := le_max_right 1 B
  have hfrac_le :
      Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ) / max 1 B ≤
        (3 : ℝ) ^ (N : ℝ) / B := by
    calc
      Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ) / max 1 B
          ≤ (3 : ℝ) ^ (N : ℝ) / max 1 B :=
            div_le_div_of_nonneg_right hpow_le hmax_pos.le
      _ ≤ (3 : ℝ) ^ (N : ℝ) / B :=
            div_le_div_of_nonneg_left hpow_N_nonneg hB hB_le_max
  exact
    Real.rpow_le_rpow
      (div_nonneg hpow_sub_nonneg hmax_pos.le) hfrac_le hη.le

theorem exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
    {Q N : ℕ} {B η : ℝ}
    (hB : 0 < B) (hη : 0 < η) :
    Real.exp (-(((3 : ℝ) ^ (N : ℝ) / B) ^ η)) ≤
      Real.exp
        (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / max 1 B) ^ η)) := by
  have hpow :=
    rpow_three_sub_div_max_one_le_rpow_three_nat_div
      (Q := Q) (N := N) (B := B) (η := η) hB hη
  exact Real.exp_le_exp.mpr (by linarith)

/-- The finite-`sigma` interpolated bad-scale tail yields the shifted
localized estimate above a quantitative minimal scale.  The constants are
chosen before the probability law; the terminal threshold `Q` and the
normalizing denominator are allowed to depend on the law through the entry
scale and `thetaHat`, as in the manuscript proof. -/
theorem exists_shifted_quenchedLocalizedEstimate_interpolated
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
        let Ohigh : ℝ := (τ * b * (L + 1)) / η
        let Ocrude : ℝ := (σ * t * (L + 1)) / η
        let Blead : ℝ :=
          max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
        let Btail : ℝ := 2 * Blead
        let B : ℝ := max 1 Btail
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        ∃ Q : ℕ,
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
    exists_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let Blead : ℝ :=
    max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
  let Btail : ℝ := 2 * Blead
  let B : ℝ := max 1 Btail
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
  obtain ⟨Q, hQ⟩ :=
    hbad (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
      ht htb hα_nonneg hαt hαb hαharm hαa
  refine ⟨Q, ?_⟩
  let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t αbad
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
      simpa [K, N0, Hshift, b, L, τ, η, Dhigh, Dcrude, Den, Ohigh,
        Ocrude, Blead, Btail, Bad] using hQ N hQN
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
  simpa [K, N0, Hshift, b, L, τ, η, Dhigh, Dcrude, Den, Ohigh,
    Ocrude, Blead, Btail, B, Bad] using hlocalized

end

end Section57
end Ch05
end Book
end Homogenization
