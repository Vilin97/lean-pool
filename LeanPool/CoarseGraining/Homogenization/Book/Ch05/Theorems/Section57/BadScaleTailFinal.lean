/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGap

/-! # Bad Scale Tail Final -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Eventual shifted bad-scale tail

This file combines the selected bad-scale tail, deterministic threshold
selection, and prefactor absorption.  The output is still shifted by the
annealed entry scale; the next layer converts this eventual bad-scale bound
into a tail bound for the random minimal scale.
-/

noncomputable section

theorem exists_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail
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
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
          P.real (badScaleEvent Hshift t αbad q) ≤
            Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, htail⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_thresholds_and_prefactor_gap
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
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
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let Blead : ℝ :=
    max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
  let Btail : ℝ := 2 * Blead
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let Ctop : ℝ :=
    (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
  let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
  let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
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
  have hBlead_lt_Btail : Blead < Btail := by
    dsimp [Btail]
    nlinarith
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact_mod_cast Nat.zero_le (3 ^ d)
  obtain ⟨Qpref, hQpref⟩ :=
    exists_forall_ge_selected_prefactor_gap
      (Ctop := Ctop) (Cbottom := Cbottom) (S := (S.card : ℝ))
      (Kbottom := Kbottom) (Kcrude := Kcrude)
      (w := w) (Blead := Blead) (Btail := Btail) (η := η)
      hBlead_pos hBtail_pos hη_pos hBlead_lt_Btail hw_nonneg
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
  let Q : ℕ := max Qpref (max Qlead Qcut)
  refine ⟨Q, ?_⟩
  intro q hQq
  have hq_pref : Qpref ≤ q := (le_max_left Qpref (max Qlead Qcut)).trans hQq
  have hq_lead : Qlead ≤ q :=
    (le_max_left Qlead Qcut).trans
      ((le_max_right Qpref (max Qlead Qcut)).trans hQq)
  have hq_cut : Qcut ≤ q :=
    (le_max_right Qlead Qcut).trans
      ((le_max_right Qpref (max Qlead Qcut)).trans hQq)
  have hpref_q :
      max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
            max 0 (((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) * Kcrude) ≤
        Real.exp
          ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
            (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) :=
    hQpref q hq_pref
  have htail_q :=
    htail (t := t) (αbad := αbad) (Btail := Btail)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa hBtail_pos
      (by simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
        Blead, Qlead] using hq_lead)
      (by simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
        Blead, Qcut] using hq_cut)
      (by
        simpa [K, S, b, L, ctop, τ, η, w, Dhigh, Dcrude, Den, Ohigh,
          Ocrude, Blead, Btail, ρtop, ρbottom, ρcrude, Cbottom, Ctop,
          Kbottom, Kcrude] using hpref_q)
  simpa [K, N0, Hshift, S, b, L, ctop, τ, η, w, Dhigh, Dcrude, Den,
    Ohigh, Ocrude, Blead, Btail] using htail_q

end

end Section57
end Ch05
end Book
end Homogenization
