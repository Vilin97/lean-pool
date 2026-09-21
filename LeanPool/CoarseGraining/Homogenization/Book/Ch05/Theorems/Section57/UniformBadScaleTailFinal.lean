/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailCollapse
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGapQuantitative

/-! # Uniform Bad Scale Tail Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Quantitative uniform-endpoint bad-scale tail

This is the `Γ∞` endpoint analogue of the finite-`σ` quantitative bad-scale
tail.  The exponent is `d`; the crude-bottom deterministic cutoff contributes
an additional explicit threshold but no stochastic branch.
-/

noncomputable section

theorem exists_quantitative_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail
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
            ∀ q : ℕ, Q ≤ q →
              P.real (badScaleEvent Hshift t αbad q) ≤
                Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, htail⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail_of_thresholds_and_prefactor_gap
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
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact_mod_cast Nat.zero_le (3 ^ d)
  obtain ⟨R, hR, hRtail⟩ :=
    exists_forall_ge_selected_prefactor_gap_quantitative_uniform
      (Ctop := Ctop) (Cbottom := Cbottom) (S := (S.card : ℝ))
      (Kbottom := Kbottom) (Kcrude := (0 : ℝ))
      (w := w) (η := η) hη_pos hw_nonneg
  refine ⟨R, ?_, ?_⟩
  · simpa [ρgap, W, C₀, w, η] using hR
  intro P hP hStruct hInf hparams
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
  intro q hQq
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
  have hBlead_lt_Btail : Blead < Btail := by
    dsimp [Btail]
    nlinarith
  have hq_pref : Qpref ≤ q := (le_max_left Qpref (max Qlead (max Qcrude Qcut))).trans hQq
  have hq_lead : Qlead ≤ q :=
    (le_max_left Qlead (max Qcrude Qcut)).trans
      ((le_max_right Qpref (max Qlead (max Qcrude Qcut))).trans hQq)
  have hq_crude : Qcrude ≤ q :=
    (le_max_left Qcrude Qcut).trans
      ((le_max_right Qlead (max Qcrude Qcut)).trans
        ((le_max_right Qpref (max Qlead (max Qcrude Qcut))).trans hQq))
  have hq_cut : Qcut ≤ q :=
    (le_max_right Qcrude Qcut).trans
      ((le_max_right Qlead (max Qcrude Qcut)).trans
        ((le_max_right Qpref (max Qlead (max Qcrude Qcut))).trans hQq))
  have hpref_q :
      max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) ≤
        Real.exp
          ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
            (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
    have hthree :=
      hRtail (Blead := Blead) (Btail := Btail)
        hBlead_pos hBtail_pos hBlead_lt_Btail q
        (by
          simpa only [M, cgap, ρgap, mul_zero, max_self, add_zero] using
            hq_pref)
    simpa only [mul_zero, max_self, add_zero] using hthree
  have htail_q :=
    htail (t := t) (αbad := αbad) (Btail := Btail)
      hP hStruct hInf hparams (q := q)
      ht hα_nonneg hαt hαb hαharm hαa htb hBtail_pos
      (by
        change Qlead ≤ q
        exact hq_lead)
      (by
        change Qcrude ≤ q
        exact hq_crude)
      (by
        change Qcut ≤ q
        exact hq_cut)
      (by
        change
          max 0 Ctop +
                max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) ≤
            Real.exp
              ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
                (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η))
        exact hpref_q)
  change
    P.real (badScaleEvent Hshift t αbad q) ≤
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η))
  simpa [N0, Hshift, η] using htail_q

end

end Section57
end Ch05
end Book
end Homogenization
