/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailCollapse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleThresholds

/-! # Bad Scale Tail Selected -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Selected-denominator bad-scale tail collapse

This file reattaches the deterministic collapse from `BadScaleTailCollapse` to
the synchronized selected-denominator component theorem.
-/

noncomputable section

/-- The selected-denominator bad-scale estimate collapsed to one finite-`sigma`
tail, up to the deterministic large-scale and prefactor-gap inequalities. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_prefactor_gap
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Btail : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q : ℕ},
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
        let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
        let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
        let ChighBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)
        let CcrudeBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            weightedGeometricExpKernelConst w (ρcrude ^ σ)
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        0 < Btail →
        1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        max 0 Ctop + max 0 ChighBottom + max 0 CcrudeBottom ≤
          Real.exp (Alead - Atail) →
        P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hselected⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_selected_denominator
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Btail P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa _hBtail hlead_one hq_large hpref
  classical
  let : IsProbabilityMeasure P := hP.isProbability
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
  let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
  let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - Ohigh) / Den
  let Acrude : ℝ := (3 : ℝ) ^ ((q : ℝ) - Ocrude) / Den
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hDen_pos : 0 < Den := by
    have hK_pos : 0 < K := by
      simpa [K] using quenchedProbeEnvelopeConst_pos d
    have hDhigh_pos : 0 < Dhigh := by
      dsimp [Dhigh]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
        (pow_pos hΓ.thetaHat_pos 2)
    have hDcrude_pos : 0 < Dcrude := by
      dsimp [Dcrude]
      exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hΓ.thetaHat_pos 2)
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hBlead_pos : 0 < Blead := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hleft : 0 < Den * (3 : ℝ) ^ Ohigh :=
      mul_pos hDen_pos (Real.rpow_pos_of_pos h3 Ohigh)
    exact hleft.trans_le (le_max_left _ _)
  have hAlead_A : Alead ≤ A ^ η := by
    have hden : Den * (3 : ℝ) ^ Ohigh ≤ Blead := by
      dsimp [Blead]
      exact le_max_left _ _
    simpa [Alead, A] using
      selected_tail_parameter_power_le_high
        (q := q) (Den := Den) (B := Blead) (η := η) (O := Ohigh)
        hDen_pos hBlead_pos hη_pos hden
  have hAlead_Acrude : Alead ≤ Acrude ^ η := by
    have hden : Den * (3 : ℝ) ^ Ocrude ≤ Blead := by
      dsimp [Blead]
      exact le_max_right _ _
    simpa [Alead, Acrude] using
      selected_tail_parameter_power_le_high
        (q := q) (Den := Den) (B := Blead) (η := η) (O := Ocrude)
        hDen_pos hBlead_pos hη_pos hden
  have hA_one : 1 ≤ A := by
    have hlead_A : (3 : ℝ) ^ (q : ℝ) / Blead ≤ A := by
      have hden : Den * (3 : ℝ) ^ Ohigh ≤ Blead := by
        dsimp [Blead]
        exact le_max_left _ _
      have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      calc
        (3 : ℝ) ^ (q : ℝ) / Blead
            ≤ (3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ Ohigh) :=
              div_le_div_of_nonneg_left hpow_nonneg
                (mul_pos hDen_pos
                  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh))
                hden
        _ = A := by
              exact (rpow_three_sub_div_eq_div_mul_rpow
                (x := (q : ℝ)) (O := Ohigh) (Den := Den)
                hDen_pos.ne').symm
    exact hlead_one.trans hlead_A
  have hAcrude_one : 1 ≤ Acrude := by
    have hlead_A : (3 : ℝ) ^ (q : ℝ) / Blead ≤ Acrude := by
      have hden : Den * (3 : ℝ) ^ Ocrude ≤ Blead := by
        dsimp [Blead]
        exact le_max_right _ _
      have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      calc
        (3 : ℝ) ^ (q : ℝ) / Blead
            ≤ (3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ Ocrude) :=
              div_le_div_of_nonneg_left hpow_nonneg
                (mul_pos hDen_pos
                  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ocrude))
                hden
        _ = Acrude := by
              exact (rpow_three_sub_div_eq_div_mul_rpow
                (x := (q : ℝ)) (O := Ocrude) (Den := Den)
                hDen_pos.ne').symm
    exact hlead_one.trans hlead_A
  have hcomponent :=
    hselected (t := t) (αbad := αbad)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa
      hA_one hAcrude_one hq_large
  exact
    measureReal_badScaleEvent_le_exp_tail_of_selected_component_sum
      (μ := P) (H := Hshift) (t := t) (α := αbad) (q := q)
      (S := (S.card : ℝ)) (qPlus := ((q + 1 : ℕ) : ℝ))
      (Cbottom := Cbottom) (wq := w ^ q)
      (Ktop := weightedLinearExpKernelConst w (ρtop ^ τ))
      (Kbottom := weightedGeometricExpKernelConst w (ρbottom ^ η))
      (Kcrude := weightedGeometricExpKernelConst w (ρcrude ^ σ))
      (A := A) (Acrude := Acrude) (Alead := Alead) (Atail := Atail)
      (η := η)
      (by
        simpa [K, N0, Hshift, S, b, L, ctop, τ, η, w, Dhigh, Dcrude,
          Den, Ohigh, Ocrude, A, Acrude, ρtop, ρbottom, ρcrude, Cbottom]
          using hcomponent)
      hAlead_A hAlead_Acrude
      (by
        simpa [K, S, b, L, ctop, τ, η, w, Dhigh, Dcrude, Den,
          Ohigh, Ocrude, Blead, Alead, Atail, ρtop, ρbottom, ρcrude,
          Cbottom] using hpref)

/-- Uniform-in-`σ` version of
`measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_prefactor_gap`. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_prefactor_gap_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct Ccrude : ℝ, 0 < Cfluct ∧ 0 < Ccrude ∧
          ∀ {t αbad Btail : ℝ},
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ {q : ℕ},
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
            let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
            let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
            let ρtop : ℝ := (3 : ℝ) ^ ctop
            let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
            let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
            let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
            let Ctop : ℝ :=
              (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
            let ChighBottom : ℝ :=
              ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)
            let CcrudeBottom : ℝ :=
              ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
                weightedGeometricExpKernelConst w (ρcrude ^ σ)
            0 < t →
            t ≤ b →
            0 ≤ αbad →
            αbad < t →
            αbad < b →
            αbad * (1 + b / a) < b →
            αbad < a →
            0 < Btail →
            1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead →
            (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
              Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
            max 0 Ctop + max 0 ChighBottom + max 0 CcrudeBottom ≤
              Real.exp (Alead - Atail) →
            P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Centry, a, hCentry, ha, hselectedBase⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_selected_denominator_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, Ccrude, hCfluct, hCcrude, hselected⟩ :=
    hselectedBase hσ_pos
  refine ⟨Cfluct, Ccrude, hCfluct, hCcrude, ?_⟩
  intro t αbad Btail P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa _hBtail hlead_one hq_large hpref
  classical
  let : IsProbabilityMeasure P := hP.isProbability
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
  let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
  let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - Ohigh) / Den
  let Acrude : ℝ := (3 : ℝ) ^ ((q : ℝ) - Ocrude) / Den
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hDen_pos : 0 < Den := by
    have hK_pos : 0 < K := by
      simpa [K] using quenchedProbeEnvelopeConst_pos d
    have hDhigh_pos : 0 < Dhigh := by
      dsimp [Dhigh]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
        (pow_pos hΓ.thetaHat_pos 2)
    have hDcrude_pos : 0 < Dcrude := by
      dsimp [Dcrude]
      exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hΓ.thetaHat_pos 2)
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hBlead_pos : 0 < Blead := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hleft : 0 < Den * (3 : ℝ) ^ Ohigh :=
      mul_pos hDen_pos (Real.rpow_pos_of_pos h3 Ohigh)
    exact hleft.trans_le (le_max_left _ _)
  have hAlead_A : Alead ≤ A ^ η := by
    have hden : Den * (3 : ℝ) ^ Ohigh ≤ Blead := by
      dsimp [Blead]
      exact le_max_left _ _
    simpa [Alead, A] using
      selected_tail_parameter_power_le_high
        (q := q) (Den := Den) (B := Blead) (η := η) (O := Ohigh)
        hDen_pos hBlead_pos hη_pos hden
  have hAlead_Acrude : Alead ≤ Acrude ^ η := by
    have hden : Den * (3 : ℝ) ^ Ocrude ≤ Blead := by
      dsimp [Blead]
      exact le_max_right _ _
    simpa [Alead, Acrude] using
      selected_tail_parameter_power_le_high
        (q := q) (Den := Den) (B := Blead) (η := η) (O := Ocrude)
        hDen_pos hBlead_pos hη_pos hden
  have hA_one : 1 ≤ A := by
    have hlead_A : (3 : ℝ) ^ (q : ℝ) / Blead ≤ A := by
      have hden : Den * (3 : ℝ) ^ Ohigh ≤ Blead := by
        dsimp [Blead]
        exact le_max_left _ _
      have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      calc
        (3 : ℝ) ^ (q : ℝ) / Blead
            ≤ (3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ Ohigh) :=
              div_le_div_of_nonneg_left hpow_nonneg
                (mul_pos hDen_pos
                  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh))
                hden
        _ = A := by
              exact (rpow_three_sub_div_eq_div_mul_rpow
                (x := (q : ℝ)) (O := Ohigh) (Den := Den)
                hDen_pos.ne').symm
    exact hlead_one.trans hlead_A
  have hAcrude_one : 1 ≤ Acrude := by
    have hlead_A : (3 : ℝ) ^ (q : ℝ) / Blead ≤ Acrude := by
      have hden : Den * (3 : ℝ) ^ Ocrude ≤ Blead := by
        dsimp [Blead]
        exact le_max_right _ _
      have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      calc
        (3 : ℝ) ^ (q : ℝ) / Blead
            ≤ (3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ Ocrude) :=
              div_le_div_of_nonneg_left hpow_nonneg
                (mul_pos hDen_pos
                  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ocrude))
                hden
        _ = Acrude := by
              exact (rpow_three_sub_div_eq_div_mul_rpow
                (x := (q : ℝ)) (O := Ocrude) (Den := Den)
                hDen_pos.ne').symm
    exact hlead_one.trans hlead_A
  have hcomponent :=
    hselected (t := t) (αbad := αbad)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa
      hA_one hAcrude_one hq_large
  exact
    measureReal_badScaleEvent_le_exp_tail_of_selected_component_sum
      (μ := P) (H := Hshift) (t := t) (α := αbad) (q := q)
      (S := (S.card : ℝ)) (qPlus := ((q + 1 : ℕ) : ℝ))
      (Cbottom := Cbottom) (wq := w ^ q)
      (Ktop := weightedLinearExpKernelConst w (ρtop ^ τ))
      (Kbottom := weightedGeometricExpKernelConst w (ρbottom ^ η))
      (Kcrude := weightedGeometricExpKernelConst w (ρcrude ^ σ))
      (A := A) (Acrude := Acrude) (Alead := Alead) (Atail := Atail)
      (η := η)
      (by
        simpa [K, N0, Hshift, S, b, L, ctop, τ, η, w, Dhigh, Dcrude,
          Den, Ohigh, Ocrude, A, Acrude, ρtop, ρbottom, ρcrude, Cbottom]
          using hcomponent)
      hAlead_A hAlead_Acrude
      (by
        simpa [K, S, b, L, ctop, τ, η, w, Dhigh, Dcrude, Den,
          Ohigh, Ocrude, Blead, Alead, Atail, ρtop, ρbottom, ρcrude,
          Cbottom] using hpref)

/-- The same tail collapse after discharging the deterministic lower bound on
the lead tail parameter and the crude-top cutoff by explicit ceiling
thresholds.  The prefactor gap is the only remaining large-scale condition. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_thresholds_and_prefactor_gap
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Btail : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q : ℕ},
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
        let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
        let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
        let ChighBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)
        let CcrudeBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            weightedGeometricExpKernelConst w (ρcrude ^ σ)
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        0 < Btail →
        Nat.ceil (Real.log Blead / Real.log 3) ≤ q →
        Nat.ceil ((L + 1) / (1 - αbad / a) + 1) ≤ q →
        max 0 Ctop + max 0 ChighBottom + max 0 CcrudeBottom ≤
          Real.exp (Alead - Atail) →
        P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, htail⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_prefactor_gap
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Btail P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hBtail hq_lead hq_cut hpref
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hBlead_pos : 0 < Blead := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hleft : 0 < Den * (3 : ℝ) ^ Ohigh :=
      mul_pos hDen_pos (Real.rpow_pos_of_pos h3 Ohigh)
    exact hleft.trans_le (le_max_left _ _)
  have hlead_one : 1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead := by
    simpa [Blead] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := (1 : ℝ)) (O := (0 : ℝ)) (D := Blead) (q := q)
        (by norm_num) hBlead_pos
        (by
          simpa [K, b, L, τ, η, Dhigh, Dcrude, Den, Ohigh, Ocrude,
            Blead] using hq_lead)
  have hδ : 0 < 1 - αbad / a := by
    have hdiv : αbad / a < 1 := by
      rw [div_lt_iff₀ ha]
      nlinarith
    linarith
  have hcut :
      (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1) + 1 <
        (1 - αbad / a) * (q : ℝ) := by
    simpa [L] using
      large_scale_cutoff_of_natCeil_add_one_le
        (L := L) (δ := 1 - αbad / a) (q := q) hδ hq_cut
  exact
    htail (t := t) (αbad := αbad) (Btail := Btail)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa hBtail
      (by simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
        Blead] using hlead_one)
      (by simpa [K] using hcut)
      (by
        simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
          Blead] using hpref)

/-- Uniform-in-`σ` version of
`measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_thresholds_and_prefactor_gap`. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_thresholds_and_prefactor_gap_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct Ccrude : ℝ, 0 < Cfluct ∧ 0 < Ccrude ∧
          ∀ {t αbad Btail : ℝ},
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ {q : ℕ},
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
            let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
            let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
            let ρtop : ℝ := (3 : ℝ) ^ ctop
            let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
            let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
            let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
            let Ctop : ℝ :=
              (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
            let ChighBottom : ℝ :=
              ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)
            let CcrudeBottom : ℝ :=
              ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
                weightedGeometricExpKernelConst w (ρcrude ^ σ)
            0 < t →
            t ≤ b →
            0 ≤ αbad →
            αbad < t →
            αbad < b →
            αbad * (1 + b / a) < b →
            αbad < a →
            0 < Btail →
            Nat.ceil (Real.log Blead / Real.log 3) ≤ q →
            Nat.ceil ((L + 1) / (1 - αbad / a) + 1) ≤ q →
            max 0 Ctop + max 0 ChighBottom + max 0 CcrudeBottom ≤
              Real.exp (Alead - Atail) →
            P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Centry, a, hCentry, ha, htailBase⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_of_prefactor_gap_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, Ccrude, hCfluct, hCcrude, htail⟩ :=
    htailBase hσ_pos
  refine ⟨Cfluct, Ccrude, hCfluct, hCcrude, ?_⟩
  intro t αbad Btail P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hBtail hq_lead hq_cut hpref
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hBlead_pos : 0 < Blead := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hleft : 0 < Den * (3 : ℝ) ^ Ohigh :=
      mul_pos hDen_pos (Real.rpow_pos_of_pos h3 Ohigh)
    exact hleft.trans_le (le_max_left _ _)
  have hlead_one : 1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead := by
    simpa [Blead] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := (1 : ℝ)) (O := (0 : ℝ)) (D := Blead) (q := q)
        (by norm_num) hBlead_pos
        (by
          simpa [K, b, L, τ, η, Dhigh, Dcrude, Den, Ohigh, Ocrude,
            Blead] using hq_lead)
  have hδ : 0 < 1 - αbad / a := by
    have hdiv : αbad / a < 1 := by
      rw [div_lt_iff₀ ha]
      nlinarith
    linarith
  have hcut :
      (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1) + 1 <
        (1 - αbad / a) * (q : ℝ) := by
    simpa [L] using
      large_scale_cutoff_of_natCeil_add_one_le
        (L := L) (δ := 1 - αbad / a) (q := q) hδ hq_cut
  exact
    htail (t := t) (αbad := αbad) (Btail := Btail)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa hBtail
      (by simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
        Blead] using hlead_one)
      (by simpa [K] using hcut)
      (by
        simpa [K, S, b, L, τ, η, w, Dhigh, Dcrude, Den, Ohigh, Ocrude,
          Blead] using hpref)

end

end Section57
end Ch05
end Book
end Homogenization
