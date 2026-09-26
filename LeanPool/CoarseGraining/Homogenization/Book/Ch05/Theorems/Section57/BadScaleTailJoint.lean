/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRawCrude
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailAssembly

/-! # Bad Scale Tail Joint -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Joint bad-scale component assembly with synchronized constants

The estimates in this file choose the raw high and crude constants once and
then feed the top, mixed-bottom, and crude-bottom branches into the deterministic
bad-scale split.  The large-scale cutoff and denominator lower bounds are still
explicit side conditions; later files discharge them by choosing a threshold.
-/

noncomputable section

/-- Synchronized three-component bad-scale tail bound, before the deterministic
threshold and prefactor absorption steps. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Den : ℝ},
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
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let Acrude : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        1 ≤ A →
        1 ≤ Acrude →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        P.real (badScaleEvent Hshift t αbad q) ≤
          (S.card : ℝ) *
              (Real.exp (-(A ^ η)) *
                weightedLinearExpKernelConst w (ρtop ^ τ)) +
            ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
              (Real.exp (-(A ^ η)) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)) +
            ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
              (Real.exp (-(Acrude ^ η)) *
                weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hhighRaw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨Ccrude, hCcrude, hcrudeRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hDen hDen_high hDen_crude
    hA_one hAcrude_one hq_large
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
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let Acrude : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have htop :
      P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
        (S.card : ℝ) *
          (Real.exp (-(A ^ η)) *
            weightedLinearExpKernelConst w (ρtop ^ τ)) := by
    simpa [K, N0, Hshift, S, b, L, ctop, τ, η, w, Dhigh, A, ρtop] using
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_badPair_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hhighRaw
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hΓ hσ_eq hparams (q := q)
        ht htb hαt hαb hαharm hDen hDen_high hA_one
  have hbottom :
      P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
          (Real.exp (-(A ^ η)) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)) := by
    simpa [K, N0, Hshift, S, b, L, τ, η, w, Dhigh, Dcrude, A, ρbottom,
      Cbottom] using
      measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_weighted_kernel_of_row_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
        (Centry := Centry) (a := a)
        hσ_pos params
        (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_interpolated_weighted_row_of_soft_max_bound
          (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
          (Centry := Centry) (a := a)
          hσ_pos params hCfluct hCcrude hCentry ha
          (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_max_mixed_of_badPair_bounds
            (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
            (Centry := Centry) (a := a)
            hσ_pos params hCfluct hCcrude hCentry ha hhighRaw hcrudeRaw))
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hΓ hσ_eq hparams (q := q)
        ht htb hαt hDen hDen_high hDen_crude hA_one
  have hcrude :
      P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
          (Real.exp (-(Acrude ^ η)) *
            weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
    simpa [K, N0, Hshift, S, L, η, w, Dcrude, Acrude, ρcrude] using
      measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_component_bound
        (d := d) (σ := σ) (Ccrude := Ccrude)
        hσ_pos hCcrude (params := params)
        (measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
          (d := d) (σ := σ) (Ccrude := Ccrude)
          hσ_pos hCcrude params hcrudeRaw)
        (Centry := Centry) (a := a) (t := t) (αbad := αbad)
        (Den := Den) hP hStruct hΓ hσ_eq hparams (q := q)
        ha ht hαt hDen hDen_crude hAcrude_one
  exact
    measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      ha hα_nonneg hαt hαa
      (by simpa [K, L] using hq_large)
      htop hbottom hcrude

/-- Uniform-in-`σ` synchronized three-component bad-scale tail bound.

The annealed entry constant and exponent are fixed before `σ`; the high and
crude fluctuation constants are still chosen after the finite moment exponent. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct Ccrude : ℝ, 0 < Cfluct ∧ 0 < Ccrude ∧
          ∀ {t αbad Den : ℝ},
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
            let A : ℝ :=
              (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
            let Acrude : ℝ :=
              (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
            let ρtop : ℝ := (3 : ℝ) ^ ctop
            let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
            let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
            let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
            0 < t →
            t ≤ b →
            0 ≤ αbad →
            αbad < t →
            αbad < b →
            αbad * (1 + b / a) < b →
            αbad < a →
            0 < Den →
            Dhigh ^ τ ≤ Den ^ η →
            Dcrude ^ σ ≤ Den ^ η →
            1 ≤ A →
            1 ≤ Acrude →
            (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
              Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
            P.real (badScaleEvent Hshift t αbad q) ≤
              (S.card : ℝ) *
                  (Real.exp (-(A ^ η)) *
                    weightedLinearExpKernelConst w (ρtop ^ τ)) +
                ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
                  (Real.exp (-(A ^ η)) *
                    weightedGeometricExpKernelConst w (ρbottom ^ η)) +
                ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
                  (Real.exp (-(Acrude ^ η)) *
                    weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
  obtain ⟨Centry, a, hCentry, ha, hhighBase⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, hCfluct, hhighRaw⟩ := hhighBase hσ_pos
  obtain ⟨Ccrude, hCcrude, hcrudeRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, hCfluct, hCcrude, ?_⟩
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hDen hDen_high hDen_crude
    hA_one hAcrude_one hq_large
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
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let Acrude : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have htop :
      P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
        (S.card : ℝ) *
          (Real.exp (-(A ^ η)) *
            weightedLinearExpKernelConst w (ρtop ^ τ)) := by
    simpa [K, N0, Hshift, S, b, L, ctop, τ, η, w, Dhigh, A, ρtop] using
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_badPair_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hhighRaw
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hΓ hσ_eq hparams (q := q)
        ht htb hαt hαb hαharm hDen hDen_high hA_one
  have hbottom :
      P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
          (Real.exp (-(A ^ η)) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)) := by
    simpa [K, N0, Hshift, S, b, L, τ, η, w, Dhigh, Dcrude, A, ρbottom,
      Cbottom] using
      measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_weighted_kernel_of_row_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
        (Centry := Centry) (a := a)
        hσ_pos params
        (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_interpolated_weighted_row_of_soft_max_bound
          (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
          (Centry := Centry) (a := a)
          hσ_pos params hCfluct hCcrude hCentry ha
          (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_max_mixed_of_badPair_bounds
            (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
            (Centry := Centry) (a := a)
            hσ_pos params hCfluct hCcrude hCentry ha hhighRaw hcrudeRaw))
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hΓ hσ_eq hparams (q := q)
        ht htb hαt hDen hDen_high hDen_crude hA_one
  have hcrude :
      P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
          (Real.exp (-(Acrude ^ η)) *
            weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
    simpa [K, N0, Hshift, S, L, η, w, Dcrude, Acrude, ρcrude] using
      measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_component_bound
        (d := d) (σ := σ) (Ccrude := Ccrude)
        hσ_pos hCcrude (params := params)
        (measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
          (d := d) (σ := σ) (Ccrude := Ccrude)
          hσ_pos hCcrude params hcrudeRaw)
        (Centry := Centry) (a := a) (t := t) (αbad := αbad)
        (Den := Den) hP hStruct hΓ hσ_eq hparams (q := q)
        ha ht hαt hDen hDen_crude hAcrude_one
  exact
    measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      ha hα_nonneg hαt hαa
      (by simpa [K, L] using hq_large)
      htop hbottom hcrude

/-- Same synchronized component-sum bound after selecting the common
denominator that dominates both raw branch denominators. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_selected_denominator
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
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let Acrude : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        1 ≤ A →
        1 ≤ Acrude →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        P.real (badScaleEvent Hshift t αbad q) ≤
          (S.card : ℝ) *
              (Real.exp (-(A ^ η)) *
                weightedLinearExpKernelConst w (ρtop ^ τ)) +
            ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
              (Real.exp (-(A ^ η)) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)) +
            ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
              (Real.exp (-(Acrude ^ η)) *
                weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hjoint⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hA_one hAcrude_one hq_large
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hτ_pos : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hDen_bounds :=
    branch_denominator_le_mixedBottomTailDenominator_pow_eta
      (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
      hη_pos hτ_pos hσ_pos hDhigh_pos hDcrude_pos
  simpa [K, S, b, L, τ, η, Dhigh, Dcrude, Den] using
    hjoint (t := t) (αbad := αbad) (Den := Den)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa hDen_pos
      hDen_bounds.1 hDen_bounds.2 hA_one hAcrude_one hq_large

/-- Uniform-in-`σ` selected-denominator component-sum bound. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_selected_denominator_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct Ccrude : ℝ, 0 < Cfluct ∧ 0 < Ccrude ∧
          ∀ {t αbad : ℝ},
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
            let A : ℝ :=
              (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
            let Acrude : ℝ :=
              (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
            let ρtop : ℝ := (3 : ℝ) ^ ctop
            let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
            let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
            let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
            0 < t →
            t ≤ b →
            0 ≤ αbad →
            αbad < t →
            αbad < b →
            αbad * (1 + b / a) < b →
            αbad < a →
            1 ≤ A →
            1 ≤ Acrude →
            (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
              Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
            P.real (badScaleEvent Hshift t αbad q) ≤
              (S.card : ℝ) *
                  (Real.exp (-(A ^ η)) *
                    weightedLinearExpKernelConst w (ρtop ^ τ)) +
                ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
                  (Real.exp (-(A ^ η)) *
                    weightedGeometricExpKernelConst w (ρbottom ^ η)) +
                ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
                  (Real.exp (-(Acrude ^ η)) *
                    weightedGeometricExpKernelConst w (ρcrude ^ σ)) := by
  obtain ⟨Centry, a, hCentry, ha, hcomponentBase⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_component_sum_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, Ccrude, hCfluct, hCcrude, hjoint⟩ :=
    hcomponentBase hσ_pos
  refine ⟨Cfluct, Ccrude, hCfluct, hCcrude, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa hA_one hAcrude_one hq_large
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hτ_pos : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hDen_bounds :=
    branch_denominator_le_mixedBottomTailDenominator_pow_eta
      (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
      hη_pos hτ_pos hσ_pos hDhigh_pos hDcrude_pos
  simpa [K, S, b, L, τ, η, Dhigh, Dcrude, Den] using
    hjoint (t := t) (αbad := αbad) (Den := Den)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hα_nonneg hαt hαb hαharm hαa hDen_pos
      hDen_bounds.1 hDen_bounds.2 hA_one hAcrude_one hq_large

end

end Section57
end Ch05
end Book
end Homogenization
