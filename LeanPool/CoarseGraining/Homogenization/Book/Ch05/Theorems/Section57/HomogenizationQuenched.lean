/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EntryScaleCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompressionFinal

/-! # Homogenization Quenched -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Quenched homogenization above the quantitative minimal scale

This file applies the deterministic scale compression to the quantitative
minimal-scale theorem.  The result is still written with the shifted entry
scale `N0`; the final public wrapper only has to choose the admissible
exponent `alpha` and undo the harmless shift.
-/

noncomputable section

theorem exists_shifted_quenchedLocalizedEstimate_interpolated_expLogSq
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
        let b : ℝ := (d : ℝ) / 2
        0 < t →
        t ≤ b →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := finiteQuenchedTailExponent d σ t
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
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
      hCfluct, hCcrude, hCentry, ha, hmin⟩ :=
    exists_quantitative_shifted_quenchedLocalizedEstimate_interpolated
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro t αbad
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
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
  obtain ⟨R, _hR, hminR⟩ :=
    hmin (t := t) (αbad := αbad)
      ht htb hα_nonneg hαt hαb hαharm hαa
  let QcutConst : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
  obtain ⟨Cscale, hCscale_pos, hscale⟩ :=
    explicit_minimalScale_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := Ccrude)
      (a := a) (t := t) (αbad := αbad) (R := R)
      hσ_pos hCfluct hCcrude ha ht
  refine ⟨Cscale, hCscale_pos, ?_⟩
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
  let X : RegCoeffField d → ℝ := quenchedMinimalScale Q Bad
  have hpack :=
    hminR hP hStruct hΓ hσ_eq hparams
  dsimp only at hpack
  change
    IsBigO P (gammaSigma η) X (3 * ((3 : ℝ) ^ Q) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct
                    (N0 + m) (N0 + n) e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-αbad) at hpack
  rcases hpack with ⟨hO, hXone, hpoint⟩
  have hscaleθ :
      3 * ((3 : ℝ) ^ Q) * B ≤
        Real.exp (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    exact hscale hΓ.thetaHat hΓ.thetaHat_pos
  refine ⟨X, ?_, hXone, hpoint⟩
  exact IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hO hscaleθ

/-- The larger regularity exponent in the parameter-only `(P4)` data is
positive. -/
theorem max_sUpper_sLower_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < max params.sUpper params.sLower :=
  lt_of_lt_of_le params.sUpper_pos (le_max_left _ _)

/-- The shifted quenched estimate with a single exponent selected from the
moment parameters.

The exponent `alpha` is chosen before the law.  For every decay exponent
`t > max sUpper sLower` with `t ≤ d / 2`, the stochastic scale has the manuscript
`exp(C log^2(2 + thetaHat))` size and the interpolated tail exponent
`finiteQuenchedTailExponent d sigma t`. -/
theorem exists_shifted_quenchedLocalizedEstimate_interpolated_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry α : ℝ, 0 < Centry ∧ 0 < α ∧
      ∀ {t : ℝ}, max params.sUpper params.sLower < t →
        t ≤ (d : ℝ) / 2 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := finiteQuenchedTailExponent d σ t
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct
                            (N0 + m) (N0 + n) e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Centry, a, hCentry, ha, hbase⟩ :=
    exists_shifted_quenchedLocalizedEstimate_interpolated_expLogSq
      (d := d) (σ := σ) hσ_pos params
  let b : ℝ := (d : ℝ) / 2
  let s0 : ℝ := max params.sUpper params.sLower
  have hb : 0 < b := by
    have hd_nat : 0 < d :=
      lt_of_lt_of_le (by norm_num : 0 < 2) params.two_le_dim
    have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_nat
    dsimp [b]
    linarith
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact max_sUpper_sLower_pos params
  obtain ⟨α, hα_pos, hαs0, hαa, hαb, hαharm⟩ :=
    exists_alpha_for_highCompetition (a := a) (b := b) (t := s0)
      ha hb hs0
  refine ⟨Centry, α, hCentry, hα_pos, ?_⟩
  intro t ht htb
  have ht_pos : 0 < t := hs0.trans ht
  have hαt : α < t := hαs0.trans ht
  obtain ⟨Cscale, hCscale_pos, hlaw⟩ :=
    hbase (t := t) (αbad := α)
      ht_pos (by simpa [b] using htb) hα_pos.le hαt hαb hαharm hαa
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  exact hlaw hP hStruct hΓ hσ_eq hparams

/-- Absolute-scale version of the shifted quenched estimate, valid once the
bottom scale has passed the annealed entry scale.

Compared with
`exists_shifted_quenchedLocalizedEstimate_interpolated_expLogSq_parameterAlpha`,
the random scale is multiplied by `3 ^ N0`; the deterministic entry-scale
compression from `EntryScaleCompression` keeps the same manuscript
`exp(C log^2(2 + thetaHat))` envelope. -/
theorem exists_aboveEntry_quenchedLocalizedEstimate_interpolated_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry α : ℝ, 0 < Centry ∧ 0 < α ∧
      ∀ {t : ℝ}, max params.sUpper params.sLower < t →
        t ≤ (d : ℝ) / 2 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := finiteQuenchedTailExponent d σ t
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      N0 ≤ n →
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Centry, α, hCentry, hα_pos, hshifted⟩ :=
    exists_shifted_quenchedLocalizedEstimate_interpolated_expLogSq_parameterAlpha
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨CentryEntry, hCentryEntry_pos, hentry⟩ :=
    exists_entryScale_pow_three_le_exp_logSq
      (d := d) (σ := σ) (Centry := Centry) hσ_pos hCentry params
  refine ⟨Centry, α, hCentry, hα_pos, ?_⟩
  intro t ht htb
  obtain ⟨Cshift, hCshift_pos, hlaw⟩ := hshifted (t := t) ht htb
  let Ctotal : ℝ := CentryEntry + Cshift
  have hCtotal_pos : 0 < Ctotal := by
    dsimp [Ctotal]
    positivity
  refine ⟨Ctotal, hCtotal_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let η : ℝ := finiteQuenchedTailExponent d σ t
  obtain ⟨Xshift, hOshift, hXshift_one, hpoint_shift⟩ :=
    hlaw hP hStruct hΓ hσ_eq hparams
  let Xabs : RegCoeffField d → ℝ := fun aω => (3 : ℝ) ^ N0 * Xshift aω
  have hentry_bound :
      (3 : ℝ) ^ N0 ≤
        Real.exp
          (CentryEntry * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    simpa [N0] using hentry hP hStruct hΓ hσ_eq hparams
  have hOabs_raw :
      IsBigO P (gammaSigma η) Xabs
        ((3 : ℝ) ^ N0 *
          Real.exp (Cshift * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) := by
    simpa [Xabs, η] using
      IndependentSums.IsBigO.const_mul
        (μ := P) (Ψ := gammaSigma η) (X := Xshift)
        (A := Real.exp (Cshift * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)))
        (c := (3 : ℝ) ^ N0)
        (by positivity : 0 ≤ (3 : ℝ) ^ N0) hOshift
  have hscale_abs :
      (3 : ℝ) ^ N0 *
          Real.exp (Cshift * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) ≤
        Real.exp (Ctotal * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)
    calc
      (3 : ℝ) ^ N0 * Real.exp (Cshift * L2)
          ≤ Real.exp (CentryEntry * L2) * Real.exp (Cshift * L2) :=
            mul_le_mul_of_nonneg_right hentry_bound (Real.exp_pos _).le
      _ = Real.exp (Ctotal * L2) := by
          rw [← Real.exp_add]
          dsimp [Ctotal]
          ring_nf
  have hOabs :
      IsBigO P (gammaSigma η) Xabs
        (Real.exp
          (Ctotal * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) :=
    IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hOabs_raw hscale_abs
  refine ⟨Xabs, hOabs, ?_, ?_⟩
  · intro aω
    have hpow_one : 1 ≤ (3 : ℝ) ^ N0 :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
    exact one_le_mul_of_one_le_of_one_le hpow_one (hXshift_one aω)
  · intro e he
    have hshift_e := hpoint_shift e he
    filter_upwards [hshift_e] with aω hshift_a
    intro m n hN0n hXabs_le hnm
    let m' : ℕ := m - N0
    let n' : ℕ := n - N0
    have hN0m : N0 ≤ m := le_trans hN0n (le_of_lt hnm)
    have hm_eq : N0 + m' = m := by
      dsimp [m']
      exact Nat.add_sub_of_le hN0m
    have hn_eq : N0 + n' = n := by
      dsimp [n']
      exact Nat.add_sub_of_le hN0n
    have hn'm' : n' < m' := by
      dsimp [m', n']
      omega
    have hpowm :
        (3 : ℝ) ^ m = (3 : ℝ) ^ N0 * (3 : ℝ) ^ m' := by
      rw [← pow_add]
      rw [hm_eq]
    have hXshift_le : Xshift aω ≤ (3 : ℝ) ^ m' := by
      have hpow_pos : 0 < (3 : ℝ) ^ N0 := by positivity
      have htarget :
          (3 : ℝ) ^ N0 * Xshift aω ≤
            (3 : ℝ) ^ N0 * (3 : ℝ) ^ m' := by
        simpa [Xabs, hpowm] using hXabs_le
      nlinarith
    have hdiff : (m' - n' : ℕ) = m - n := by
      dsimp [m', n']
      omega
    have hXshift_pos : 0 < Xshift aω :=
      lt_of_lt_of_le zero_lt_one (hXshift_one aω)
    have hquot :
        (3 : ℝ) ^ m' / Xshift aω =
          (3 : ℝ) ^ m / Xabs aω := by
      dsimp [Xabs]
      rw [hpowm]
      field_simp [hXshift_pos.ne', pow_ne_zero N0 (by norm_num : (3 : ℝ) ≠ 0)]
    have hresult :=
      hshift_a (m := m') (n := n') hXshift_le hn'm'
    simpa [N0, hm_eq, hn_eq, hdiff, hquot] using hresult

/-- Note-facing quenched homogenization estimate above a random minimal scale.

The exponent `alpha` is selected before the law and depends only on the
dimension and the moment parameters.  For each admissible `t`, the scale
constant is selected before the probability law; the stochastic integrability
exponent is the corrected finite-`sigma` exponent
`finiteQuenchedTailExponent d sigma t`. -/
theorem exists_quenchedLocalizedEstimate_interpolated_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      ∀ {t : ℝ}, max params.sUpper params.sLower < t → t ≤ 1 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let η : ℝ := finiteQuenchedTailExponent d σ t
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
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
      hCfluct, hCcrudeShift, hCsmall, hCentry, ha, habsBase⟩ :=
    exists_quantitative_absolute_quenchedLocalizedEstimate_interpolated
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨CentryEntry, hCentryEntry_pos, hentry⟩ :=
    exists_entryScale_pow_three_le_exp_logSq
      (d := d) (σ := σ) (Centry := Centry) hσ_pos hCentry params
  let b : ℝ := (d : ℝ) / 2
  let s0 : ℝ := max params.sUpper params.sLower
  have hb : 0 < b := by
    have hd_nat : 0 < d :=
      lt_of_lt_of_le (by norm_num : 0 < 2) params.two_le_dim
    have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_nat
    dsimp [b]
    linarith
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact max_sUpper_sLower_pos params
  obtain ⟨α, hα_pos, hαs0, hαa, hαb, hαharm⟩ :=
    exists_alpha_for_highCompetition (a := a) (b := b) (t := s0)
      ha hb hs0
  refine ⟨α, hα_pos, ?_⟩
  intro t ht ht_le_one
  have ht_pos : 0 < t := hs0.trans ht
  have htb : t ≤ b := by
    have hone_le_b : (1 : ℝ) ≤ b := by
      have hd : (2 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast params.two_le_dim
      dsimp [b]
      nlinarith
    exact ht_le_one.trans hone_le_b
  have hαt : α < t := hαs0.trans ht
  obtain ⟨Rshift, Rsmall, Runion, habsLaw⟩ :=
    habsBase (t := t) (α := α)
      ht_pos htb hα_pos.le hαt (by simpa [b] using hαb)
      (by simpa [b] using hαharm) hαa
  obtain ⟨Cscale, hCscale_pos, hscale⟩ :=
    explicit_absoluteMinimalScale_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Cfluct := Cfluct)
      (CcrudeShift := CcrudeShift) (Csmall := Csmall)
      (a := a) (t := t) (α := α) (CentryScale := CentryEntry)
      (Rshift := Rshift) (Rsmall := Rsmall) (Runion := Runion)
      hσ_pos hCfluct hCcrudeShift hCsmall ha ht_pos hαt
      hCentryEntry_pos
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
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
  have hpack :=
    habsLaw hP hStruct hΓ hσ_eq hparams
  dsimp only at hpack
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
                ((3 : ℝ) ^ m / X aω) ^ (-α) at hpack
  rcases hpack with ⟨hO, hXone, hpoint⟩
  have hentry_bound :
      (3 : ℝ) ^ N0 ≤
        Real.exp
          (CentryEntry * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    simpa [N0] using hentry hP hStruct hΓ hσ_eq hparams
  have hscaleθ :
      3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    have hraw :=
      hscale (θ := hΓ.thetaHat) (N0 := N0) hΓ.thetaHat_pos hentry_bound
    dsimp only at hraw
    change
      3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) at hraw
    exact hraw
  refine ⟨X, ?_, hXone, hpoint⟩
  exact IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hO hscaleθ

/-- Note-facing finite-`sigma` quenched estimate with the public exponent
chosen before `sigma`.

The annealed entry constant and the final algebraic exponent depend only on
the dimension and the deterministic moment parameters.  For each finite
moment exponent `sigma`, the fluctuation constants and scale constant may
depend on `sigma`, as in the manuscript. -/
theorem exists_quenchedLocalizedEstimate_interpolated_expLogSq_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {σ : ℝ}, 0 < σ →
      ∀ {t : ℝ}, max params.sUpper params.sLower < t → t ≤ 1 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let η : ℝ := finiteQuenchedTailExponent d σ t
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Centry, a, hCentry, ha, habsBaseUniform⟩ :=
    exists_quantitative_absolute_quenchedLocalizedEstimate_interpolated_uniformAnnealedExponent
      (d := d) params
  let b : ℝ := (d : ℝ) / 2
  let s0 : ℝ := max params.sUpper params.sLower
  have hb : 0 < b := by
    have hd_nat : 0 < d :=
      lt_of_lt_of_le (by norm_num : 0 < 2) params.two_le_dim
    have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_nat
    dsimp [b]
    linarith
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact max_sUpper_sLower_pos params
  obtain ⟨α, hα_pos, hαs0, hαa, hαb, hαharm⟩ :=
    exists_alpha_for_highCompetition (a := a) (b := b) (t := s0)
      ha hb hs0
  refine ⟨α, hα_pos, by simpa [s0] using hαs0, ?_⟩
  intro σ hσ_pos t ht ht_le_one
  obtain ⟨Cfluct, CcrudeShift, Csmall,
      hCfluct, hCcrudeShift, hCsmall, habsBase⟩ :=
    habsBaseUniform hσ_pos
  obtain ⟨CentryEntry, hCentryEntry_pos, hentry⟩ :=
    exists_entryScale_pow_three_le_exp_logSq
      (d := d) (σ := σ) (Centry := Centry) hσ_pos hCentry params
  have ht_pos : 0 < t := hs0.trans ht
  have htb : t ≤ b := by
    have hone_le_b : (1 : ℝ) ≤ b := by
      have hd : (2 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast params.two_le_dim
      dsimp [b]
      nlinarith
    exact ht_le_one.trans hone_le_b
  have hαt : α < t := hαs0.trans ht
  obtain ⟨Rshift, Rsmall, Runion, habsLaw⟩ :=
    habsBase (t := t) (α := α)
      ht_pos htb hα_pos.le hαt (by simpa [b] using hαb)
      (by simpa [b] using hαharm) hαa
  obtain ⟨Cscale, hCscale_pos, hscale⟩ :=
    explicit_absoluteMinimalScale_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Cfluct := Cfluct)
      (CcrudeShift := CcrudeShift) (Csmall := Csmall)
      (a := a) (t := t) (α := α) (CentryScale := CentryEntry)
      (Rshift := Rshift) (Rsmall := Rsmall) (Runion := Runion)
      hσ_pos hCfluct hCcrudeShift hCsmall ha ht_pos hαt
      hCentryEntry_pos
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
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
  have hpack :=
    habsLaw hP hStruct hΓ hσ_eq hparams
  dsimp only at hpack
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
                ((3 : ℝ) ^ m / X aω) ^ (-α) at hpack
  rcases hpack with ⟨hO, hXone, hpoint⟩
  have hentry_bound :
      (3 : ℝ) ^ N0 ≤
        Real.exp
          (CentryEntry * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    simpa [N0] using hentry hP hStruct hΓ hσ_eq hparams
  have hscaleθ :
      3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    have hraw :=
      hscale (θ := hΓ.thetaHat) (N0 := N0) hΓ.thetaHat_pos hentry_bound
    dsimp only at hraw
    change
      3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) at hraw
    exact hraw
  refine ⟨X, ?_, hXone, hpoint⟩
  exact IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hO hscaleθ

end

end Section57
end Ch05
end Book
end Homogenization
