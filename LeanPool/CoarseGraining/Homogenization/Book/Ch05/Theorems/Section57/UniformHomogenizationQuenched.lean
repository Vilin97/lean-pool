/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformScaleCompressionFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched

/-! # Uniform Homogenization Quenched -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Quenched homogenization at the uniform endpoint

This file assembles the `Γ∞` endpoint bad-scale proof into the shifted
quenched estimate with stochastic integrability exponent `d`.
-/

noncomputable section

/-- If the normalizing random scale is enlarged, the negative-power right hand
side in the quenched estimate becomes larger. -/
theorem rpow_neg_div_mono_of_le
    {A X Y α : ℝ} (hA : 0 < A) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ≤ Y) (hα : 0 < α) :
    (A / X) ^ (-α) ≤ (A / Y) ^ (-α) := by
  have hbaseX : 0 < A / X := div_pos hA hX
  have hbaseY : 0 < A / Y := div_pos hA hY
  have hbaseYX : A / Y ≤ A / X :=
    div_le_div_of_nonneg_left hA.le hX hXY
  exact
    (Real.rpow_le_rpow_iff_of_neg hbaseX hbaseY
      (neg_neg_of_pos hα)).2 hbaseYX

/-- Algebraic form of a discounted deterministic bound. -/
theorem discount_mul_rpow_eq_div_rpow_neg
    {D t α : ℝ} {m n : ℕ}
    (hD : 0 < D) (hα : 0 < α) :
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * D ^ α =
      ((3 : ℝ) ^ ((t / α) * ((m - n : ℕ) : ℝ)) / D) ^ (-α) := by
  let s : ℝ := ((m - n : ℕ) : ℝ)
  let R : ℝ := (t / α) * s
  have h3_nonneg : (0 : ℝ) ≤ 3 := by norm_num
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  have hnum_nonneg : 0 ≤ (3 : ℝ) ^ R :=
    (Real.rpow_pos_of_pos h3_pos R).le
  have hRα : R * (-α) = -t * s := by
    dsimp [R]
    field_simp [hα.ne']
  calc
    (3 : ℝ) ^ (-t * s) * D ^ α
        = ((3 : ℝ) ^ R) ^ (-α) * D ^ α := by
            rw [← Real.rpow_mul h3_nonneg, hRα]
    _ = ((3 : ℝ) ^ R) ^ (-α) / D ^ (-α) := by
            rw [Real.rpow_neg hD.le α]
            field_simp [Real.rpow_pos_of_pos hD α |>.ne']
    _ = ((3 : ℝ) ^ R / D) ^ (-α) := by
            rw [Real.div_rpow hnum_nonneg hD.le (-α)]

/-- Deterministic control of the finite band below the entry scale.  The
factor `3 ^ N0 * D` built into `X` pays for all bottoms `n < N0`. -/
theorem small_bottom_deterministic_estimate
    {J D X t α : ℝ} {m n N0 : ℕ}
    (hD : 1 ≤ D) (hJ : J ≤ D ^ α)
    (hXlower : (3 : ℝ) ^ N0 * D ≤ X)
    (hXupper : X ≤ (3 : ℝ) ^ m)
    (hnN0 : n < N0) (_hnm : n < m)
    (hα : 0 < α) (hαt : α < t) :
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * J ≤
      ((3 : ℝ) ^ m / X) ^ (-α) := by
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hX_pos : 0 < X := by
    have hpow_pos : 0 < (3 : ℝ) ^ N0 := by positivity
    have hlower_pos : 0 < (3 : ℝ) ^ N0 * D := mul_pos hpow_pos hD_pos
    exact hlower_pos.trans_le hXlower
  have hpowm_pos : 0 < (3 : ℝ) ^ m := by positivity
  have hpowN0_le_powm : (3 : ℝ) ^ N0 ≤ (3 : ℝ) ^ m := by
    calc
      (3 : ℝ) ^ N0 ≤ (3 : ℝ) ^ N0 * D := by
        have hpow_nonneg : 0 ≤ (3 : ℝ) ^ N0 := by positivity
        nlinarith
      _ ≤ (3 : ℝ) ^ m := hXlower.trans hXupper
  have hN0m_real : (N0 : ℝ) ≤ (m : ℝ) := by
    have hpow_rpow :
        (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (3 : ℝ) ^ ((m : ℕ) : ℝ) := by
      simpa [Real.rpow_natCast] using hpowN0_le_powm
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).1 hpow_rpow
  have hN0m : N0 ≤ m := by exact_mod_cast hN0m_real
  have hmn_le : ((m - N0 : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_left (le_of_lt hnN0) m
  have hratio_one : 1 ≤ t / α := by
    have hle : α / α ≤ t / α :=
      div_le_div_of_nonneg_right hαt.le hα.le
    simpa [hα.ne'] using hle
  have hexp_le :
      ((m - N0 : ℕ) : ℝ) ≤ (t / α) * ((m - n : ℕ) : ℝ) := by
    have hs_nonneg : 0 ≤ ((m - n : ℕ) : ℝ) := by positivity
    calc
      ((m - N0 : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := hmn_le
      _ = 1 * ((m - n : ℕ) : ℝ) := by ring
      _ ≤ (t / α) * ((m - n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hratio_one hs_nonneg
  let Bsmall : ℝ :=
    (3 : ℝ) ^ ((t / α) * ((m - n : ℕ) : ℝ)) / D
  have hbase_bound :
      (3 : ℝ) ^ m / X ≤ Bsmall := by
    have hden_pos : 0 < (3 : ℝ) ^ N0 * D := by positivity
    have hdiv_lower :
        (3 : ℝ) ^ m / X ≤ (3 : ℝ) ^ m / ((3 : ℝ) ^ N0 * D) :=
      div_le_div_of_nonneg_left hpowm_pos.le hden_pos hXlower
    have hpow_split : (3 : ℝ) ^ m = (3 : ℝ) ^ N0 * (3 : ℝ) ^ (m - N0) := by
      rw [← pow_add]
      rw [Nat.add_sub_of_le hN0m]
    have hdiv_eq :
        (3 : ℝ) ^ m / ((3 : ℝ) ^ N0 * D) =
          (3 : ℝ) ^ (m - N0) / D := by
      rw [hpow_split]
      field_simp [pow_ne_zero N0 (by norm_num : (3 : ℝ) ≠ 0)]
    have hpow_exp :
        (3 : ℝ) ^ (m - N0) ≤
          (3 : ℝ) ^ ((t / α) * ((m - n : ℕ) : ℝ)) := by
      have hpow_rpow :
          (3 : ℝ) ^ ((m - N0 : ℕ) : ℝ) ≤
            (3 : ℝ) ^ ((t / α) * ((m - n : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) hexp_le
      simpa [Real.rpow_natCast] using hpow_rpow
    calc
      (3 : ℝ) ^ m / X
          ≤ (3 : ℝ) ^ m / ((3 : ℝ) ^ N0 * D) := hdiv_lower
      _ = (3 : ℝ) ^ (m - N0) / D := hdiv_eq
      _ ≤ (3 : ℝ) ^ ((t / α) * ((m - n : ℕ) : ℝ)) / D :=
          div_le_div_of_nonneg_right hpow_exp hD_pos.le
  have hBsmall_pos : 0 < Bsmall := by
    dsimp [Bsmall]
    exact div_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _) hD_pos
  have hdiscount_D :
      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * D ^ α =
        Bsmall ^ (-α) := by
    simpa [Bsmall] using
      discount_mul_rpow_eq_div_rpow_neg
        (D := D) (t := t) (α := α) (m := m) (n := n)
        hD_pos hα
  calc
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * J
        ≤ (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * D ^ α :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Bsmall ^ (-α) := hdiscount_D
    _ ≤ ((3 : ℝ) ^ m / X) ^ (-α) := by
      exact
        (Real.rpow_le_rpow_iff_of_neg hBsmall_pos
          (div_pos hpowm_pos hX_pos) (neg_neg_of_pos hα)).2 hbase_bound

theorem exists_shifted_quenchedLocalizedEstimate_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
        let b : ℝ := (d : ℝ) / 2
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hInf.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := ((d : ℕ) : ℝ)
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
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
    exists_quantitative_shifted_quenchedLocalizedEstimate_uniformEndpoint
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
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
  obtain ⟨R, _hR, hminR⟩ :=
    hmin (t := t) (αbad := αbad)
      ht hα_nonneg hαt hαb hαharm hαa htb
  obtain ⟨Cscale, hCscale_pos, hscale⟩ :=
    explicit_uniformEndpoint_minimalScale_prefactor_le_exp_logSq
      (d := d) (Cfluct := Cfluct) (Ccrude := Ccrude)
      (a := a) (t := t) (αbad := αbad) (R := R)
      hCfluct hCcrude ha ht (by simpa [b] using htb)
  refine ⟨Cscale, hCscale_pos, ?_⟩
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
  let X : RegCoeffField d → ℝ := quenchedMinimalScale Q Bad
  have hpack :=
    hminR hP hStruct hInf hparams
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
        Real.exp (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)) :=
    hscale hInf.thetaHat hInf.thetaHat_pos
  refine ⟨X, ?_, hXone, hpoint⟩
  exact IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hO hscaleθ

theorem exists_shifted_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry α : ℝ, 0 < Centry ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {t : ℝ},
        max params.sUpper params.sLower < t →
        t ≤ (d : ℝ) / 2 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hInf.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := ((d : ℕ) : ℝ)
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
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
    exists_shifted_quenchedLocalizedEstimate_uniformEndpoint_expLogSq
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
  refine ⟨Centry, α, hCentry, hα_pos, by simpa [s0] using hαs0, ?_⟩
  intro t ht htb
  have ht_pos : 0 < t := hs0.trans ht
  have hαt : α < t := hαs0.trans ht
  obtain ⟨Cscale, hCscale_pos, hlaw⟩ :=
    hbase (t := t) (αbad := α)
      ht_pos hα_pos.le hαt hαb hαharm hαa (by simpa [b] using htb)
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hInf hparams
  exact hlaw hP hStruct hInf hparams

theorem exists_aboveEntry_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry α : ℝ, 0 < Centry ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {t : ℝ},
        max params.sUpper params.sLower < t →
        t ≤ (d : ℝ) / 2 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hInf.toQuantitativeCoarseGrainedEllipticity Centry
            let η : ℝ := ((d : ℕ) : ℝ)
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
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
  obtain ⟨Centry, α, hCentry, hα_pos, hαs0, hshifted⟩ :=
    exists_shifted_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
      (d := d) params
  obtain ⟨CentryEntry, hCentryEntry_pos, hentry⟩ :=
    exists_entryScale_pow_three_le_exp_logSq
      (d := d) (σ := (1 : ℝ)) (Centry := Centry)
      zero_lt_one hCentry params
  refine ⟨Centry, α, hCentry, hα_pos, hαs0, ?_⟩
  intro t ht htb
  obtain ⟨Cshift, hCshift_pos, hlaw⟩ := hshifted (t := t) ht htb
  let Ctotal : ℝ := CentryEntry + Cshift
  have hCtotal_pos : 0 < Ctotal := by
    dsimp [Ctotal]
    positivity
  refine ⟨Ctotal, hCtotal_pos, ?_⟩
  intro P hP hStruct hInf hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let η : ℝ := ((d : ℕ) : ℝ)
  obtain ⟨Xshift, hOshift, hXshift_one, hpoint_shift⟩ :=
    hlaw hP hStruct hInf hparams
  let Xabs : RegCoeffField d → ℝ := fun aω => (3 : ℝ) ^ N0 * Xshift aω
  have hentry_bound :
      (3 : ℝ) ^ N0 ≤
        Real.exp
          (CentryEntry * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)) := by
    simpa [N0, GammaInfinityCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity]
      using!
        hentry hP hStruct (hInf.toGammaSigma 1 zero_lt_one)
          rfl hparams
  have hOabs_raw :
      IsBigO P (gammaSigma η) Xabs
        ((3 : ℝ) ^ N0 *
          Real.exp (Cshift * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) := by
    simpa [Xabs, η] using
      IndependentSums.IsBigO.const_mul
        (μ := P) (Ψ := gammaSigma η) (X := Xshift)
        (A := Real.exp (Cshift * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)))
        (c := (3 : ℝ) ^ N0)
        (by positivity : 0 ≤ (3 : ℝ) ^ N0) hOshift
  have hscale_abs :
      (3 : ℝ) ^ N0 *
          Real.exp (Cshift * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)) ≤
        Real.exp (Ctotal * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ)
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
          (Ctotal * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) :=
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
      have htarget :
          (3 : ℝ) ^ N0 * Xshift aω ≤
            (3 : ℝ) ^ N0 * (3 : ℝ) ^ m' := by
        simpa [Xabs, hpowm] using hXabs_le
      have hpow_pos : 0 < (3 : ℝ) ^ N0 := by positivity
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

/-- Note-facing quenched homogenization estimate at the uniform ellipticity
endpoint.

The stochastic scale has `Γ_d` integrability.  The constant `Cscale` is chosen
before the law; the law only contributes the endpoint datum `thetaHat`. -/
theorem exists_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {t : ℝ},
        max params.sUpper params.sLower < t →
        t ≤ (d : ℝ) / 2 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            let η : ℝ := ((d : ℕ) : ℝ)
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          localizedLimitNormalizedJMax hP hStruct m n e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  obtain ⟨Centry, α, hCentry, hα_pos, hαs0, habove⟩ :=
    exists_aboveEntry_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
      (d := d) params
  obtain ⟨CentryEntry, hCentryEntry_pos, hentry⟩ :=
    exists_entryScale_pow_three_le_exp_logSq
      (d := d) (σ := (1 : ℝ)) (Centry := Centry)
      zero_lt_one hCentry params
  classical
  let Kdet : ℝ :=
    quenchedProbeEnvelopeConst d *
      GammaInfinityCoarseGrainedEllipticity.unitJConst d params
  let Aextra : ℝ := (max 1 Kdet) ^ α⁻¹
  let pextra : ℝ := 2 * α⁻¹
  let Cextra : ℝ := 4 * max 0 (Real.log Aextra) + 2 * pextra
  have hKdet_pos : 0 < Kdet := by
    dsimp [Kdet]
    exact mul_pos (quenchedProbeEnvelopeConst_pos d)
      (GammaInfinityCoarseGrainedEllipticity.unitJConst_pos
        (d := d) params)
  have hAextra_pos : 0 < Aextra := by
    dsimp [Aextra]
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Kdet)) α⁻¹
  have hpextra_nonneg : 0 ≤ pextra := by
    dsimp [pextra]
    positivity
  have hCextra_nonneg : 0 ≤ Cextra := by
    dsimp [Cextra]
    have hlog_nonneg : 0 ≤ max 0 (Real.log Aextra) := le_max_left 0 _
    nlinarith
  refine ⟨α, hα_pos, hαs0, ?_⟩
  intro t ht htb
  have hαt : α < t := hαs0.trans ht
  obtain ⟨Cabove, hCabove_pos, habove_law⟩ :=
    habove (t := t) ht htb
  let Cscale : ℝ := CentryEntry + Cextra + Cabove
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hInf hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let η : ℝ := ((d : ℕ) : ℝ)
  obtain ⟨Xabove, hOabove, hXabove_one, hpoint_above⟩ :=
    habove_law hP hStruct hInf hparams
  let θ : ℝ := hInf.thetaHat
  let Jscale : ℝ := Kdet * θ ^ (2 : ℕ)
  let Dsmall : ℝ := (max 1 Jscale) ^ α⁻¹
  let G : ℝ := (3 : ℝ) ^ N0 * Dsmall
  let X : RegCoeffField d → ℝ := fun aω => G * Xabove aω
  have hentry_bound :
      (3 : ℝ) ^ N0 ≤
        Real.exp
          (CentryEntry * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    simpa [N0, θ,
      GammaInfinityCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity]
      using!
        hentry hP hStruct (hInf.toGammaSigma 1 zero_lt_one)
          rfl hparams
  have hDsmall_one : 1 ≤ Dsmall := by
    dsimp [Dsmall]
    exact Real.one_le_rpow (le_max_left 1 Jscale)
      (inv_nonneg.mpr hα_pos.le)
  have hDsmall_pos : 0 < Dsmall :=
    lt_of_lt_of_le zero_lt_one hDsmall_one
  have hDpow_eq : Dsmall ^ α = max 1 Jscale := by
    dsimp [Dsmall]
    exact Real.rpow_inv_rpow
      (le_trans zero_le_one (le_max_left 1 Jscale)) hα_pos.ne'
  have hJscale_le_D : Jscale ≤ Dsmall ^ α := by
    calc
      Jscale ≤ max 1 Jscale := le_max_right 1 Jscale
      _ = Dsmall ^ α := hDpow_eq.symm
  have hDsmall_poly :
      Dsmall ≤ Aextra * (max 1 θ) ^ pextra := by
    simpa [Dsmall, Jscale, Kdet, Aextra, pextra, θ] using
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := Kdet) (θ := θ) (r := α⁻¹)
        hInf.thetaHat_pos.le (inv_nonneg.mpr hα_pos.le)
  have hDsmall_exp :
      Dsmall ≤
        Real.exp (Cextra * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    calc
      Dsmall ≤ Aextra * (max 1 θ) ^ pextra := hDsmall_poly
      _ ≤ Real.exp
          (Cextra * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
          simpa [Cextra, θ] using
            const_mul_rpow_max_one_le_exp_logSq
              (A := Aextra) (θ := θ) (p := pextra)
              hAextra_pos hInf.thetaHat_pos.le hpextra_nonneg
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    positivity
  have hG_one : 1 ≤ G := by
    dsimp [G]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) hDsmall_one
  have hG_bound :
      G ≤
        Real.exp
          ((CentryEntry + Cextra) *
            (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
    calc
      G = (3 : ℝ) ^ N0 * Dsmall := rfl
      _ ≤ Real.exp (CentryEntry * L2) *
          Real.exp (Cextra * L2) :=
          mul_le_mul hentry_bound hDsmall_exp
            (by positivity) (by positivity)
      _ = Real.exp ((CentryEntry + Cextra) * L2) := by
          rw [← Real.exp_add]
          ring_nf
  have hOraw :
      IsBigO P (gammaSigma η) X
        (G * Real.exp (Cabove * (Real.log (2 + θ)) ^ (2 : ℕ))) := by
    simpa [X, η, θ] using
      IndependentSums.IsBigO.const_mul
        (μ := P) (Ψ := gammaSigma η) (X := Xabove)
        (A := Real.exp (Cabove * (Real.log (2 + θ)) ^ (2 : ℕ)))
        (c := G) hG_nonneg hOabove
  have hscale_final :
      G * Real.exp (Cabove * (Real.log (2 + θ)) ^ (2 : ℕ)) ≤
        Real.exp
          (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
    calc
      G * Real.exp (Cabove * L2)
          ≤ Real.exp ((CentryEntry + Cextra) * L2) *
              Real.exp (Cabove * L2) :=
          mul_le_mul_of_nonneg_right hG_bound (Real.exp_pos _).le
      _ = Real.exp (Cscale * L2) := by
          rw [← Real.exp_add]
          dsimp [Cscale]
          ring_nf
  have hOfinal :
      IsBigO P (gammaSigma η) X
        (Real.exp
          (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ))) :=
    IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hOraw hscale_final
  refine ⟨X, hOfinal, ?_, ?_⟩
  · intro aω
    dsimp [X]
    exact one_le_mul_of_one_le_of_one_le hG_one (hXabove_one aω)
  · intro e he
    have habove_e := hpoint_above e he
    have hdet_e :
        ∀ᵐ aω ∂P, ∀ m n : ℕ, n ≤ m →
          localizedLimitNormalizedJMax hP hStruct m n e aω ≤ Jscale := by
      rw [MeasureTheory.ae_all_iff]
      intro m
      rw [MeasureTheory.ae_all_iff]
      intro n
      by_cases hnm_le : n ≤ m
      · have hprobe :=
          localizedLimitNormalizedJMax_le_quenchedProbeEnvelope_ae
            hP hStruct (hInf.toGammaSigma 1 zero_lt_one)
            hnm_le e he
        have hmax :=
          hInf.localizedNormalizedProbeJMax_le_thetaHat_sq_ae
            (m := m) (n := n) hnm_le
        filter_upwards [hprobe, hmax] with aω hprobe_a hmax_a _
        calc
          localizedLimitNormalizedJMax hP hStruct m n e aω
              ≤ quenchedProbeEnvelope hP hStruct m n aω := hprobe_a
          _ ≤ Jscale := by
              have hK_nonneg : 0 ≤ quenchedProbeEnvelopeConst d :=
                quenchedProbeEnvelopeConst_nonneg d
              calc
                quenchedProbeEnvelope hP hStruct m n aω
                    = quenchedProbeEnvelopeConst d *
                        localizedNormalizedProbeJMax hP hStruct m n aω := by
                        simp [quenchedProbeEnvelope]
                _ ≤ quenchedProbeEnvelopeConst d *
                    (GammaInfinityCoarseGrainedEllipticity.unitJConst d params *
                      θ ^ (2 : ℕ)) := by
                    simpa [θ, hparams] using
                      mul_le_mul_of_nonneg_left hmax_a hK_nonneg
                _ = Jscale := by
                    simp [Jscale, Kdet]
                    ring
      · exact Filter.Eventually.of_forall fun _ hnm' =>
          False.elim (hnm_le hnm')
    filter_upwards [habove_e, hdet_e] with aω habove_a hdet_a
    intro m n hX_le hnm
    by_cases hN0n : N0 ≤ n
    · have hXabove_le_X : Xabove aω ≤ X aω := by
        dsimp [X]
        calc
          Xabove aω = 1 * Xabove aω := by ring
          _ ≤ G * Xabove aω :=
              mul_le_mul_of_nonneg_right hG_one (by
                exact le_trans zero_le_one (hXabove_one aω))
      have hXabove_le_pow : Xabove aω ≤ (3 : ℝ) ^ m :=
        hXabove_le_X.trans hX_le
      have hres :=
        habove_a (m := m) (n := n) hN0n hXabove_le_pow hnm
      have hmono :
          ((3 : ℝ) ^ m / Xabove aω) ^ (-α) ≤
            ((3 : ℝ) ^ m / X aω) ^ (-α) := by
        exact rpow_neg_div_mono_of_le
          (A := (3 : ℝ) ^ m) (X := Xabove aω) (Y := X aω)
          (by positivity)
          (lt_of_lt_of_le zero_lt_one (hXabove_one aω))
          (lt_of_lt_of_le zero_lt_one
            (by simpa [X] using
              one_le_mul_of_one_le_of_one_le hG_one (hXabove_one aω)))
          hXabove_le_X hα_pos
      exact hres.trans hmono
    · have hnN0 : n < N0 := Nat.lt_of_not_ge hN0n
      have hloc_le :
          localizedLimitNormalizedJMax hP hStruct m n e aω ≤ Dsmall ^ α :=
        (hdet_a m n (le_of_lt hnm)).trans hJscale_le_D
      have hXlower : (3 : ℝ) ^ N0 * Dsmall ≤ X aω := by
        dsimp [X, G]
        calc
          (3 : ℝ) ^ N0 * Dsmall
              = ((3 : ℝ) ^ N0 * Dsmall) * 1 := by ring
          _ ≤ ((3 : ℝ) ^ N0 * Dsmall) * Xabove aω :=
              mul_le_mul_of_nonneg_left (hXabove_one aω)
                (by positivity)
      exact
        small_bottom_deterministic_estimate
          (J := localizedLimitNormalizedJMax hP hStruct m n e aω)
          (D := Dsmall) (X := X aω) (t := t) (α := α)
          (m := m) (n := n) (N0 := N0)
          hDsmall_one hloc_le hXlower hX_le hnN0 hnm hα_pos hαt

end

end Section57
end Ch05
end Book
end Homogenization
