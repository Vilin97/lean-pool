/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentSummation
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop

/-! # Bad Scale Component Bounds High -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# High component bad-scale bounds

This file rebuilds the high component estimates along the no-loss route.  The
finite descendant multiplicity is kept as a probability-level prefactor and is
absorbed by the weighted exponential kernel in the final summation.
-/

noncomputable section

private theorem rpow_three_mul_rpow_pow_nat_eq
    {x y : ℝ} {r : ℕ} :
    (3 : ℝ) ^ x * ((3 : ℝ) ^ y) ^ r =
      (3 : ℝ) ^ (x + y * (r : ℝ)) := by
  have hpow :
      ((3 : ℝ) ^ y) ^ r = (3 : ℝ) ^ (y * (r : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hpow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

private theorem exp_neg_rpow_le_exp_neg_rpow_of_le
    {x y τ : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hτ : 0 < τ) :
    Real.exp (-(y ^ τ)) ≤ Real.exp (-(x ^ τ)) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hpow : x ^ τ ≤ y ^ τ :=
    Real.rpow_le_rpow hx hxy hτ.le
  exact Real.exp_le_exp.mpr (by linarith)

/-- Sharp high-top bad-scale component estimate from a fixed high-pair
tail bound.  This helper exposes the constants so that the top and bottom
high branches can be assembled with the same intermediate-scale exponent. -/
theorem measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
    {d : ℕ} [NeZero d] {σ Cfluct Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (_hCentry : 0 < Centry) (ha : 0 < a)
    (hpair :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ell : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let tau : ℝ := min σ 2
        let scale : ℝ :=
          Cfluct *
            (3 : ℝ) ^
              ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / (2 * K * scale)
        ell < n → n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau)))) :
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
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let τ : ℝ := min σ 2
        let A : ℝ :=
          (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
          (S.card : ℝ) *
            (Real.exp (-(A ^ τ)) * weightedLinearExpKernelConst w (ρ ^ τ)) := by
  intro t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht_pos hαt hαb hαharm hA_one
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
  let L : ℝ :=
    (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let c : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let τ : ℝ := min σ 2
  let A : ℝ :=
    (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ c
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  have hA_one_local : 1 ≤ A := by
    simpa [A, K, L, b] using hA_one
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hL_nonneg : 0 ≤ L := by
    have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    dsimp [L]
    positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    have hta : 0 < t - αbad := sub_pos.mpr hαt
    have hba : 0 < b - αbad := sub_pos.mpr hαb
    have hone_ba : 0 < 1 + b / a := by positivity
    have hprod : 0 < (t - αbad) * (1 + b / a) :=
      mul_pos hta hone_ba
    have hharm : 0 < b - αbad * (1 + b / a) :=
      sub_pos.mpr hαharm
    positivity
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ c :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hc_pos
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hS_nonneg : 0 ≤ (S.card : ℝ) := by positivity
  refine
    measureReal_highTopBadScaleEvent_le_weighted_exp_linear_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := τ) (C := (S.card : ℝ)) (w := w)
      hS_nonneg hw_pos hA_one_local hρ_gt hτ_pos ?_
  intro r j
  let m : ℕ := q + r
  let n : ℕ := q + j.val
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ℓ : ℕ) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / (2 * K * scale)
  have htail_nonneg :
      0 ≤ (S.card : ℝ) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
    positivity
  by_cases hhigh : selectedBadPairScale K a t αbad q m n < n
  · by_cases hnm : n < m
    · have hℓ_eq : ℓ = selectedBadPairScale K a t αbad q m n := by
        dsimp [ℓ, selectedBadPairScale, x, m, n]
      have hℓn : ℓ < n := by
        simpa [hℓ_eq] using hhigh
      have hqn : q ≤ n := by
        dsimp [n]
        exact Nat.le_add_right q j.val
      have hnm_le : n ≤ m := le_of_lt hnm
      have hqm : q ≤ m := by
        dsimp [m]
        exact Nat.le_add_right q r
      have hceil :
          (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
        rw [hℓ_eq]
        simpa [K, L, x, m, n] using
          selectedBadPairScale_cast_le_logOffset
            (K := K) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n) ha
      have hexp_comp :
          b * ((n - ℓ : ℕ) : ℝ) - x ≥
            b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1) := by
        have hraw :=
          highNatScaleExponent_lower_bound_of_ceil_q_le_n_sharp
            (a := a) (b := b) (t := t) (α := αbad) (L := L)
            (q := q) (m := m) (n := n) (ℓ := ℓ)
            ha hb_pos hαt hαb hαharm hL_nonneg
            (le_of_lt hℓn) hqn hnm_le
            (by simpa [x] using hceil)
        simpa [x, c] using hraw
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hscale_pos : 0 < scale := by
        dsimp [scale]
        exact mul_pos
          (mul_pos hCfluct
            (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _))
          (pow_pos hΓ.thetaHat_pos 2)
      have hden_pos : 0 < 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ) := by
        exact mul_pos
          (mul_pos
            (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos)
            hCfluct)
          (pow_pos hΓ.thetaHat_pos 2)
      have hlam_eq :
          lam =
            (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)) := by
        let decay : ℝ :=
          (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ℓ : ℕ) : ℝ))
        have hdecay_pos : 0 < decay := by
          dsimp [decay]
          exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
        have hquot :
            (3 : ℝ) ^ (-x) / decay =
              (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) := by
          dsimp [decay, b]
          rw [div_eq_mul_inv]
          rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 1
          ring_nf
        dsimp [lam, T, scale]
        change
          (3 : ℝ) ^ (-x) /
              (2 * K *
                (Cfluct * decay * hΓ.thetaHat ^ (2 : ℕ))) =
            (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        calc
          (3 : ℝ) ^ (-x) /
              (2 * K *
                (Cfluct * decay * hΓ.thetaHat ^ (2 : ℕ)))
              =
            ((3 : ℝ) ^ (-x) / decay) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)) := by
                field_simp [hK_pos.ne', hCfluct.ne',
                  hΓ.thetaHat_pos.ne', hdecay_pos.ne']
          _ =
            (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)) := by
                rw [hquot]
      have hpow_base :
          (3 : ℝ) ^ (b * (q : ℝ) + c * (r : ℝ) - b * (L + 1)) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
            =
          A * ρ ^ r := by
        dsimp [A, ρ]
        have hrpow :=
          rpow_three_mul_rpow_pow_nat_eq
            (x := b * (q : ℝ) - b * (L + 1))
            (y := c) (r := r)
        calc
          (3 : ℝ) ^ (b * (q : ℝ) + c * (r : ℝ) - b * (L + 1)) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
              =
            ((3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) *
                ((3 : ℝ) ^ c) ^ r) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)) := by
                rw [hrpow]
                congr 1
                ring_nf
          _ =
            ((3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
              (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))) *
                ((3 : ℝ) ^ c) ^ r := by
                field_simp [hden_pos.ne']
      have hlam_lower : A * ρ ^ r ≤ lam := by
        rw [hlam_eq]
        rw [← hpow_base]
        have hmr : ((m - q : ℕ) : ℝ) = (r : ℝ) := by
          dsimp [m]
          rw [Nat.add_sub_cancel_left]
        have hpow_le :
            (3 : ℝ) ^
                (b * (q : ℝ) + c * (r : ℝ) - b * (L + 1)) ≤
              (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) := by
          exact
            Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 3)
              (by
                have hcomp := hexp_comp
                rw [hmr] at hcomp
                linarith)
        exact div_le_div_of_nonneg_right hpow_le hden_pos.le
      have hρ_pow_one : 1 ≤ ρ ^ r :=
        one_le_pow₀ (le_of_lt hρ_gt)
      have hAρ_one : 1 ≤ A * ρ ^ r := by
        simpa using
          mul_le_mul hA_one_local hρ_pow_one
            (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith : 0 ≤ A)
      have hlam_one : 1 ≤ lam := hAρ_one.trans hlam_lower
      have hraw :=
        hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
          (q := q) (m := m) (n := n)
      dsimp only at hraw
      have hbad :
          P.real (badPairEvent Hshift t αbad q m n) ≤
            (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ τ))) := by
        simpa [K, x, ℓ, N0, Hshift, D, S, τ, scale, T, lam] using
          hraw hℓn hnm hqm hlam_one
      have hmono :
          P.real (highTopPairEvent Hshift K a t αbad q m n) ≤
            P.real (badPairEvent Hshift t αbad q m n) := by
        exact measureReal_mono (μ := P) (by
          intro ω hω
          exact hω.2.2)
      have hD_le_w : (D.card : ℝ) ≤ w ^ r := by
        have hcard :
            D.card = (3 ^ d) ^ (m - n) := by
          simpa [D] using
            descendantsAtScale_originCube_nat_shift_card
              (d := d) (N := N0) (m := m) (n := n) hnm_le
        have hgap_le : m - n ≤ r := by
          dsimp [m, n]
          omega
        have hpow_le_nat : (3 ^ d) ^ (m - n) ≤ (3 ^ d) ^ r :=
          Nat.pow_le_pow_right
            (by exact pow_pos (by norm_num : (0 : ℕ) < 3) d) hgap_le
        dsimp [w]
        rw [hcard]
        exact_mod_cast hpow_le_nat
      have hlam_nonneg : 0 ≤ lam := by
        exact (by positivity : 0 ≤ A * ρ ^ r).trans hlam_lower
      have hexp_le :
          Real.exp (-(lam ^ τ)) ≤
            Real.exp (-((A * ρ ^ r) ^ τ)) :=
        exp_neg_rpow_le_exp_neg_rpow_of_le
          (by positivity : 0 ≤ A * ρ ^ r) hlam_lower hτ_pos
      have htail :
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ τ))) ≤
            (S.card : ℝ) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
        have hDexp :
            (D.card : ℝ) * Real.exp (-(lam ^ τ)) ≤
              w ^ r * Real.exp (-((A * ρ ^ r) ^ τ)) :=
          mul_le_mul hD_le_w hexp_le (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hDexp hS_nonneg
      exact hmono.trans (hbad.trans htail)
    · have hempty :
          highTopPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highTopPairEvent, badPairEvent, hnm]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact htail_nonneg
  · have hempty :
        highTopPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highTopPairEvent, hhigh]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact htail_nonneg

/-- Sharp high-top bad-scale component estimate with the finite descendant
cardinality absorbed by the weighted linear kernel. -/
theorem measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
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
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let τ : ℝ := min σ 2
        let A : ℝ :=
          (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
          (S.card : ℝ) *
            (Real.exp (-(A ^ τ)) * weightedLinearExpKernelConst w (ρ ^ τ)) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  exact
    ⟨Cfluct, Centry, a, hCfluct, hCentry, ha,
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hpair⟩

end

end Section57
end Ch05
end Book
end Homogenization
