/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.MinimalScaleTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedLocalizedEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomTail

/-! # Localized Unit Ellipticity Minimal -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Minimal-scale envelope for localized unit ellipticity

This file packages the deterministic stopping-scale logic for the localized
unit-ellipticity supremum.  The stochastic tail estimate for the stopping
scale is added after this deterministic layer.
-/

noncomputable section

/-- The clean collapsed square envelope at scale `m`, based at integer scale
`N`. -/
noncomputable def unitEllipticityEnvelopeThreshold
    (t α : ℝ) (m N : ℕ) : ℝ :=
  (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
    Real.sqrt (((3 : ℝ) ^ m / (3 : ℝ) ^ N) ^ (-α))) ^ (2 : ℕ)

theorem unitEllipticityEnvelopeThreshold_eq_shift
    {t α : ℝ} {N r : ℕ} :
    unitEllipticityEnvelopeThreshold t α (N + r) N =
      Real.rpow (3 : ℝ)
        (2 * t * (N : ℝ) + (2 * t - α) * (r : ℝ)) := by
  let A : ℝ := Real.rpow (3 : ℝ) (t * ((N + r : ℕ) : ℝ))
  let B : ℝ := (((3 : ℝ) ^ (N + r) / (3 : ℝ) ^ N) ^ (-α))
  have hratio :
      (3 : ℝ) ^ (N + r) / (3 : ℝ) ^ N = (3 : ℝ) ^ r := by
    rw [pow_add]
    field_simp [pow_ne_zero N (by norm_num : (3 : ℝ) ≠ 0)]
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hA_sq :
      A ^ (2 : ℕ) =
        Real.rpow (3 : ℝ) (2 * t * ((N + r : ℕ) : ℝ)) := by
    dsimp [A]
    let x : ℝ := t * ((N + r : ℕ) : ℝ)
    have hpow₀ :
        Real.rpow (3 : ℝ) (x * (2 : ℝ)) =
          Real.rpow (Real.rpow (3 : ℝ) x) (2 : ℝ) := by
      exact Real.rpow_mul (x := (3 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 3) x (2 : ℝ)
    have hpow :
        Real.rpow (3 : ℝ) (x * (2 : ℝ)) =
          Real.rpow (3 : ℝ) x ^ (2 : ℕ) := by
      simpa [Real.rpow_two] using hpow₀
    calc
      Real.rpow (3 : ℝ) (t * ((N + r : ℕ) : ℝ)) ^ (2 : ℕ)
          = Real.rpow (3 : ℝ) (x * (2 : ℝ)) := by
            simpa [x] using hpow.symm
      _ = Real.rpow (3 : ℝ) (2 * t * ((N + r : ℕ) : ℝ)) := by
            congr 1
            ring
  have hB_eq :
      B = Real.rpow (3 : ℝ) (-α * (r : ℝ)) := by
    dsimp [B]
    rw [hratio]
    rw [← Real.rpow_natCast (3 : ℝ) r]
    calc
      Real.rpow (Real.rpow (3 : ℝ) (r : ℝ)) (-α)
          = Real.rpow (3 : ℝ) ((r : ℝ) * (-α)) := by
            exact (Real.rpow_mul (x := (3 : ℝ))
              (by norm_num : (0 : ℝ) ≤ 3) (r : ℝ) (-α)).symm
      _ = Real.rpow (3 : ℝ) (-α * (r : ℝ)) := by
            congr 1
            ring
  calc
    unitEllipticityEnvelopeThreshold t α (N + r) N
        = (A * Real.sqrt B) ^ (2 : ℕ) := by
            simp [unitEllipticityEnvelopeThreshold, A, B]
    _ = A ^ (2 : ℕ) * B := by
            rw [mul_pow, Real.sq_sqrt hB_nonneg]
    _ =
        Real.rpow (3 : ℝ) (2 * t * ((N + r : ℕ) : ℝ)) *
          Real.rpow (3 : ℝ) (-α * (r : ℝ)) := by
            rw [hA_sq, hB_eq]
    _ = Real.rpow (3 : ℝ)
        (2 * t * (N : ℝ) + (2 * t - α) * (r : ℝ)) := by
            have hcombine :
                Real.rpow (3 : ℝ) (2 * t * ((N + r : ℕ) : ℝ)) *
                    Real.rpow (3 : ℝ) (-α * (r : ℝ)) =
                  Real.rpow (3 : ℝ)
                    (2 * t * ((N + r : ℕ) : ℝ) + -α * (r : ℝ)) := by
              exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                (2 * t * ((N + r : ℕ) : ℝ)) (-α * (r : ℝ))).symm
            rw [hcombine]
            congr 1
            norm_num [Nat.cast_add]
            ring

theorem unitEllipticity_tail_parameter_le_threshold_div
    {t α scale : ℝ} {N r : ℕ} :
    ((3 : ℝ) ^ (2 * t * (N : ℝ)) / scale) *
        ((3 : ℝ) ^ (2 * t - α)) ^ r ≤
      unitEllipticityEnvelopeThreshold t α (N + r) N / scale := by
  have hρpow :
      ((3 : ℝ) ^ (2 * t - α)) ^ r =
        Real.rpow (3 : ℝ) ((2 * t - α) * (r : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (x := (3 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 3) (2 * t - α) (r : ℝ)).symm
  rw [unitEllipticityEnvelopeThreshold_eq_shift (t := t) (α := α) (N := N) (r := r)]
  rw [hρpow]
  have hprod :
      (3 : ℝ) ^ (2 * t * (N : ℝ)) *
          Real.rpow (3 : ℝ) ((2 * t - α) * (r : ℝ)) =
        Real.rpow (3 : ℝ)
          (2 * t * (N : ℝ) + (2 * t - α) * (r : ℝ)) := by
    exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
      (2 * t * (N : ℝ)) ((2 * t - α) * (r : ℝ))).symm
  calc
    ((3 : ℝ) ^ (2 * t * (N : ℝ)) / scale) *
        Real.rpow (3 : ℝ) ((2 * t - α) * (r : ℝ))
        =
      ((3 : ℝ) ^ (2 * t * (N : ℝ)) *
        Real.rpow (3 : ℝ) ((2 * t - α) * (r : ℝ))) / scale := by
          ring
    _ =
      Real.rpow (3 : ℝ)
        (2 * t * (N : ℝ) + (2 * t - α) * (r : ℝ)) / scale := by
          rw [hprod]
    _ ≤
      Real.rpow (3 : ℝ)
        (2 * t * (N : ℝ) + (2 * t - α) * (r : ℝ)) / scale := le_rfl

/-- Bad scale for the localized limiting-normalized unit ellipticity supremum:
above the base scale `N`, the supremum exceeds the collapsed envelope. -/
def unitEllipticityBadScaleEvent
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (t α : ℝ) (N : ℕ) : Set (RegCoeffField d) :=
  {a | ∃ m : ℕ, N ≤ m ∧
    unitEllipticityEnvelopeThreshold t α m N <
      localizedLimitWeightedUnitEllipticitySup hP hStruct params m a}

theorem unitEllipticityBadScaleEvent_antitone
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {t α : ℝ} (hα : 0 ≤ α) {N K : ℕ} (hNK : N ≤ K) :
    unitEllipticityBadScaleEvent hP hStruct params t α K ⊆
      unitEllipticityBadScaleEvent hP hStruct params t α N := by
  intro a hbad
  rcases hbad with ⟨m, hKm, hbad⟩
  refine ⟨m, hNK.trans hKm, ?_⟩
  let rK : ℕ := m - K
  let rN : ℕ := m - N
  have hmK : K + rK = m := by
    dsimp [rK]
    exact Nat.add_sub_of_le hKm
  have hmN : N + rN = m := by
    dsimp [rN]
    exact Nat.add_sub_of_le (hNK.trans hKm)
  have hsub_le : rK ≤ rN := by
    dsimp [rK, rN]
    exact Nat.sub_le_sub_left hNK m
  have hcast_le : (rK : ℝ) ≤ (rN : ℝ) := by exact_mod_cast hsub_le
  have hpow_le :
      ((3 : ℝ) ^ (rN : ℝ)) ^ (-α) ≤
        ((3 : ℝ) ^ (rK : ℝ)) ^ (-α) := by
    have hbaseK_pos : 0 < (3 : ℝ) ^ (rK : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hbaseN_pos : 0 < (3 : ℝ) ^ (rN : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hbase_le :
        (3 : ℝ) ^ (rK : ℝ) ≤ (3 : ℝ) ^ (rN : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hcast_le
    by_cases hα_zero : α = 0
    · simp [hα_zero]
    · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα_zero)
      exact
        (Real.rpow_le_rpow_iff_of_neg hbaseN_pos hbaseK_pos
          (by linarith : (-α : ℝ) < 0)).2 hbase_le
  have hthreshold_le :
      unitEllipticityEnvelopeThreshold t α m N ≤
        unitEllipticityEnvelopeThreshold t α m K := by
    have hleft :
        unitEllipticityEnvelopeThreshold t α m N =
          unitEllipticityEnvelopeThreshold t α (N + rN) N := by
      rw [hmN]
    have hright :
        unitEllipticityEnvelopeThreshold t α m K =
          unitEllipticityEnvelopeThreshold t α (K + rK) K := by
      rw [hmK]
    rw [hleft, hright]
    simp only [unitEllipticityEnvelopeThreshold]
    have hA_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (t * ((N + rN : ℕ) : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hB_nonneg :
        0 ≤ Real.sqrt (((3 : ℝ) ^ (N + rN) / (3 : ℝ) ^ N) ^ (-α)) := by
      positivity
    have hAK_eq :
        Real.rpow (3 : ℝ) (t * ((N + rN : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (t * ((K + rK : ℕ) : ℝ)) := by
      rw [hmN, hmK]
    have hratioN :
        (3 : ℝ) ^ (N + rN) / (3 : ℝ) ^ N = (3 : ℝ) ^ rN := by
      rw [pow_add]
      field_simp [pow_ne_zero N (by norm_num : (3 : ℝ) ≠ 0)]
    have hratioK :
        (3 : ℝ) ^ (K + rK) / (3 : ℝ) ^ K = (3 : ℝ) ^ rK := by
      rw [pow_add]
      field_simp [pow_ne_zero K (by norm_num : (3 : ℝ) ≠ 0)]
    have hsqrt_le :
        Real.sqrt (((3 : ℝ) ^ (N + rN) / (3 : ℝ) ^ N) ^ (-α)) ≤
          Real.sqrt (((3 : ℝ) ^ (K + rK) / (3 : ℝ) ^ K) ^ (-α)) := by
      rw [hratioN, hratioK]
      exact Real.sqrt_le_sqrt (by simpa [Real.rpow_natCast] using hpow_le)
    have hmul_le :
        Real.rpow (3 : ℝ) (t * ((N + rN : ℕ) : ℝ)) *
            Real.sqrt (((3 : ℝ) ^ (N + rN) / (3 : ℝ) ^ N) ^ (-α)) ≤
          Real.rpow (3 : ℝ) (t * ((K + rK : ℕ) : ℝ)) *
            Real.sqrt (((3 : ℝ) ^ (K + rK) / (3 : ℝ) ^ K) ^ (-α)) := by
      rw [hAK_eq]
      exact mul_le_mul_of_nonneg_left hsqrt_le
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    exact pow_le_pow_left₀ (mul_nonneg hA_nonneg hB_nonneg) hmul_le 2
  exact lt_of_le_of_lt hthreshold_le hbad

theorem badTailEvent_unitEllipticityBadScaleEvent_subset
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {t α : ℝ} (hα : 0 ≤ α) {N : ℕ} :
    badTailEvent (unitEllipticityBadScaleEvent hP hStruct params t α) N ⊆
      unitEllipticityBadScaleEvent hP hStruct params t α N := by
  intro a htail
  rcases htail with ⟨K, hNK, hK⟩
  exact unitEllipticityBadScaleEvent_antitone
    hP hStruct params hα hNK hK

theorem unitEllipticityBadScaleEvent_subset_rows
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {t α : ℝ} {N : ℕ} :
    unitEllipticityBadScaleEvent hP hStruct params t α N ⊆
      ⋃ r : ℕ,
        {a : RegCoeffField d |
          unitEllipticityEnvelopeThreshold t α (N + r) N <
            localizedLimitWeightedUnitEllipticitySup hP hStruct params (N + r) a} := by
  intro a hbad
  rcases hbad with ⟨m, hNm, hbad⟩
  let r : ℕ := m - N
  refine Set.mem_iUnion.2 ⟨r, ?_⟩
  have hm : N + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hNm
  simpa [hm]
    using hbad

theorem measureReal_unitEllipticityBadScaleRow_le_weighted
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α : ℝ} {N r : ℕ} :
    let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let A : ℝ := (3 : ℝ) ^ (2 * t * (N : ℝ)) / scale
    let ρ : ℝ := (3 : ℝ) ^ (2 * t - α)
    0 < t →
    α < t →
    1 ≤ A →
    P.real
        {a : RegCoeffField d |
          unitEllipticityEnvelopeThreshold t α (N + r) N <
            localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a} ≤
      w ^ N * (w ^ r * Real.exp (-((A * ρ ^ r) ^ hΓ.sigma))) := by
  classical
  intro scale w A ρ ht hαt hA_one
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (((N + r : ℕ) : ℤ))
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let lam : ℝ := unitEllipticityEnvelopeThreshold t α (N + r) N / scale
  have hθ_one : 1 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hθ_one) hΓ.thetaHat_pos
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_one
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < 2 * t - α := by linarith
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (2 * t - α) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by norm_num : (1 : ℝ) < 3) hgap
  have hAρ_nonneg : 0 ≤ A * ρ ^ r := by positivity
  have hlam_lower : A * ρ ^ r ≤ lam := by
    simpa [A, ρ, lam, scale] using
      unitEllipticity_tail_parameter_le_threshold_div
        (t := t) (α := α) (scale := scale) (N := N) (r := r)
  have hlam_one : 1 ≤ lam := by
    have hρ_pow_one : 1 ≤ ρ ^ r := one_le_pow₀ hρ_gt.le
    have hA_le_Aρ : A ≤ A * ρ ^ r := by
      calc
        A = A * 1 := by ring
        _ ≤ A * ρ ^ r :=
          mul_le_mul_of_nonneg_left hρ_pow_one hA_pos.le
    exact hA_one.trans (hA_le_Aρ.trans hlam_lower)
  have hcard :
      D.card = (3 ^ d) ^ (N + r) := by
    simpa [Q, D] using
      descendantsAtScale_originCube_nat_card
        (d := d) (m := N + r) (n := 0) (Nat.zero_le _)
  have hmeasure :
      P.real
          {a : RegCoeffField d |
            scale * lam <
              localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a} ≤
        (D.card : ℝ) * Real.exp (-(lam ^ hΓ.sigma)) := by
    simpa [Q, D, scale, lam] using
      measureReal_localizedLimitWeightedUnitEllipticitySup_tail_le_card_mul_exp
        hP hStruct hΓ (N + r) hlam_one
  have hrow_subset :
      {a : RegCoeffField d |
          unitEllipticityEnvelopeThreshold t α (N + r) N <
            localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a} ⊆
        {a : RegCoeffField d |
          scale * lam <
            localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a} := by
    intro a ha
    have hscale_lam :
        scale * lam = unitEllipticityEnvelopeThreshold t α (N + r) N := by
      dsimp [lam]
      field_simp [hscale_pos.ne']
    simpa [hscale_lam] using ha
  have hrow_measure :
      P.real
          {a : RegCoeffField d |
            unitEllipticityEnvelopeThreshold t α (N + r) N <
              localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a} ≤
        (D.card : ℝ) * Real.exp (-(lam ^ hΓ.sigma)) :=
    (measureReal_mono (μ := P) hrow_subset).trans hmeasure
  have hD_weight : (D.card : ℝ) ≤ w ^ N * w ^ r := by
    have hw_eq : w = ((3 ^ d : ℕ) : ℝ) := rfl
    have hD_eq : (D.card : ℝ) = w ^ N * w ^ r := by
      calc
        (D.card : ℝ) = w ^ (N + r) := by
            rw [hcard]
            norm_num [w]
        _ = w ^ N * w ^ r := by
            rw [pow_add]
    exact le_of_eq hD_eq
  have hexp :
      Real.exp (-(lam ^ hΓ.sigma)) ≤
        Real.exp (-((A * ρ ^ r) ^ hΓ.sigma)) := by
    have hpow : (A * ρ ^ r) ^ hΓ.sigma ≤ lam ^ hΓ.sigma :=
      Real.rpow_le_rpow hAρ_nonneg hlam_lower hΓ.sigma_pos.le
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    P.real
        {a : RegCoeffField d |
          unitEllipticityEnvelopeThreshold t α (N + r) N <
            localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a}
        ≤ (D.card : ℝ) * Real.exp (-(lam ^ hΓ.sigma)) := hrow_measure
    _ ≤ (w ^ N * w ^ r) *
        Real.exp (-((A * ρ ^ r) ^ hΓ.sigma)) :=
          mul_le_mul hD_weight hexp (by positivity) (by positivity)
    _ = w ^ N * (w ^ r * Real.exp (-((A * ρ ^ r) ^ hΓ.sigma))) := by
          ring

theorem measureReal_unitEllipticityBadScaleEvent_le_weighted_kernel
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α : ℝ} {N : ℕ} :
    let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let A : ℝ := (3 : ℝ) ^ (2 * t * (N : ℝ)) / scale
    let ρ : ℝ := (3 : ℝ) ^ (2 * t - α)
    0 < t →
    α < t →
    1 ≤ A →
    P.real (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α N) ≤
      w ^ N *
        (Real.exp (-(A ^ hΓ.sigma)) *
          weightedGeometricExpKernelConst w (ρ ^ hΓ.sigma)) := by
  classical
  intro scale w A ρ ht hαt hA_one
  let : IsProbabilityMeasure P := hP.isProbability
  let E : ℕ → Fin 1 → Set (RegCoeffField d) :=
    fun r _ =>
      {a : RegCoeffField d |
        unitEllipticityEnvelopeThreshold t α (N + r) N <
          localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params (N + r) a}
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hC_nonneg : 0 ≤ w ^ N := pow_nonneg hw_pos.le N
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < 2 * t - α := by linarith
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (2 * t - α) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by norm_num : (1 : ℝ) < 3) hgap
  have hsubset :
      unitEllipticityBadScaleEvent hP hStruct hΓ.params t α N ⊆
        ⋃ r : ℕ, ⋃ j : Fin 1, E r j := by
    intro a ha
    have hrows :=
      unitEllipticityBadScaleEvent_subset_rows
        hP hStruct hΓ.params (t := t) (α := α) (N := N) ha
    rcases Set.mem_iUnion.1 hrows with ⟨r, hr⟩
    exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨0, by simpa [E] using hr⟩⟩
  calc
    P.real (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α N)
        ≤ P.real (⋃ r : ℕ, ⋃ j : Fin 1, E r j) :=
          measureReal_mono (μ := P) hsubset
    _ ≤ ((1 : ℕ) : ℝ) * w ^ N *
        (Real.exp (-(A ^ hΓ.sigma)) *
          weightedGeometricExpKernelConst w (ρ ^ hΓ.sigma)) :=
          measureReal_iUnion_constRows_le_weighted_exp_kernel
            (μ := P) (Q := 1) (E := E)
            hC_nonneg hw_pos hA_one hρ_gt hΓ.sigma_pos
            (by
              intro r j
              simpa [E, scale, w, A, ρ] using
                measureReal_unitEllipticityBadScaleRow_le_weighted
                  hP hStruct hΓ (t := t) (α := α) (N := N) (r := r)
                  ht hαt hA_one)
    _ =
      w ^ N *
        (Real.exp (-(A ^ hΓ.sigma)) *
          weightedGeometricExpKernelConst w (ρ ^ hΓ.sigma)) := by
          ring

theorem measureReal_badTailEvent_unitEllipticityBadScaleEvent_le_weighted_kernel
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α : ℝ} {N : ℕ} :
    let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let A : ℝ := (3 : ℝ) ^ (2 * t * (N : ℝ)) / scale
    let ρ : ℝ := (3 : ℝ) ^ (2 * t - α)
    0 < t →
    0 ≤ α →
    α < t →
    1 ≤ A →
    P.real
        (badTailEvent
          (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) N) ≤
      w ^ N *
        (Real.exp (-(A ^ hΓ.sigma)) *
          weightedGeometricExpKernelConst w (ρ ^ hΓ.sigma)) := by
  intro scale w A ρ ht hα hαt hA_one
  let : IsProbabilityMeasure P := hP.isProbability
  have hmono :
      P.real
          (badTailEvent
            (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) N) ≤
        P.real (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α N) :=
    measureReal_mono (μ := P)
      (badTailEvent_unitEllipticityBadScaleEvent_subset
        hP hStruct hΓ.params (t := t) (α := α) hα)
  exact hmono.trans
    (by
      simpa [scale, w, A, ρ] using
        measureReal_unitEllipticityBadScaleEvent_le_weighted_kernel
          hP hStruct hΓ (t := t) (α := α) (N := N)
          ht hαt hA_one)

theorem exists_quantitative_threshold_unitEllipticityBadTail_le_interpolated_tail
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ_pos : 0 < σ) :
    ∀ {t α : ℝ},
      let η : ℝ := finiteQuenchedTailExponent d σ t
      let w : ℝ := ((3 ^ d : ℕ) : ℝ)
      let W : ℝ := max 1 w
      let ρunit : ℝ := (3 : ℝ) ^ (2 * t - α)
      let Kunit : ℝ := weightedGeometricExpKernelConst w (ρunit ^ σ)
      let M : ℝ := max 1 (max 0 Kunit)
      let ρgap : ℝ := (3 : ℝ) ^ η
      let C₀ : ℝ := 2 + Real.log W
      0 < t →
      0 ≤ α →
      α < t →
      ∃ R : ℕ,
        (∀ q : ℕ, R ≤ q →
          C₀ * (q : ℝ) ≤
            Real.exp ((Real.log ρgap / 2) * (q : ℝ))) ∧
        ∀ {P : Ch04.RestrictionCoeffLaw d}
          (hP : Ch04.RestrictionLawCarrier P)
          (hStruct : Ch04.RestrictionStructuralLaw P)
          (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
          hΓ.sigma = σ →
          let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
          let Blead : ℝ := smallBottomTailDenominator scale η σ
          let Btail : ℝ := 2 * Blead
          let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
          let Qpref : ℕ :=
            max (Nat.ceil (max 0 (Real.log M)))
              (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
                Real.log ρgap)))
          let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
          let Q : ℕ := max Qpref Qlead
          ∀ q : ℕ, Q ≤ q →
            P.real
              (badTailEvent
                (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α)
                q) ≤
              Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  intro t α
  dsimp only
  intro ht hα_nonneg hαt
  classical
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let W : ℝ := max 1 w
  let ρunit : ℝ := (3 : ℝ) ^ (2 * t - α)
  let Kunit : ℝ := weightedGeometricExpKernelConst w (ρunit ^ σ)
  let M : ℝ := max 1 (max 0 Kunit)
  let ρgap : ℝ := (3 : ℝ) ^ η
  let C₀ : ℝ := 2 + Real.log W
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hρgap_gt : 1 < ρgap := by
    dsimp [ρgap]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη_pos
  have hW_one : 1 ≤ W := by
    dsimp [W]
    exact le_max_left 1 w
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hlogW_nonneg : 0 ≤ Real.log W := Real.log_nonneg hW_one
    dsimp [C₀]
    linarith
  obtain ⟨R, hR⟩ :=
    linear_le_exp_linear_eventually
      (C := C₀) (γ := Real.log ρgap / 2)
      hC₀_nonneg (by
        have hlogρ_pos : 0 < Real.log ρgap := Real.log_pos hρgap_gt
        positivity)
  refine ⟨R, ?_, ?_⟩
  · simpa [η, w, W, ρunit, Kunit, M, ρgap, C₀] using hR
  intro P hP hStruct hΓ hσ_eq
  let : IsProbabilityMeasure P := hP.isProbability
  let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
  let Blead : ℝ := smallBottomTailDenominator scale η σ
  let Btail : ℝ := 2 * Blead
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
        Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Q : ℕ := max Qpref Qlead
  intro q hQq
  have hθ_one : 1 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hθ_one) hΓ.thetaHat_pos
  have hBlead_pos : 0 < Blead := by
    simpa [Blead] using
      smallBottomTailDenominator_pos
        (scale := scale) (η := η) (σ := σ)
  have hBtail_pos : 0 < Btail := by
    dsimp [Btail]
    positivity
  have hBlead_lt_Btail : Blead < Btail := by
    dsimp [Btail]
    nlinarith
  have hρunit_gt : 1 < ρunit := by
    have hgap : 0 < 2 * t - α := by linarith
    dsimp [ρunit]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (2 * t - α) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hKunit_pos : 0 < Kunit := by
    dsimp [Kunit]
    exact weightedGeometricExpKernelConst_pos
      (w := w) (R := ρunit ^ σ) hw_pos
      (Real.one_lt_rpow hρunit_gt hσ_pos)
  have hM_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left 1 _
  have hq_pref : Qpref ≤ q := (le_max_left Qpref Qlead).trans hQq
  have hq_lead : Qlead ≤ q := (le_max_right Qpref Qlead).trans hQq
  have hqM :
      Nat.ceil (max 0 (Real.log M)) ≤ q :=
    (le_max_left _ _).trans hq_pref
  have hqR : R ≤ q :=
    (le_max_left R
        (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_pref)
  have hqc :
      Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap) ≤ q :=
    (le_max_right R
        (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_pref)
  have hlead_one : 1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead := by
    simpa [Blead] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := (1 : ℝ)) (O := (0 : ℝ)) (D := Blead) (q := q)
        (by norm_num) hBlead_pos
        (by simpa [Qlead] using hq_lead)
  have hη_le_t : η ≤ σ * t := by
    have hb_pos : 0 < (d : ℝ) / 2 := by
      have hd : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      positivity
    simpa [η, finiteQuenchedTailExponent] using
      interpolatedQuenchedTailExponent_le_sigma_mul_t
        (b := (d : ℝ) / 2) (σ := σ) (t := t)
        hb_pos hσ_pos ht
  have hη_le : η ≤ σ * (2 * t) := by
    have hσt_nonneg : 0 ≤ σ * t := mul_nonneg hσ_pos.le ht.le
    nlinarith
  let Aold : ℝ := (3 : ℝ) ^ (2 * t * (q : ℝ)) / scale
  let Alead : ℝ := ((3 : ℝ) ^ (q : ℝ) / Blead) ^ η
  let Atail : ℝ := ((3 : ℝ) ^ (q : ℝ) / Btail) ^ η
  have hAlead_to_old : Alead ≤ Aold ^ σ := by
    simpa [Aold, Alead, Blead] using
      smallBottomTailDenominator_rpow_le_crude_scale
        (scale := scale) (η := η) (σ := σ) (t := 2 * t) (q := q)
        hscale_pos hη_pos hσ_pos hη_le
  have hAold_nonneg : 0 ≤ Aold := by
    dsimp [Aold]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      hscale_pos.le
  have hAold_one : 1 ≤ Aold := by
    have hAlead_one : 1 ≤ Alead := by
      dsimp [Alead]
      exact Real.one_le_rpow hlead_one hη_pos.le
    exact one_le_of_one_le_rpow hAold_nonneg hσ_pos
      (hAlead_one.trans hAlead_to_old)
  have hkernel_q :
      P.real
          (badTailEvent
            (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) q) ≤
        w ^ q * (Real.exp (-(Aold ^ σ)) * Kunit) := by
    simpa [scale, w, Aold, ρunit, Kunit, hσ_eq] using
      measureReal_badTailEvent_unitEllipticityBadScaleEvent_le_weighted_kernel
        hP hStruct hΓ (t := t) (α := α) (N := q)
        ht hα_nonneg hαt hAold_one
  have hprefix_le :
      Kunit * w ^ q ≤ M * (((q : ℝ) + 1) * W ^ q) := by
    have hK_le_M : Kunit ≤ M := by
      calc
        Kunit ≤ max 0 Kunit := le_max_right 0 Kunit
        _ ≤ M := by
          dsimp [M]
          exact le_max_right 1 _
    have hwW : w ≤ W := by
      dsimp [W]
      exact le_max_right 1 w
    have hwq_le : w ^ q ≤ W ^ q :=
      pow_le_pow_left₀ hw_pos.le hwW q
    have hWq_nonneg : 0 ≤ W ^ q := by positivity
    have hleft :
        Kunit * w ^ q ≤ M * W ^ q :=
      mul_le_mul hK_le_M hwq_le
        (pow_nonneg hw_pos.le q) (zero_le_one.trans hM_one)
    have hqplus_one : 1 ≤ (q : ℝ) + 1 := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      linarith
    have hright :
        M * W ^ q ≤ M * (((q : ℝ) + 1) * W ^ q) := by
      have hfactor : W ^ q ≤ ((q : ℝ) + 1) * W ^ q := by
        calc
          W ^ q = 1 * W ^ q := by ring
          _ ≤ ((q : ℝ) + 1) * W ^ q :=
            mul_le_mul_of_nonneg_right hqplus_one hWq_nonneg
      exact mul_le_mul_of_nonneg_left hfactor (zero_le_one.trans hM_one)
    exact hleft.trans hright
  have hc_pos : 0 < cgap := by
    simpa [cgap, Btail] using
      inv_rpow_sub_pos_of_lt hBlead_pos hBtail_pos hη_pos hBlead_lt_Btail
  have hpref_gap :
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (Alead - Atail) := by
    have hpref_exp :
        M * (((q : ℝ) + 1) * W ^ q) ≤
          Real.exp (cgap * ρgap ^ q) :=
      linear_prefactor_le_exp_const_mul_pow_of_large
        (M := M) (W := W) (C₀ := C₀) (c := cgap)
        (ρ := ρgap) (R := R) (q := q)
        hM_one hW_one hc_pos hρgap_gt
        (le_rfl : 2 + Real.log W ≤ C₀) hR hqM hqR hqc
    have hgap :
        cgap * ρgap ^ q ≤ Alead - Atail := by
      simpa [Alead, Atail, cgap, ρgap] using
        geometric_gap_le_rpow_three_nat_div_gap
          (Blead := Blead) (Btail := Btail) (η := η)
          (c := cgap) (ρ := ρgap) (q := q)
          hBlead_pos hBtail_pos
          (le_rfl : cgap ≤ Blead ^ (-η) - Btail ^ (-η))
          (le_rfl : ρgap ≤ (3 : ℝ) ^ η) hc_pos.le
          (le_of_lt (lt_trans zero_lt_one hρgap_gt))
    exact hpref_exp.trans (Real.exp_le_exp.mpr hgap)
  have hexp_old :
      Real.exp (-(Aold ^ σ)) ≤ Real.exp (-Alead) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmeasure_tail :
      P.real
          (badTailEvent
            (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) q) ≤
        M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) := by
    calc
      P.real
          (badTailEvent
            (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) q)
          ≤ w ^ q * (Real.exp (-(Aold ^ σ)) * Kunit) := hkernel_q
      _ = Kunit * w ^ q * Real.exp (-(Aold ^ σ)) := by ring
      _ ≤ Kunit * w ^ q * Real.exp (-Alead) :=
            mul_le_mul_of_nonneg_left hexp_old
              (by positivity : 0 ≤ Kunit * w ^ q)
      _ ≤ M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) :=
            mul_le_mul_of_nonneg_right hprefix_le (Real.exp_pos _).le
  calc
    P.real
        (badTailEvent
          (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α) q)
        ≤ M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) :=
          hmeasure_tail
    _ ≤ Real.exp (Alead - Atail) * Real.exp (-Alead) :=
          mul_le_mul_of_nonneg_right hpref_gap (Real.exp_pos _).le
    _ = Real.exp (-Atail) := by
          rw [← Real.exp_add]
          ring_nf

theorem localizedLimitWeightedUnitEllipticitySup_le_of_not_mem_unitEllipticityBadScaleEvent
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {t α : ℝ} {N m : ℕ} {a : RegCoeffField d}
    (hnot : a ∉ unitEllipticityBadScaleEvent hP hStruct params t α N)
    (hNm : N ≤ m) :
    localizedLimitWeightedUnitEllipticitySup hP hStruct params m a ≤
      unitEllipticityEnvelopeThreshold t α m N := by
  exact le_of_not_gt fun hbad => hnot ⟨m, hNm, hbad⟩

/-- Above the constructed stopping scale, absence of unit-ellipticity bad
scales gives exactly the collapsed envelope with the random scale `X`. -/
theorem localizedLimitWeightedUnitEllipticitySup_le_above_quenchedMinimalScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {N0 m : ℕ} {t α : ℝ} {a : RegCoeffField d}
    (hgood :
      hasGoodTailFrom N0
        (unitEllipticityBadScaleEvent hP hStruct params t α) a)
    (hscale :
      quenchedMinimalScale N0
          (unitEllipticityBadScaleEvent hP hStruct params t α) a ≤
        (3 : ℝ) ^ m) :
    localizedLimitWeightedUnitEllipticitySup hP hStruct params m a ≤
      (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
        Real.sqrt
          (((3 : ℝ) ^ m /
            quenchedMinimalScale N0
              (unitEllipticityBadScaleEvent hP hStruct params t α) a) ^
            (-α))) ^ (2 : ℕ) := by
  let Bad : ℕ → Set (RegCoeffField d) :=
    unitEllipticityBadScaleEvent hP hStruct params t α
  let L : ℕ := quenchedMinimalScaleIndex N0 Bad a
  have hLm : L ≤ m := by
    simpa [L, Bad] using
      quenchedMinimalScaleIndex_le_of_scale_le_pow
        (N0 := N0) (Bad := Bad) (ω := a) hscale
  have hnot : a ∉ Bad L := by
    exact not_mem_bad_of_quenchedMinimalScaleIndex_le
      (N0 := N0) (Bad := Bad) (ω := a)
      hgood (N := L) (K := L) le_rfl le_rfl
  have hraw :=
    localizedLimitWeightedUnitEllipticitySup_le_of_not_mem_unitEllipticityBadScaleEvent
      hP hStruct params (t := t) (α := α) (N := L) (m := m)
      (a := a) (by simpa [Bad] using hnot) hLm
  simpa [unitEllipticityEnvelopeThreshold, quenchedMinimalScale, Bad, L]
    using hraw

theorem exists_unitEllipticityMinimalScale_interpolated
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ_pos : 0 < σ)
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (hσ_eq : hΓ.sigma = σ)
    {t α : ℝ} :
    let η : ℝ := finiteQuenchedTailExponent d σ t
    0 < t →
    0 ≤ α →
    α < t →
    ∃ X : RegCoeffField d → ℝ, ∃ C : ℝ, 0 < C ∧
      IsBigO P (gammaSigma η) X C ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ᵐ aω ∂P,
          ∀ {m : ℕ},
            X aω ≤ (3 : ℝ) ^ m →
            localizedLimitWeightedUnitEllipticitySup
                hP hStruct hΓ.params m aω ≤
              (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
                Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))) ^ (2 : ℕ) := by
  intro η ht hα_nonneg hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let W : ℝ := max 1 w
  let ρunit : ℝ := (3 : ℝ) ^ (2 * t - α)
  let Kunit : ℝ := weightedGeometricExpKernelConst w (ρunit ^ σ)
  let M : ℝ := max 1 (max 0 Kunit)
  let ρgap : ℝ := (3 : ℝ) ^ η
  let C₀ : ℝ := 2 + Real.log W
  obtain ⟨R, _hR, htail_abs⟩ :=
    exists_quantitative_threshold_unitEllipticityBadTail_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos
      (t := t) (α := α) ht hα_nonneg hαt
  let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
  let Blead : ℝ := smallBottomTailDenominator scale η σ
  let Btail : ℝ := 2 * Blead
  let B : ℝ := max 1 Btail
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
        Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Q : ℕ := max Qpref Qlead
  let Bad : ℕ → Set (RegCoeffField d) :=
    unitEllipticityBadScaleEvent hP hStruct hΓ.params t α
  let X : RegCoeffField d → ℝ := quenchedMinimalScale Q Bad
  let C : ℝ := 3 * ((3 : ℝ) ^ Q) * B
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hθ_one : 1 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hθ_one) hΓ.thetaHat_pos
  have hBlead_pos : 0 < Blead := by
    simpa [Blead] using
      smallBottomTailDenominator_pos
        (scale := scale) (η := η) (σ := σ)
  have hBtail_pos : 0 < Btail := by
    dsimp [Btail]
    positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_max_left 1 Btail
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have htail :
      ∀ N : ℕ, Q ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hQN
    have hN_abs :
        P.real
            (badTailEvent
              (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α)
              N) ≤
          Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) := by
      simpa [η, w, W, ρunit, Kunit, M, ρgap, C₀,
        scale, Blead, Btail, cgap, Qpref, Qlead, Q] using
        htail_abs hP hStruct hΓ hσ_eq N hQN
    have hcompare :
        Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
      simpa [B] using
        exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
          (Q := Q) (N := N) (B := Btail) (η := η)
          hBtail_pos hη_pos
    exact hN_abs.trans hcompare
  have hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Q ≤ N ∧ P.real (badTailEvent Bad N) ≤ ε := by
    intro ε hε
    obtain ⟨j, hj⟩ :=
      exists_exp_neg_rpow_three_div_le
        (B := B) (η := η) (ε := ε) hB_pos hη_pos hε
    refine ⟨Q + j, Nat.le_add_right Q j, ?_⟩
    have htail_j := htail (Q + j) (Nat.le_add_right Q j)
    exact htail_j.trans (by simpa [Nat.add_sub_cancel_left] using hj)
  have hgoodAE : ∀ᵐ aω ∂P, hasGoodTailFrom Q Bad aω := by
    exact ae_hasGoodTailFrom
      (μ := P) (N0 := Q) (Bad := Bad) hsmall
  have hO :
      IsBigO P (gammaSigma η) X C := by
    simpa [X, C] using
      isBigO_quenchedMinimalScale_of_badTailEvent_bound
        (μ := P) (N0 := Q) (Bad := Bad) (B := B) (η := η)
        hη_pos hB htail
  have hXone : ∀ aω, 1 ≤ X aω := by
    intro aω
    simpa [X] using one_le_quenchedMinimalScale Q Bad aω
  have hpoint :
      ∀ᵐ aω ∂P,
        ∀ {m : ℕ},
          X aω ≤ (3 : ℝ) ^ m →
          localizedLimitWeightedUnitEllipticitySup
              hP hStruct hΓ.params m aω ≤
            (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
              Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))) ^ (2 : ℕ) := by
    filter_upwards [hgoodAE] with aω hgood
    intro m hm
    simpa [Bad, X] using
      localizedLimitWeightedUnitEllipticitySup_le_above_quenchedMinimalScale
        hP hStruct hΓ.params (N0 := Q) (m := m) (t := t) (α := α)
        (a := aω) hgood (by simpa [Bad, X] using hm)
  exact ⟨X, C, hC_pos, hO, hXone, hpoint⟩

end

end Section57
end Ch05
end Book
end Homogenization
