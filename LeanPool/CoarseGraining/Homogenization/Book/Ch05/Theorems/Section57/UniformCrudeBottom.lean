/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityEndpoint
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsCrudeBottom

/-! # Uniform Crude Bottom -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# The crude bottom-scale branch at the uniform endpoint

Under `Γ_∞`, the crude branch is deterministic: the localized normalized
probe maximum is almost surely bounded by a constant multiple of
`thetaHat^2`.  Consequently the corresponding bad-pair event is empty modulo
null sets once the crude threshold is at least this deterministic scale.
-/

noncomputable section

/-- Endpoint crude fixed bad-pair estimate.  The right side is exactly zero:
the endpoint replaces the finite-`σ` crude tail by deterministic boundedness. -/
theorem measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_eq_zero_of_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {N0 q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let scale : ℝ := K * (C * hInf.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) = 0 := by
  let C : ℝ := GammaInfinityCoarseGrainedEllipticity.unitJConst d params
  have hC_pos : 0 < C := by
    simpa [C] using
      GammaInfinityCoarseGrainedEllipticity.unitJConst_pos
        (d := d) params
  refine ⟨C, hC_pos, ?_⟩
  intro t αbad P hP hStruct hInf hparams N0 q m n
  dsimp only
  intro hnm hqm hlam
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let A : ℝ := C * hInf.thetaHat ^ (2 : ℕ)
  let scale : ℝ := K * A
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let lam : ℝ := T / scale
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hC_pos (pow_pos hInf.thetaHat_pos 2)
  have hA_nonneg : 0 ≤ A := hA_pos.le
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos hK_pos hA_pos
  have hA_le_A_lam : A ≤ A * lam := by
    calc
      A = A * 1 := by ring
      _ ≤ A * lam := mul_le_mul_of_nonneg_left hlam hA_nonneg
  have hmax_ae :
      localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n)
        ≤ᵐ[P] fun _ => A := by
    have hbound :=
      hInf.localizedNormalizedProbeJMax_le_thetaHat_sq_ae
        (m := N0 + m) (n := N0 + n)
        (Nat.add_le_add_left (le_of_lt hnm) N0)
    simpa [A, C, hparams] using hbound
  let tailSet : Set (RegCoeffField d) :=
    {aω | A * lam <
      localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω}
  have htail_empty_ae : tailSet =ᵐ[P] (∅ : Set (RegCoeffField d)) := by
    filter_upwards [hmax_ae] with aω hmax
    apply propext
    change (A * lam <
        localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω) ↔ False
    exact iff_false_intro (not_lt_of_ge (hmax.trans hA_le_A_lam))
  have htail_measure : P.real tailSet = 0 := by
    have hmeasure := MeasureTheory.measure_congr htail_empty_ae
    exact by
      simpa [tailSet] using! congrArg ENNReal.toReal hmeasure
  have hsubset :
      badPairEvent Hshift t αbad q m n ⊆ tailSet := by
    intro aω hbad
    rcases hbad with ⟨_hnm_bad, _hqm_bad, hbad_val⟩
    have hdisc_pos :
        0 < Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hthreshold :
        Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) * T =
          Real.rpow (3 : ℝ) (-αbad * ((m - q : ℕ) : ℝ)) := by
      simpa [T, x] using
        rpow_three_discount_mul_postThreshold
          (t := t) (α := αbad) (m := m) (n := n) (N := q)
    have hT_lt_H : T < Hshift m n aω := by
      have hdisc_lt :
          Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) * T <
            Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) *
              Hshift m n aω := by
        rw [hthreshold]
        exact hbad_val
      nlinarith [hdisc_lt, hdisc_pos]
    have hT_div_lt :
        T / K <
          localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω := by
      have hK_mul :
          T < K *
            localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω := by
        simpa [Hshift, quenchedProbeEnvelope, K] using hT_lt_H
      exact (div_lt_iff₀ hK_pos).2 (by simpa [mul_comm] using hK_mul)
    have hA_lam : A * lam = T / K := by
      dsimp [lam, scale]
      field_simp [hK_pos.ne', hA_pos.ne']
    exact by
      simpa [tailSet, hA_lam] using hT_div_lt
  have hle_zero :
      P.real (badPairEvent Hshift t αbad q m n) ≤ 0 := by
    exact (measureReal_mono (μ := P) hsubset).trans_eq htail_measure
  exact le_antisymm hle_zero MeasureTheory.measureReal_nonneg

/-- Endpoint concrete crude-bottom row estimate. -/
theorem measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < a →
        0 < t →
        αbad < t →
        1 ≤ A →
        P.real (crudeBottomPairEvent Hshift K a t αbad q m n) ≤
          ((S.card : ℝ) * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ ((d : ℕ) : ℝ)))) := by
  obtain ⟨Ccrude, hCcrude, hpair⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_eq_zero_of_gammaInfinity
      (d := d) params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad P hP hStruct hInf hparams q r j
  dsimp only
  intro ha ht hαt hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let L : ℝ :=
    (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / scale
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - αbad) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hS_nonneg : 0 ≤ (S.card : ℝ) := by positivity
  have hA_nonneg : 0 ≤ A := by linarith
  have htail_nonneg :
      0 ≤ ((S.card : ℝ) * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ ((d : ℕ) : ℝ)))) := by
    exact mul_nonneg
      (mul_nonneg hS_nonneg (pow_nonneg hw_pos.le q))
      (mul_nonneg (pow_nonneg hw_pos.le r) (Real.exp_pos _).le)
  by_cases hnℓ_sel : n ≤ selectedBadPairScale K a t αbad q m n
  · by_cases hnm : n < m
    · have hℓ_eq : ℓ = selectedBadPairScale K a t αbad q m n := by
        dsimp [ℓ, selectedBadPairScale, x]
      have hnℓ : n ≤ ℓ := by
        simpa [hℓ_eq] using hnℓ_sel
      have hqm : q ≤ m := by
        dsimp [m]
        exact Nat.le_add_right q r
      have hlam_lower : A * ρ ^ r ≤ lam := by
        exact
          crudeBottom_lam_lower
            (d := d) (K := K) (C := Ccrude)
            (θ := hInf.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (r := r) (j := j)
            hK_pos hCcrude hInf.thetaHat_pos ha ht hαt
            hnℓ hnm
      have hρ_pow_one : 1 ≤ ρ ^ r :=
        one_le_pow₀ (le_of_lt hρ_gt)
      have hlam_one : 1 ≤ lam := by
        have hAρ_one : 1 ≤ A * ρ ^ r := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ A * ρ ^ r :=
              mul_le_mul hA_one hρ_pow_one
                (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
        exact hAρ_one.trans hlam_lower
      have hraw :=
        hpair (t := t) (αbad := αbad) hP hStruct hInf hparams
          (N0 := N0) (q := q) (m := m) (n := n)
      dsimp only at hraw
      have hbad_zero :
          P.real (badPairEvent Hshift t αbad q m n) = 0 := by
        simpa [K, Hshift, x, scale, T, lam] using
          hraw hnm hqm hlam_one
      have hcrude_zero :
          P.real (crudeBottomPairEvent Hshift K a t αbad q m n) ≤ 0 := by
        have hmono :
            P.real (crudeBottomPairEvent Hshift K a t αbad q m n) ≤
              P.real (badPairEvent Hshift t αbad q m n) :=
          measureReal_mono
            (by
              intro ω hω
              exact hω.2.2)
        exact hmono.trans_eq hbad_zero
      exact hcrude_zero.trans htail_nonneg
    · have hempty :
          crudeBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [crudeBottomPairEvent, badPairEvent, hnm]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact htail_nonneg
  · have hempty :
        crudeBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [crudeBottomPairEvent, hnℓ_sel]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact htail_nonneg

/-- Endpoint concrete crude-bottom row cutoff.  Once the crude row parameter is
at least one, every fixed crude-bottom pair has zero probability. -/
theorem measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let A : ℝ :=
          (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < a →
        0 < t →
        αbad < t →
        1 ≤ A →
        P.real (crudeBottomPairEvent Hshift K a t αbad q m n) = 0 := by
  obtain ⟨Ccrude, hCcrude, hpair⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_eq_zero_of_gammaInfinity
      (d := d) params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad P hP hStruct hInf hparams q r j
  dsimp only
  intro ha ht hαt hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let L : ℝ :=
    (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let A : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / scale
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - αbad) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hA_nonneg : 0 ≤ A := by linarith
  by_cases hnℓ_sel : n ≤ selectedBadPairScale K a t αbad q m n
  · by_cases hnm : n < m
    · have hℓ_eq : ℓ = selectedBadPairScale K a t αbad q m n := by
        dsimp [ℓ, selectedBadPairScale, x]
      have hnℓ : n ≤ ℓ := by
        simpa [hℓ_eq] using hnℓ_sel
      have hqm : q ≤ m := by
        dsimp [m]
        exact Nat.le_add_right q r
      have hlam_lower : A * ρ ^ r ≤ lam := by
        exact
          crudeBottom_lam_lower
            (d := d) (K := K) (C := Ccrude)
            (θ := hInf.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (r := r) (j := j)
            hK_pos hCcrude hInf.thetaHat_pos ha ht hαt
            hnℓ hnm
      have hρ_pow_one : 1 ≤ ρ ^ r :=
        one_le_pow₀ (le_of_lt hρ_gt)
      have hlam_one : 1 ≤ lam := by
        have hAρ_one : 1 ≤ A * ρ ^ r := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ A * ρ ^ r :=
              mul_le_mul hA_one hρ_pow_one
                (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
        exact hAρ_one.trans hlam_lower
      have hraw :=
        hpair (t := t) (αbad := αbad) hP hStruct hInf hparams
          (N0 := N0) (q := q) (m := m) (n := n)
      dsimp only at hraw
      have hbad_zero :
          P.real (badPairEvent Hshift t αbad q m n) = 0 := by
        simpa [K, Hshift, x, scale, T, lam] using
          hraw hnm hqm hlam_one
      have hle_zero :
          P.real (crudeBottomPairEvent Hshift K a t αbad q m n) ≤ 0 := by
        have hmono :
            P.real (crudeBottomPairEvent Hshift K a t αbad q m n) ≤
              P.real (badPairEvent Hshift t αbad q m n) :=
          measureReal_mono
            (by
              intro ω hω
              exact hω.2.2)
        exact hmono.trans_eq hbad_zero
      exact le_antisymm hle_zero MeasureTheory.measureReal_nonneg
    · have hempty :
          crudeBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [crudeBottomPairEvent, badPairEvent, hnm]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
  · have hempty :
        crudeBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [crudeBottomPairEvent, hnℓ_sel]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]

/-- Endpoint crude-bottom component cutoff. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let A : ℝ :=
          (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        0 < a →
        0 < t →
        αbad < t →
        1 ≤ A →
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) = 0 := by
  obtain ⟨Ccrude, hCcrude, hrow⟩ :=
    measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity
      (d := d) params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad P hP hStruct hInf hparams q
  dsimp only
  intro ha ht hαt hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let A : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - αbad) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hd_pos : 0 < ((d : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hle_zero :
      P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤ 0 := by
    simpa using
      measureReal_crudeBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
        (μ := P) (H := Hshift) (K := K) (a := a)
        (t := t) (α := αbad) (q := q)
        (A := (1 : ℝ)) (ρ := ρ) (η := ((d : ℕ) : ℝ))
        (C := (0 : ℝ)) (w := w)
        (by norm_num : (0 : ℝ) ≤ 0) hw_pos
        (by norm_num : (1 : ℝ) ≤ 1) hρ_gt hd_pos
        (by
          intro r j
          have hz :=
            hrow (Centry := Centry) (a := a) (t := t) (αbad := αbad)
              hP hStruct hInf hparams (q := q) (r := r) (j := j)
              ha ht hαt hA_one
          simpa [K, N0, Hshift, L, A, ρ] using
            (by
              rw [hz]
              simp : P.real
                (crudeBottomPairEvent Hshift K a t αbad q (q + r) (q - j.val))
                  ≤ 0 * (w ^ r * Real.exp (-(((1 : ℝ) * ρ ^ r) ^ ((d : ℕ) : ℝ)))))
        )
  exact le_antisymm hle_zero MeasureTheory.measureReal_nonneg

/-- Endpoint crude-bottom component estimate after summing the weighted rows. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
        0 < a →
        0 < t →
        αbad < t →
        1 ≤ A →
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ ((d : ℕ) : ℝ))) *
              weightedGeometricExpKernelConst w (ρ ^ ((d : ℕ) : ℝ))) := by
  obtain ⟨Ccrude, hCcrude, hrow⟩ :=
    measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity
      (d := d) params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad P hP hStruct hInf hparams q
  dsimp only
  intro ha ht hαt hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
  have hC_nonneg : 0 ≤ (S.card : ℝ) * w ^ q := by
    positivity
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hA_one_local : 1 ≤ A := by
    simpa [A, K, L] using hA_one
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - αbad) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hd_pos : 0 < ((d : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  exact
    measureReal_crudeBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := ((d : ℕ) : ℝ))
      (C := (S.card : ℝ) * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one_local hρ_gt hd_pos
      (by
        intro r j
        simpa [K, Hshift, S, L, w, A, ρ] using
          hrow (Centry := Centry) (a := a) (t := t) (αbad := αbad)
            hP hStruct hInf hparams (q := q) (r := r) (j := j)
            ha ht hαt hA_one_local)

end

end Section57
end Ch05
end Book
end Homogenization
