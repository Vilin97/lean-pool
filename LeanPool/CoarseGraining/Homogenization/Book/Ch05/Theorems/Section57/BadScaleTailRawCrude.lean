/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRaw

/-! # Bad Scale Tail Raw Crude -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Raw-constant crude-bottom component

This file exposes the crude-bottom component estimate with the raw crude
fixed-pair estimate supplied externally.  It is used to keep the crude branch
constant synchronized with the mixed high-bottom branch in the final bad-scale
assembly.
-/

noncomputable section

/-- Crude-bottom component estimate using a supplied raw crude fixed-pair tail. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
    {d : ℕ} [NeZero d] {σ Ccrude : ℝ}
    (hσ_pos : 0 < σ) (hCcrude : 0 < Ccrude)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hcrudeRaw :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {N0 q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ)))) :
      ∀ {Centry a t αbad : ℝ},
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
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
        0 < a →
        0 < t →
        αbad < t →
        1 ≤ A →
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ σ)) *
              weightedGeometricExpKernelConst w (ρ ^ σ)) := by
  intro Centry a t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ha ht hαt hA_one
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
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
      (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
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
  exact
    measureReal_crudeBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := σ)
      (C := (S.card : ℝ) * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one_local hρ_gt hσ_pos
      (by
        intro r j
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ℓ : ℕ := selectedBadPairScale K a t αbad q m n
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let T : ℝ := (3 : ℝ) ^ (-x)
        let lam : ℝ := T / scale
        have hK_pos : 0 < K := by
          simpa [K] using quenchedProbeEnvelopeConst_pos d
        have hρ_pos : 0 < ρ := by
          dsimp [ρ]
          exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
        have hA_nonneg : 0 ≤ A := by linarith
        have hAρ_nonneg : 0 ≤ A * ρ ^ r :=
          mul_nonneg hA_nonneg (pow_nonneg hρ_pos.le r)
        have htail_nonneg :
            0 ≤ ((S.card : ℝ) * w ^ q) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
          exact mul_nonneg
            (mul_nonneg (by positivity) (pow_nonneg hw_pos.le q))
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
                  (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
                  (q := q) (r := r) (j := j)
                  hK_pos hCcrude hΓ.thetaHat_pos ha ht hαt
                  hnℓ hnm
            have hρ_pow_one : 1 ≤ ρ ^ r :=
              one_le_pow₀ (le_of_lt hρ_gt)
            have hlam_one : 1 ≤ lam := by
              have hAρ_one : 1 ≤ A * ρ ^ r := by
                calc
                  (1 : ℝ) = 1 * 1 := by ring
                  _ ≤ A * ρ ^ r :=
                    mul_le_mul hA_one_local hρ_pow_one
                      (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
              exact hAρ_one.trans hlam_lower
            have hraw :=
              hcrudeRaw (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
                (N0 := N0) (q := q) (m := m) (n := n)
            dsimp only at hraw
            have hbad :
                P.real (badPairEvent Hshift t αbad q m n) ≤
                  (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
              simpa [K, Hshift, x, D, S, scale, T, lam] using
                hraw hnm hqm hlam_one
            have hD :
                (D.card : ℝ) ≤ w ^ q * w ^ r := by
              have hnm_le : n ≤ m := le_of_lt hnm
              simpa [D, w, m, n] using
                descendantsAtScale_bottom_row_card_le_weight
                  (d := d) (N := N0) (q := q) (r := r) (j := j) hnm_le
            exact
              measureReal_crudeBottomPairEvent_le_weighted_row_of_badPair_bound
                (μ := P) (H := Hshift) (K := K) (a := a)
                (t := t) (α := αbad) (q := q) (m := m) (n := n)
                (r := r) (S := (S.card : ℝ)) (D := (D.card : ℝ))
                (A := A) (ρ := ρ) (σ := σ) (lam := lam) (w := w)
                (by positivity) hw_pos.le hD hAρ_nonneg hlam_lower hσ_pos hbad
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
          exact htail_nonneg)

end

end Section57
end Ch05
end Book
end Homogenization
