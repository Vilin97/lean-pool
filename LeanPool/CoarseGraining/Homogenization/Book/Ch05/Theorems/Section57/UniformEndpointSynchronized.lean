/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointDenominator

/-! # Uniform Endpoint Synchronized -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Synchronized uniform-endpoint bad-scale inputs

The endpoint bad-scale assembly must choose the high-branch constants, the
deterministic crude cutoff constant, and the annealed entry scale only once.
The lemmas in this file expose the endpoint high-bottom branch with those
constants supplied externally.
-/

noncomputable section

/-- Localized high-bottom fixed-pair estimate at the uniform endpoint, with the
raw localized bad-pair estimate supplied externally. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high_gammaInfinity_of_badPair_bound
    {d : ℕ} [NeZero d] {Cfluct Centry a : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (_hCentry : 0 < Centry) (ha : 0 < a)
    (hhighRaw :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = (2 : ℝ) → hΓ.params = params →
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
        let tau : ℝ := min (2 : ℝ) 2
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
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref highA 2 := by
  intro t αbad P hP hStruct hInf hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let hΓ2 := hInf.toGammaSigma 2 (by norm_num : (0 : ℝ) < 2)
  have hΓ2_params : hΓ2.params = params := by
    simpa [hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using hparams
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · by_cases hell : selectedBadPairScale K a t αbad q m n < n
    · let highScale : ℝ :=
        Cfluct *
          (3 : ℝ) ^
            ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
          hInf.thetaHat ^ (2 : ℕ)
      let T : ℝ := Real.rpow (3 : ℝ) (-x)
      let highLam : ℝ := T / (2 * K * highScale)
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hHighLam : highA ≤ highLam := by
        simpa [K, x, ell, b, L, highScale, T, highLam, highA] using
          highBottom_tailParameter_interpolation_lower_bound
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hInf.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n)
            hK_pos hCfluct hInf.thetaHat_pos ha ht hαt hell hnq hqm
      have hsoft_raw :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref highLam 2 := by
        by_cases hlam : 1 ≤ highLam
        · have hraw :=
            hhighRaw (t := t) (αbad := αbad)
              hP hStruct hΓ2 rfl hΓ2_params
              (q := q) (m := m) (n := n)
          dsimp only at hraw
          have hbad :
              P.real (badPairEvent Hshift t αbad q m n) ≤
                (S.card : ℝ) *
                  ((D.card : ℝ) * Real.exp (-(highLam ^ (2 : ℝ)))) := by
            simpa [K, x, ell, selectedBadPairScale, N0, Hshift, D, S,
              highScale, T, highLam, hΓ2,
              GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using!
              hraw hell hnm hqm hlam
          have hmono :
              P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
                P.real (badPairEvent Hshift t αbad q m n) :=
            measureReal_mono (μ := P) (by
              intro ω hω
              exact hω.2.2)
          have hpref : 0 ≤ pref := by
            dsimp [pref]
            positivity
          exact
            hmono.trans
              (hbad.trans
                (by
                  simpa [pref, mul_assoc] using
                    pref_mul_exp_le_softPairTail_of_one_le_lam
                      (pref := pref) (lam := highLam) (η := (2 : ℝ))
                      hpref hlam))
        · exact
            (measureReal_le_one
              (μ := P)
              (s := highBottomPairEvent Hshift K a t αbad q m n)).trans
              (one_le_softPairTail_of_not_one_le_lam
                (pref := pref) (lam := highLam) (η := (2 : ℝ)) hlam)
      exact
        hsoft_raw.trans
          (softPairTail_mono_lam
            (pref := pref) (lam₁ := highA) (lam₂ := highLam)
            (η := (2 : ℝ)) (by norm_num) hHighLam)
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, hell]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact softPairTail_nonneg
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact softPairTail_nonneg

/-- Deterministic high-bottom fixed-pair cutoff at the uniform endpoint, with
the raw endpoint crude bad-pair cutoff supplied externally. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_eq_zero_of_crudeA_one_gammaInfinity_of_badPair_zero
    {d : ℕ} [NeZero d] {Ccrude : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCcrude : 0 < Ccrude)
    (hzeroRaw :
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
        let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) = 0) :
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → n ≤ q → αbad < t → 1 ≤ crudeA →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) = 0 := by
  intro Centry a t αbad P hP hStruct hInf hparams q m n
  dsimp only
  intro hnm hqm hnq hαt hcrudeA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / scale
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hlam_lower : crudeA ≤ lam := by
    simpa [K, x, scale, T, lam, crudeA] using
      crudeBottom_tailParameter_discount_lower_bound
        (K := K) (C := Ccrude) (θ := hInf.thetaHat)
        (t := t) (α := αbad) (q := q) (m := m) (n := n)
        hK_pos hCcrude hInf.thetaHat_pos hnq hqm
  have hlam_one : 1 ≤ lam := hcrudeA_one.trans hlam_lower
  have hbad_zero :
      P.real (badPairEvent Hshift t αbad q m n) = 0 := by
    have h := hzeroRaw (t := t) (αbad := αbad)
      hP hStruct hInf hparams (N0 := N0) (q := q) (m := m) (n := n)
    simpa [K, Hshift, x, scale, T, lam] using h hnm hqm hlam_one
  have hle_zero :
      P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤ 0 := by
    have hmono :
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          P.real (badPairEvent Hshift t αbad q m n) :=
      measureReal_mono (μ := P) (by
        intro ω hω
        exact hω.2.2)
    exact hmono.trans_eq hbad_zero
  exact le_antisymm hle_zero MeasureTheory.measureReal_nonneg

/-- Endpoint high-bottom fixed row estimate with all constants supplied
externally. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity_of_bounds
    {d : ℕ} [NeZero d] {Cfluct Ccrude Centry a : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (_hCentry : 0 < Centry) (_ha : 0 < a)
    (hhigh :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref highA 2)
    (hzero :
      ∀ {Centry' a' t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry'
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → n ≤ q → αbad < t → 1 ≤ crudeA →
        P.real (highBottomPairEvent Hshift K a' t αbad q m n) = 0) :
      ∀ {t αbad Den : ℝ},
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
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  intro t αbad Den P hP hStruct hInf hparams q r j
  dsimp only
  intro ht hαt htb hDen hDen_dom
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
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      Dhigh
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      Dcrude
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hDhigh_pos : 0 < Dhigh := by
    dsimp [Dhigh]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
      (pow_pos hInf.thetaHat_pos 2)
  have hDcrude_pos : 0 < Dcrude := by
    dsimp [Dcrude]
    exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hInf.thetaHat_pos 2)
  have hqm : q ≤ m := by
    dsimp [m]
    exact Nat.le_add_right q r
  have hnq : n ≤ q := by
    dsimp [n]
    exact Nat.sub_le q j.val
  have htail_nonneg :
      0 ≤ (Cpref * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
    positivity
  by_cases hnm : n < m
  · by_cases hcrude_one : 1 ≤ crudeA
    · have hzero_pair :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) = 0 := by
        have hz :=
          hzero (Centry' := Centry) (a' := a) (t := t) (αbad := αbad)
            hP hStruct hInf hparams (q := q) (m := m) (n := n)
        simpa [K, N0, Hshift, crudeA, Dcrude] using
          hz hnm hqm hnq hαt hcrude_one
      rw [hzero_pair]
      exact htail_nonneg
    · have hcrude_lt : crudeA < 1 := lt_of_not_ge hcrude_one
      have hfixed :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref highA 2 := by
        have hx :=
          hhigh (t := t) (αbad := αbad)
            hP hStruct hInf hparams (q := q) (m := m) (n := n)
        dsimp only at hx
        simpa [K, N0, Hshift, D, S, b, L, pref, highA, Dhigh] using
          hx hnm hqm ht hαt
      have hw_pos : 0 < w := by
        dsimp [w]
        exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
      have hw_one : 1 ≤ w := by
        have hn : 1 ≤ 3 ^ d :=
          Nat.succ_le_of_lt (pow_pos (by norm_num : (0 : ℕ) < 3) d)
        simpa [w] using (by exact_mod_cast hn : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ))
      have hwq_one : 1 ≤ w ^ q := one_le_pow₀ hw_one
      have hwr_one : 1 ≤ w ^ r := one_le_pow₀ hw_one
      have hDcard :
          (D.card : ℝ) ≤ w ^ q * w ^ r := by
        have hnm_le : n ≤ m := le_of_lt hnm
        simpa [D, w, m, n] using
          descendantsAtScale_bottom_row_card_le_weight
            (d := d) (N := N0) (q := q) (r := r) (j := j) hnm_le
      have hpref_bound :
          max 1 pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
        have hD_nonneg : 0 ≤ (D.card : ℝ) := by positivity
        have hpref_le :
            pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
          calc
            pref = (S.card : ℝ) * (D.card : ℝ) := rfl
            _ ≤ max 1 (S.card : ℝ) * (w ^ q * w ^ r) :=
              mul_le_mul
                (le_max_right 1 (S.card : ℝ)) hDcard
                hD_nonneg
                ((by norm_num : (0 : ℝ) ≤ 1).trans
                  (le_max_left 1 (S.card : ℝ)))
            _ = max 1 (S.card : ℝ) * w ^ q * w ^ r := by ring
        have hone :
            1 ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
          have hmaxS : 1 ≤ max 1 (S.card : ℝ) :=
            le_max_left 1 (S.card : ℝ)
          nlinarith [hmaxS, hwq_one, hwr_one]
        exact max_le hone hpref_le
      have hpow :
          (A * ρ ^ r) ^ η ≤ (max 1 highA) ^ (2 : ℝ) := by
        simpa [b, m, n, highA, A, ρ, η, Dhigh, Dcrude, crudeA] using
          uniformEndpoint_highBottom_tailParameter_rpow_le_high
            (d := d) (q := q) (r := r) (j := j)
            (t := t) (α := αbad) (L := L)
            (Dhigh := Dhigh) (Dcrude := Dcrude) (Den := Den)
            ht hαt (by simpa [b] using htb)
            hDhigh_pos hDcrude_pos hDen
            (by simpa [Dhigh, Dcrude, η] using hDen_dom)
            (by simpa [m, n, Dcrude, crudeA] using hcrude_lt)
      have hCpref_nonneg : 0 ≤ max 1 (S.card : ℝ) := by
        exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (S.card : ℝ))
      have hrow :=
        le_weighted_row_of_le_soft_single
          (x := P.real (highBottomPairEvent Hshift K a t αbad q m n))
          (pref := pref) (highA := highA) (A := A) (ρ := ρ) (η := η)
          (C := max 1 (S.card : ℝ)) (w := w) (q := q) (r := r)
          hfixed hpref_bound hCpref_nonneg hw_pos.le hpow
      change
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))
      calc
        P.real (highBottomPairEvent Hshift K a t αbad q m n)
            ≤ (Real.exp 1 * max 1 (S.card : ℝ) * w ^ q) *
                (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := hrow
        _ = (Cpref * w ^ q) *
                (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
              dsimp [Cpref]
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, badPairEvent, hnm]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact htail_nonneg

/-- Endpoint high-bottom component estimate from synchronized row bounds. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity_of_row_bound
    {d : ℕ} [NeZero d] {Cfluct Ccrude Centry a : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hrow :
      ∀ {t αbad Den : ℝ},
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
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
      ∀ {t αbad Den : ℝ},
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
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        αbad < t →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * (Cpref * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ η)) := by
  intro t αbad Den P hP hStruct hInf hparams q
  dsimp only
  intro ht hαt htb hDen hDen_dom hA_one
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
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hexp_pos : 0 < 2 * (t - αbad) / η := by
      exact div_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hαt)) hη_pos
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (2 * (t - αbad) / η) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hexp_pos
  have hC_nonneg : 0 ≤ Cpref * w ^ q := by
    dsimp [Cpref]
    positivity
  exact
    measureReal_highBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := η)
      (C := Cpref * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one hρ_gt hη_pos
      (by
        intro r j
        simpa [K, N0, Hshift, S, b, L, η, w, Dhigh, Dcrude,
          A, ρ, Cpref] using
          hrow (t := t) (αbad := αbad) (Den := Den)
            hP hStruct hInf hparams
            (q := q) (r := r) (j := j)
            ht hαt htb hDen hDen_dom)

/-- Endpoint crude-bottom fixed-pair cutoff with the raw endpoint crude
bad-pair cutoff supplied externally. -/
theorem measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity_of_badPair_zero
    {d : ℕ} [NeZero d] {Ccrude : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCcrude : 0 < Ccrude)
    (hzeroRaw :
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
        let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) = 0) :
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
        hzeroRaw (t := t) (αbad := αbad) hP hStruct hInf hparams
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

/-- Endpoint crude-bottom component cutoff from synchronized fixed-pair
cutoffs. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity_of_pair_zero
    {d : ℕ} [NeZero d] {Ccrude : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hpair :
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
        P.real (crudeBottomPairEvent Hshift K a t αbad q m n) = 0) :
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
            hpair (Centry := Centry) (a := a) (t := t) (αbad := αbad)
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

end

end Section57
end Ch05
end Book
end Homogenization
