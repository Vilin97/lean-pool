/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailDenominator

/-! # Bad Scale Tail Raw -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Raw-constant bad-scale component inputs

This file exposes the mixed high-bottom fixed-pair estimate with the raw high
and crude pair estimates supplied as hypotheses.  This keeps the constants used
by the top, mixed-bottom, and crude-bottom branches synchronized for the final
bad-scale assembly.
-/

noncomputable section

/-- Exact fixed-pair mixed-bottom estimate with the high and crude raw pair
estimates supplied externally, so downstream assembly can use one shared set
of constants. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_max_mixed_of_badPair_bounds
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (_hCentry : 0 < Centry) (ha : 0 < a)
    (hhighRaw :
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
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))))
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
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
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
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ tau) ((max 1 crudeA) ^ σ)) := by
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
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
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let tau : ℝ := min σ 2
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · by_cases hell : selectedBadPairScale K a t αbad q m n < n
    · let highScale : ℝ :=
        Cfluct *
          (3 : ℝ) ^
            ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)
      let T : ℝ := Real.rpow (3 : ℝ) (-x)
      let highLam : ℝ := T / (2 * K * highScale)
      let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
      let crudeLam : ℝ := T / crudeScale
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hHighLam : highA ≤ highLam := by
        simpa [K, x, ell, b, L, highScale, T, highLam, highA] using
          highBottom_tailParameter_interpolation_lower_bound
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n)
            hK_pos hCfluct hΓ.thetaHat_pos ha ht hαt hell hnq hqm
      have hCrudeLam : crudeA ≤ crudeLam := by
        simpa [K, x, crudeScale, T, crudeLam, crudeA] using
          crudeBottom_tailParameter_discount_lower_bound
            (K := K) (C := Ccrude) (θ := hΓ.thetaHat)
            (t := t) (α := αbad) (q := q) (m := m) (n := n)
            hK_pos hCcrude hΓ.thetaHat_pos hnq hqm
      have htau_pos : 0 < tau := by
        dsimp [tau]
        exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
      have hhighSoft :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref highA tau := by
        have hsoft_raw :
            P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
              softPairTail pref highLam tau := by
          by_cases hlam : 1 ≤ highLam
          · have hraw :=
              hhighRaw (t := t) (αbad := αbad)
                hP hStruct hΓ hσ_eq hparams
                (q := q) (m := m) (n := n)
            dsimp only at hraw
            have hbad :
                P.real (badPairEvent Hshift t αbad q m n) ≤
                  (S.card : ℝ) *
                    ((D.card : ℝ) * Real.exp (-(highLam ^ tau))) := by
              simpa [K, x, ell, selectedBadPairScale, N0, Hshift, D, S, tau,
                highScale, T, highLam] using
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
                        (pref := pref) (lam := highLam) (η := tau)
                        hpref hlam))
          · exact
              (measureReal_le_one
                (μ := P)
                (s := highBottomPairEvent Hshift K a t αbad q m n)).trans
                (one_le_softPairTail_of_not_one_le_lam
                  (pref := pref) (lam := highLam) (η := tau) hlam)
        exact
          hsoft_raw.trans
            (softPairTail_mono_lam
              (pref := pref) (lam₁ := highA) (lam₂ := highLam)
              (η := tau) htau_pos hHighLam)
      have hcrudeSoft :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref crudeA σ := by
        have hsoft_raw :
            P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
              softPairTail pref crudeLam σ := by
          by_cases hlam : 1 ≤ crudeLam
          · have hraw :=
              hcrudeRaw (t := t) (αbad := αbad)
                hP hStruct hΓ hσ_eq hparams
                (N0 := N0) (q := q) (m := m) (n := n)
            dsimp only at hraw
            have hbad :
                P.real (badPairEvent Hshift t αbad q m n) ≤
                  (S.card : ℝ) *
                    ((D.card : ℝ) * Real.exp (-(crudeLam ^ σ))) := by
              simpa [K, Hshift, x, D, S, crudeScale, T, crudeLam] using
                hraw hnm hqm hlam
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
                        (pref := pref) (lam := crudeLam) (η := σ)
                        hpref hlam))
          · exact
              (measureReal_le_one
                (μ := P)
                (s := highBottomPairEvent Hshift K a t αbad q m n)).trans
                (one_le_softPairTail_of_not_one_le_lam
                  (pref := pref) (lam := crudeLam) (η := σ) hlam)
        exact
          hsoft_raw.trans
            (softPairTail_mono_lam
              (pref := pref) (lam₁ := crudeA) (lam₂ := crudeLam)
              (η := σ) hσ_pos hCrudeLam)
      exact
        le_maxExponent_softPairTail_of_le_both
          (x := P.real (highBottomPairEvent Hshift K a t αbad q m n))
          (pref := pref) (lam₁ := highA) (lam₂ := crudeA)
          (η₁ := tau) (η₂ := σ) hhighSoft hcrudeSoft
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, hell]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact mul_nonneg
        ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
        (Real.exp_pos _).le
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
      (Real.exp_pos _).le

/-- Convert the synchronized mixed-bottom soft fixed-pair estimate into the
weighted row estimate with the corrected finite exponent. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_interpolated_weighted_row_of_soft_max_bound
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (_hCentry : 0 < Centry) (ha : 0 < a)
    (hpair :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
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
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ tau) ((max 1 crudeA) ^ σ))) :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
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
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q r j
  dsimp only
  intro ht htb hαt hDen hDen_high hDen_crude
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
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  by_cases hnm : n < m
  · let D : Finset (TriadicCube d) :=
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
    have hqm : q ≤ m := by
      dsimp [m]
      exact Nat.le_add_right q r
    have hx :=
      hpair (t := t) (αbad := αbad)
        hP hStruct hΓ hσ_eq hparams (q := q) (m := m) (n := n)
    dsimp only at hx
    have hfixed :
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)) := by
      simpa [K, N0, Hshift, D, S, b, L, τ, pref, highA, crudeA,
        Dhigh, Dcrude] using!
        hx hnm hqm ht hαt
    have hη_pos : 0 < η := by
      simpa [η] using
        finiteQuenchedTailExponent_pos
          (d := d) (σ := σ) (t := t) hσ_pos ht
    have hτ_pos : 0 < τ := by
      simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
    have hb_pos : 0 < b := by
      dsimp [b]
      have hd : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      positivity
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
    have hlog3_pos : 0 < Real.log (3 : ℝ) :=
      Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hL_nonneg : 0 ≤ L := by
      have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
      have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
        Real.log_nonneg (le_max_right (2 * K) 1)
      dsimp [L]
      positivity
    have hoff_nonneg : 0 ≤ τ * b * (L + 1) := by
      positivity
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
    have hpref_bound : max 1 pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
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
        have hmaxS : 1 ≤ max 1 (S.card : ℝ) := le_max_left 1 (S.card : ℝ)
        nlinarith [hmaxS, hwq_one, hwr_one]
      exact max_le hone hpref_le
    let row : ℝ := τ * (t - αbad)
    let offset : ℝ := τ * b * (L + 1)
    let X : ℝ := η * (q : ℝ) - offset + row * (r : ℝ)
    let Xhigh : ℝ :=
      τ *
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1))
    let Xcrude : ℝ :=
      σ *
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ))
    have hm_sub_q : m - q = r := by
      dsimp [m]
      exact Nat.add_sub_cancel_left q r
    have hcollapse_raw :
        η * (q : ℝ) + τ * (t - αbad) * (r : ℝ) ≤
          max
            (τ *
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * (r : ℝ)))
            (σ * (t * ((q - n : ℕ) : ℝ) + (t - αbad) * (r : ℝ))) := by
      have hmain :=
        finiteQuenchedTailExponent_mul_nat_add_row_le_max_bottom
          (d := d) (q := q) (n := n) (r := r)
          (σ := σ) (t := t) (α := αbad) hσ_pos ht hαt
          (by simpa [b] using htb)
      simpa [b, τ, η] using hmain
    have hcollapse :
        X ≤ max Xhigh Xcrude := by
      have hsub :=
        sub_nonneg_le_max_sub_left_of_le_max
          (c := offset) (by simpa [offset] using hoff_nonneg)
          hcollapse_raw
      have hX_eq :
          X = η * (q : ℝ) + τ * (t - αbad) * (r : ℝ) - offset := by
        dsimp [X, row]
        ring
      have hXhigh_eq :
          Xhigh =
            τ *
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * (r : ℝ)) - offset := by
        dsimp [Xhigh, offset]
        rw [hm_sub_q]
        ring
      have hXcrude_eq :
          Xcrude =
            σ * (t * ((q - n : ℕ) : ℝ) + (t - αbad) * (r : ℝ)) := by
        dsimp [Xcrude]
        rw [hm_sub_q]
      rw [hX_eq, hXhigh_eq, hXcrude_eq]
      exact hsub
    have hAρ :
        A * ρ ^ r = (3 : ℝ) ^ (X / η) / Den := by
      simpa [A, ρ, X, row, offset] using
        rpow_three_row_parameter_div_eq
          (q := q) (r := r) (offset := offset)
          (row := row) (Den := Den) (η := η) hη_pos
    have hhigh_exp :
        Xhigh / τ =
          b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1) := by
      dsimp [Xhigh]
      field_simp [hτ_pos.ne']
    have hcrude_exp :
        Xcrude / σ =
          t * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ) := by
      dsimp [Xcrude]
      field_simp [hσ_pos.ne']
    have hpow :
        (A * ρ ^ r) ^ η ≤
          max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ) := by
      rw [hAρ]
      have hgeneric :=
        rpow_three_div_den_le_branch_max_of_exponent_le_max
          (X := X) (Xhigh := Xhigh) (Xcrude := Xcrude)
          (Dhigh := Dhigh) (Dcrude := Dcrude) (Den := Den)
          (η := η) (τ := τ) (σ := σ)
          hη_pos hτ_pos hσ_pos hDhigh_pos hDcrude_pos hDen
          (by simpa [Dhigh, τ, η] using hDen_high)
          (by simpa [Dcrude, η] using hDen_crude)
          hcollapse
      rw [hhigh_exp, hcrude_exp] at hgeneric
      simpa [highA, crudeA] using hgeneric
    have hCpref_nonneg : 0 ≤ max 1 (S.card : ℝ) := by
      exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (S.card : ℝ))
    have hrow :=
      le_weighted_row_of_le_soft_maxExponent
        (x := P.real (highBottomPairEvent Hshift K a t αbad q m n))
        (pref := pref) (highA := highA) (crudeA := crudeA)
        (τ := τ) (σ := σ) (A := A) (ρ := ρ) (η := η)
        (C := max 1 (S.card : ℝ)) (w := w)
        (q := q) (r := r)
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
    positivity

/-- Sum synchronized mixed-bottom row estimates into the high-bottom component
bound, still without choosing new constants. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_weighted_kernel_of_row_bound
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hrow :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ →
        hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
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
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ →
        hΓ.params = params →
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
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * (Cpref * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ η)) := by
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hαt hDen hDen_high hDen_crude hA_one
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
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    simpa [η] using
      finiteQuenchedTailExponent_pos
        (d := d) (σ := σ) (t := t) hσ_pos ht
  have hτ_pos : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hexp_pos : 0 < τ * (t - αbad) / η := by
      exact div_pos (mul_pos hτ_pos (sub_pos.mpr hαt)) hη_pos
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (τ * (t - αbad) / η) :=
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
        simpa [K, N0, Hshift, S, b, L, τ, η, w, Dhigh, Dcrude,
          A, ρ, Cpref] using
          hrow (t := t) (αbad := αbad) (Den := Den)
            hP hStruct hΓ hσ_eq hparams
            (q := q) (r := r) (j := j)
            ht htb hαt hDen hDen_high hDen_crude)

end

end Section57
end Ch05
end Book
end Homogenization
