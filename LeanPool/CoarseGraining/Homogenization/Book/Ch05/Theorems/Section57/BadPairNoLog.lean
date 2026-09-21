/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMaxTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.DeterministicThresholds

/-! # Bad Pair No Log -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# No-log fixed bad-pair probability bounds

This file restarts the bad-scale tail proof after removing the exponent-loss
route.  The estimates here keep finite maxima as probability prefactors instead
of putting logarithmic factors into the stochastic scale.
-/

noncomputable section

/-- High-range fixed bad-pair estimate with explicit finite-union prefactors
and no logarithmic scale inflation. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
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
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, htail⟩ :=
    measureReal_localizedFirstQuenchedEstimate_normalizedProbeJMax_tail_noLog
      (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro helln hnm hqm hlam
  classical
  let : IsProbabilityMeasure P := hP.isProbability
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
  let b : ℝ := (d : ℝ) / 2
  let center : ℝ := Real.rpow (3 : ℝ) (-a * (ell : ℝ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^
        ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let lam : ℝ := T / (2 * K * scale)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos
      (mul_pos hCfluct (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _))
      (pow_pos hΓ.thetaHat_pos 2)
  have hT_pos : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hcenterK :
      K * center ≤ (1 / 2 : ℝ) * T := by
    simpa [K, x, ell, center, T] using
      prefactor_rpow_three_neg_le_half_rpow_of_natCeil_log_gap
        (K := K) (a := a) (x := x) ha
  have hsubset :
      badPairEvent Hshift t αbad q m n ⊆
        {aω | center + scale * lam <
          localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} := by
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
    have hcenter_le : center ≤ T / (2 * K) := by
      have hmul : center * (2 * K) ≤ T := by
        nlinarith [hcenterK]
      exact (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos)).2 hmul
    have hscale_lam : scale * lam = T / (2 * K) := by
      dsimp [lam]
      field_simp [hscale_pos.ne']
    have hsum_le : center + scale * lam ≤ T / K := by
      rw [hscale_lam]
      calc
        center + T / (2 * K) ≤ T / (2 * K) + T / (2 * K) := by
          nlinarith [hcenter_le]
        _ = T / K := by
          field_simp [hK_pos.ne']
          ring
    exact lt_of_le_of_lt hsum_le hT_div_lt
  have htail_bound :
      P.real
          {aω | center + scale * lam <
            localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} ≤
        (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
    simpa [N0, D, S, tau, b, center, scale] using
      htail hP hStruct hΓ hσ_eq hparams
        (ell := ell) (n := n) (m := m) (lam := lam)
        hlam helln hnm
  exact (measureReal_mono (μ := P) hsubset).trans htail_bound

/-- Uniform-in-`σ` version of
`measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog`. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
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
              (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
  obtain ⟨Centry, a, hCentry, ha, htailBase⟩ :=
    measureReal_localizedFirstQuenchedEstimate_normalizedProbeJMax_tail_noLog_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, hCfluct, htail⟩ := htailBase hσ_pos
  refine ⟨Cfluct, hCfluct, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro helln hnm hqm hlam
  classical
  let : IsProbabilityMeasure P := hP.isProbability
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
  let b : ℝ := (d : ℝ) / 2
  let center : ℝ := Real.rpow (3 : ℝ) (-a * (ell : ℝ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^
        ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let lam : ℝ := T / (2 * K * scale)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos
      (mul_pos hCfluct (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _))
      (pow_pos hΓ.thetaHat_pos 2)
  have hT_pos : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hcenterK :
      K * center ≤ (1 / 2 : ℝ) * T := by
    simpa [K, x, ell, center, T] using
      prefactor_rpow_three_neg_le_half_rpow_of_natCeil_log_gap
        (K := K) (a := a) (x := x) ha
  have hsubset :
      badPairEvent Hshift t αbad q m n ⊆
        {aω | center + scale * lam <
          localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} := by
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
    have hcenter_le : center ≤ T / (2 * K) := by
      have hmul : center * (2 * K) ≤ T := by
        nlinarith [hcenterK]
      exact (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos)).2 hmul
    have hscale_lam : scale * lam = T / (2 * K) := by
      dsimp [lam]
      field_simp [hscale_pos.ne']
    have hsum_le : center + scale * lam ≤ T / K := by
      rw [hscale_lam]
      calc
        center + T / (2 * K) ≤ T / (2 * K) + T / (2 * K) := by
          nlinarith [hcenter_le]
        _ = T / K := by
          field_simp [hK_pos.ne']
          ring
    exact lt_of_le_of_lt hsum_le hT_div_lt
  have htail_bound :
      P.real
          {aω | center + scale * lam <
            localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} ≤
        (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
    simpa [N0, D, S, tau, b, center, scale] using
      htail hP hStruct hΓ hσ_eq hparams
        (ell := ell) (n := n) (m := m) (lam := lam)
        hlam helln hnm
  exact (measureReal_mono (μ := P) hsubset).trans htail_bound

/-- Crude fixed bad-pair estimate with explicit finite-union prefactors and
no logarithmic scale inflation. -/
theorem measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
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
        let scale : ℝ := K * (C * hΓ.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
  obtain ⟨C, hC, horigin⟩ :=
    isBigO_limitNormalizedBlockJObservable_originCube_of_scaleZero
      (d := d) hσ_pos params
  refine ⟨C, hC, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams N0 q m n
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
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ := C * hΓ.thetaHat ^ (2 : ℕ)
  let scale : ℝ := K * A
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let lam : ℝ := T / scale
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hC (pow_pos hΓ.thetaHat_pos 2)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos hK_pos hA_pos
  have hOrigin :
      ∀ i : NormalizedProbeIndex d,
        IsBigO P (gammaSigma σ)
          (limitNormalizedBlockJObservable hP hStruct
            (originCube d (((N0 + n : ℕ) : ℤ))) (normalizedProbeVec i)) A := by
    intro i
    simpa [A] using
      horigin hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i)
        (normalizedProbeVec_abs_apply_le_one i)
        (n := N0 + n)
  have htail_bound :
      P.real
          {aω | A * lam <
            localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} ≤
        (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
    simpa [D, S, A] using
      measureReal_localizedNormalizedProbeJMax_tail_le_card_mul_card_mul_exp_of_isBigO
        hP hStruct hStruct.stationary
        (σ := σ) (A := A) (lam := lam)
        hlam (m := N0 + m) (n := N0 + n)
        (Nat.add_lt_add_left hnm N0) hOrigin
  have hsubset :
      badPairEvent Hshift t αbad q m n ⊆
        {aω | A * lam <
          localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} := by
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
    simpa [hA_lam] using hT_div_lt
  exact (measureReal_mono (μ := P) hsubset).trans htail_bound

end

end Section57
end Ch05
end Book
end Homogenization
