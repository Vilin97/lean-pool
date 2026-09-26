/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry

/-! # Bad Pair Selection -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Selecting the intermediate scale in high bad-pair estimates

This file combines the deterministic ceiling choice for `ℓ` with the
fixed-pair high-scale probability estimate.
-/

noncomputable section

theorem three_mul_log_descendantsAtScale_originCube_nat_card_pos
    {d : ℕ} [NeZero d] {m n : ℕ} (hnm : n < m) :
    0 <
      3 *
        Real.log
          (((descendantsAtScale (originCube d ((m : ℕ) : ℤ))
            ((n : ℕ) : ℤ)).card : ℝ)) := by
  have hcard_two :
      2 ≤
        (descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)).card :=
    descendantsAtScale_originCube_nat_card_two_le (d := d) hnm
  have hlog_pos :
      0 <
        Real.log
          (((descendantsAtScale (originCube d ((m : ℕ) : ℤ))
            ((n : ℕ) : ℤ)).card : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast hcard_two)
  positivity

theorem shiftedHighBadPairFluctuationScale_pos
    {d : ℕ} [NeZero d] {σ Cfluct : ℝ}
    (hσ_pos : 0 < σ) (hCfluct : 0 < Cfluct)
    {P : Ch04.RestrictionCoeffLaw d}
    {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {N0 m n ℓ : ℕ} (hnm : n < m) :
    0 <
      quenchedProbeEnvelopeConst d *
        (((3 *
          Real.log
            (((Finset.univ : Finset (NormalizedProbeIndex d)).card : ℝ))) ^
            (min σ 2)⁻¹) *
          (((3 *
            Real.log
              (((descendantsAtScale
                (originCube d (((N0 + m : ℕ) : ℤ)))
                (((N0 + n : ℕ) : ℤ))).card : ℝ))) ^
              (min σ 2)⁻¹) *
            (Cfluct *
              (3 : ℝ) ^
                (-(d : ℝ) / 2 *
                  (Int.toNat
                    ((((N0 + n : ℕ) : ℤ) -
                      ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
              hΓ.thetaHat ^ (2 : ℕ)))) := by
  have hτ_pos : 0 < min σ 2 :=
    lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hK_pos : 0 < quenchedProbeEnvelopeConst d :=
    quenchedProbeEnvelopeConst_pos d
  have hS_base :
      0 <
        3 *
          Real.log
            (((Finset.univ : Finset (NormalizedProbeIndex d)).card : ℝ)) :=
    three_mul_log_normalizedProbeIndex_univ_card_pos (d := d)
  have hD_base :
      0 <
        3 *
          Real.log
            (((descendantsAtScale
              (originCube d (((N0 + m : ℕ) : ℤ)))
              (((N0 + n : ℕ) : ℤ))).card : ℝ)) := by
    exact
      three_mul_log_descendantsAtScale_originCube_nat_card_pos
        (d := d) (m := N0 + m) (n := N0 + n)
        (Nat.add_lt_add_left hnm N0)
  have hS_pow :
      0 <
        (3 *
          Real.log
            (((Finset.univ : Finset (NormalizedProbeIndex d)).card : ℝ))) ^
            (min σ 2)⁻¹ :=
    Real.rpow_pos_of_pos hS_base _
  have hD_pow :
      0 <
        (3 *
          Real.log
            (((descendantsAtScale
              (originCube d (((N0 + m : ℕ) : ℤ)))
              (((N0 + n : ℕ) : ℤ))).card : ℝ))) ^
            (min σ 2)⁻¹ :=
    Real.rpow_pos_of_pos hD_base _
  have htriad :
      0 <
        (3 : ℝ) ^
          (-(d : ℝ) / 2 *
            (Int.toNat
              ((((N0 + n : ℕ) : ℤ) -
                ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) := by
    positivity
  have htheta_sq : 0 < hΓ.thetaHat ^ (2 : ℕ) := by
    exact pow_pos hΓ.thetaHat_pos 2
  exact
    mul_pos hK_pos
      (mul_pos hS_pow
        (mul_pos hD_pow
          (mul_pos (mul_pos hCfluct htriad) htheta_sq)))

/-- High-scale fixed-pair estimate with the deterministic intermediate scale
chosen by a logarithmic ceiling.  The remaining hypothesis is the genuinely
stochastic threshold-size condition for the fluctuation scale. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil
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
      ∀ {q m n : ℕ} {s : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ℓ : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          K *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 *
                      (Int.toNat
                        ((((N0 + n : ℕ) : ℤ) -
                          ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        ℓ < n → n < m → q ≤ m → 1 ≤ s → A * s ≤ T / 2 →
        P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
          Real.exp (-(s ^ (min σ 2))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n s
  dsimp only
  intro hℓn hnm hqm hs hscale
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    K *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  ((((N0 + n : ℕ) : ℤ) -
                    ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let discount : ℝ := (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ))
  let R : ℝ := (3 : ℝ) ^ (-αbad * ((m - q : ℕ) : ℝ))
  let c : ℝ := K * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
  have hℓn' : ℓ < n := by
    simpa [K, x, ℓ] using hℓn
  have hthreshold : discount * T ≤ R := by
    dsimp [discount, T, R, x]
    exact le_of_eq
      (rpow_three_discount_mul_postThreshold
        (t := t) (α := αbad) (m := m) (n := n) (N := q))
  have hcenter : c ≤ T / 2 := by
    have h :=
      prefactor_rpow_three_neg_le_half_rpow_of_natCeil_log_gap
        (K := K) (a := a) (x := x) ha
    calc
      c = K * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) := rfl
      _ ≤ (1 / 2 : ℝ) * Real.rpow (3 : ℝ) (-x) := by
          simpa [ℓ] using h
      _ = T / 2 := by
          dsimp [T]
          ring
  have hscale' : A * s ≤ T / 2 := by
    simpa [K, x, ℓ, N0, D, S, A, T] using hscale
  simpa [K, x, ℓ, N0, D, S, A, T, discount, R, c] using
    hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
      (q := q) (m := m) (n := n) (ℓ := ℓ) (s := s) (T := T)
      hℓn' hnm hqm hs hthreshold hcenter hscale'

/-- High-scale fixed-pair estimate after choosing the tail parameter
`s = T / (2A)`, where `A` is the fluctuation scale and `T` is the
post-discount threshold. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil_ratio
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
        let ℓ : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          K *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 *
                      (Int.toNat
                        ((((N0 + n : ℕ) : ℤ) -
                          ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        ℓ < n → n < m → q ≤ m → 1 ≤ T / (2 * A) →
        P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
          Real.exp (-((T / (2 * A)) ^ (min σ 2))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hℓn hnm hqm hratio
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    K *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  ((((N0 + n : ℕ) : ℤ) -
                    ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  have hA_pos : 0 < A := by
    simpa [K, x, ℓ, N0, D, S, A, T] using
      shiftedHighBadPairFluctuationScale_pos
        (d := d) (σ := σ) (Cfluct := Cfluct)
        hσ_pos hCfluct hΓ (N0 := N0) (m := m) (n := n) (ℓ := ℓ) hnm
  have hscale : A * (T / (2 * A)) ≤ T / 2 := by
    have heq : A * (T / (2 * A)) = T / 2 := by
      field_simp [hA_pos.ne']
    exact le_of_eq heq
  simpa [K, x, ℓ, N0, D, S, A, T] using
    hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
      (q := q) (m := m) (n := n) (s := T / (2 * A))
      hℓn hnm hqm hratio hscale

/-- The selected-ratio high-pair estimate with the shifted scale difference
simplified to the manuscript form `n - ℓ`. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil_ratio_natScale
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
        let ℓ : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          K *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 * ((n - ℓ : ℕ) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        ℓ < n → n < m → q ≤ m → 1 ≤ T / (2 * A) →
        P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
          Real.exp (-((T / (2 * A)) ^ (min σ 2))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil_ratio
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hℓn hnm hqm hratio
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    K *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 * ((n - ℓ : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let Araw : ℝ :=
    K *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  ((((N0 + n : ℕ) : ℤ) -
                    ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  have hAraw_eq : Araw = A := by
    have hℓ_le_n : ℓ ≤ n := le_of_lt hℓn
    have hdiff :
        Int.toNat
          ((((N0 + n : ℕ) : ℤ) -
            ((N0 + ℓ : ℕ) : ℤ))) = n - ℓ :=
      int_toNat_nat_add_sub_nat_add_of_le hℓ_le_n
    have hdiff' :
        Int.toNat
          (((N0 : ℤ) + (n : ℤ)) - ((N0 : ℤ) + (ℓ : ℤ))) = n - ℓ := by
      change
        Int.toNat
          ((((N0 + n : ℕ) : ℤ) -
            ((N0 + ℓ : ℕ) : ℤ))) = n - ℓ
      exact hdiff
    dsimp [Araw, A]
    rw [hdiff']
  have hratio_raw : 1 ≤ T / (2 * Araw) := by
    have hratio_A : 1 ≤ T / (2 * A) := by
      simpa [K, x, ℓ, N0, D, S, A, T] using hratio
    simpa [hAraw_eq] using hratio_A
  have hraw :=
    hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
      (q := q) (m := m) (n := n)
  dsimp only at hraw
  have hbound :=
    hraw hℓn hnm hqm hratio_raw
  simpa [K, x, ℓ, N0, D, S, A, Araw, T, hAraw_eq] using hbound

/-- High-pair estimate fed by any deterministic lower bound on the selected
tail parameter. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil_natScale_of_le_ratio
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
      ∀ {q m n : ℕ} {B : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ℓ : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          K *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 * ((n - ℓ : ℕ) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        ℓ < n → n < m → q ≤ m → 1 ≤ B → B ≤ T / (2 * A) →
        P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
          Real.exp (-(B ^ (min σ 2))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp_of_natCeil_ratio_natScale
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n B
  dsimp only
  intro hℓn hnm hqm hB_one hB_le
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    K *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 * ((n - ℓ : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  have hratio : 1 ≤ T / (2 * A) := hB_one.trans hB_le
  have hprob :
      P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
        Real.exp (-((T / (2 * A)) ^ (min σ 2))) := by
    simpa [K, x, ℓ, N0, D, S, A, T] using
      hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
        (q := q) (m := m) (n := n)
        hℓn hnm hqm hratio
  have hτ_nonneg : 0 ≤ min σ 2 :=
    (lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)).le
  have hB_nonneg : 0 ≤ B := zero_le_one.trans hB_one
  have hratio_nonneg : 0 ≤ T / (2 * A) := hB_nonneg.trans hB_le
  have hpow_le :
      B ^ (min σ 2) ≤ (T / (2 * A)) ^ (min σ 2) :=
    Real.rpow_le_rpow hB_nonneg hB_le hτ_nonneg
  have hexp :
      Real.exp (-((T / (2 * A)) ^ (min σ 2))) ≤
        Real.exp (-(B ^ (min σ 2))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact hprob.trans hexp

end

end Section57
end Ch05
end Book
end Homogenization
