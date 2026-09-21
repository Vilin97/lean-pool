/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailTwoBranch
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsHigh
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsCrudeBottom

/-! # Bad Scale Tail Denominator -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Denominator selection for the interpolated bad-scale tail

This file removes the explicit denominator-domination side conditions from the
mixed high-bottom component bound by choosing the normalizing denominator as
the maximum of the two branch denominators at the correct powers.
-/

noncomputable section

/-- If the denominator for a normalized `eta`-tail dominates the branch
denominator after raising to the relevant powers, and the exponent in the
normalized tail is no larger than the branch exponent, then the normalized
tail parameter is bounded by the branch tail parameter. -/
theorem rpow_three_div_den_rpow_le_of_exponent_le
    {X Y D Den η γ : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hD : 0 < D) (hDen : 0 < Den)
    (hDpow : D ^ γ ≤ Den ^ η) (hXY : X ≤ Y) :
    (((3 : ℝ) ^ (X / η) / Den) ^ η) ≤
      (((3 : ℝ) ^ (Y / γ) / D) ^ γ) := by
  have hthree_pos : 0 < (3 : ℝ) := by norm_num
  have hthree_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have hDenη_pos : 0 < Den ^ η := Real.rpow_pos_of_pos hDen η
  have hDγ_pos : 0 < D ^ γ := Real.rpow_pos_of_pos hD γ
  have hlhs :
      (((3 : ℝ) ^ (X / η) / Den) ^ η) =
        (3 : ℝ) ^ X / Den ^ η := by
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDen.le η]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hη.ne']
  have hrhs :
      (((3 : ℝ) ^ (Y / γ) / D) ^ γ) =
        (3 : ℝ) ^ Y / D ^ γ := by
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hD.le γ]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hγ.ne']
  rw [hlhs, hrhs]
  have hpow : (3 : ℝ) ^ X ≤ (3 : ℝ) ^ Y :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hXY
  calc
    (3 : ℝ) ^ X / Den ^ η
        ≤ (3 : ℝ) ^ Y / Den ^ η :=
          div_le_div_of_nonneg_right hpow hDenη_pos.le
    _ ≤ (3 : ℝ) ^ Y / D ^ γ :=
          div_le_div_of_nonneg_left
            (Real.rpow_pos_of_pos hthree_pos Y).le hDγ_pos hDpow

/-- Recover a lower bound on a positive base from a lower bound on a positive
power of that base. -/
theorem one_le_of_one_le_rpow
    {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) (hpow : 1 ≤ x ^ η) :
    1 ≤ x := by
  have hpow' : (1 : ℝ) ^ η ≤ x ^ η := by simpa using hpow
  exact (Real.rpow_le_rpow_iff zero_le_one hx hη).mp hpow'

/-- The denominator that dominates both branch denominators after raising to
the corrected finite exponent. -/
noncomputable def mixedBottomTailDenominator
    (Dhigh Dcrude η τ σ : ℝ) : ℝ :=
  max ((max 1 Dhigh) ^ (τ / η)) ((max 1 Dcrude) ^ (σ / η))

theorem mixedBottomTailDenominator_pos
    {Dhigh Dcrude η τ σ : ℝ} :
    0 < mixedBottomTailDenominator Dhigh Dcrude η τ σ := by
  have hbase : 0 < max 1 Dhigh :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 Dhigh)
  have hterm : 0 < (max 1 Dhigh) ^ (τ / η) :=
    Real.rpow_pos_of_pos hbase _
  exact hterm.trans_le (le_max_left _ _)

theorem branch_denominator_le_mixedBottomTailDenominator_pow_eta
    {Dhigh Dcrude η τ σ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) (hσ : 0 < σ)
    (hDhigh : 0 < Dhigh) (hDcrude : 0 < Dcrude) :
    Dhigh ^ τ ≤ (mixedBottomTailDenominator Dhigh Dcrude η τ σ) ^ η ∧
      Dcrude ^ σ ≤ (mixedBottomTailDenominator Dhigh Dcrude η τ σ) ^ η := by
  have hbaseHigh_pos : 0 < max 1 Dhigh :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 Dhigh)
  have hbaseCrude_pos : 0 < max 1 Dcrude :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 Dcrude)
  have htermHigh_nonneg : 0 ≤ (max 1 Dhigh) ^ (τ / η) :=
    (Real.rpow_pos_of_pos hbaseHigh_pos _).le
  have htermCrude_nonneg : 0 ≤ (max 1 Dcrude) ^ (σ / η) :=
    (Real.rpow_pos_of_pos hbaseCrude_pos _).le
  have hhigh_eq :
      ((max 1 Dhigh) ^ (τ / η)) ^ η = (max 1 Dhigh) ^ τ := by
    rw [← Real.rpow_mul hbaseHigh_pos.le]
    congr 1
    field_simp [hη.ne']
  have hcrude_eq :
      ((max 1 Dcrude) ^ (σ / η)) ^ η = (max 1 Dcrude) ^ σ := by
    rw [← Real.rpow_mul hbaseCrude_pos.le]
    congr 1
    field_simp [hη.ne']
  constructor
  · have hD_le : Dhigh ≤ max 1 Dhigh := le_max_right 1 Dhigh
    have hpow_le : Dhigh ^ τ ≤ (max 1 Dhigh) ^ τ :=
      Real.rpow_le_rpow hDhigh.le hD_le hτ.le
    have hterm_le :
        (max 1 Dhigh) ^ (τ / η) ≤
          mixedBottomTailDenominator Dhigh Dcrude η τ σ := by
      dsimp [mixedBottomTailDenominator]
      exact le_max_left _ _
    have hterm_pow_le :
        ((max 1 Dhigh) ^ (τ / η)) ^ η ≤
          (mixedBottomTailDenominator Dhigh Dcrude η τ σ) ^ η :=
      Real.rpow_le_rpow htermHigh_nonneg hterm_le hη.le
    exact hpow_le.trans (by simpa [hhigh_eq] using hterm_pow_le)
  · have hD_le : Dcrude ≤ max 1 Dcrude := le_max_right 1 Dcrude
    have hpow_le : Dcrude ^ σ ≤ (max 1 Dcrude) ^ σ :=
      Real.rpow_le_rpow hDcrude.le hD_le hσ.le
    have hterm_le :
        (max 1 Dcrude) ^ (σ / η) ≤
          mixedBottomTailDenominator Dhigh Dcrude η τ σ := by
      dsimp [mixedBottomTailDenominator]
      exact le_max_right _ _
    have hterm_pow_le :
        ((max 1 Dcrude) ^ (σ / η)) ^ η ≤
          (mixedBottomTailDenominator Dhigh Dcrude η τ σ) ^ η :=
      Real.rpow_le_rpow htermCrude_nonneg hterm_le hη.le
    exact hpow_le.trans (by simpa [hcrude_eq] using hterm_pow_le)

/-- High-top component rewritten with the corrected finite bad-scale exponent.
The proof uses the same raw high-range estimate as the original high-top
component and only changes the deterministic tail parameter. -/
theorem measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_badPair_bound
    {d : ℕ} [NeZero d] {σ Cfluct Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCentry : 0 < Centry) (ha : 0 < a)
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
      ∀ {t αbad Den : ℝ},
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
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ c
        0 < t →
        t ≤ b →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        1 ≤ A →
        P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
          (S.card : ℝ) *
            (Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ τ)) := by
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hαt hαb hαharm hDen hDen_high hA_one
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
  let c : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Aold : ℝ :=
    (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) / Dhigh
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ c
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
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
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDen.le
  have hAold_nonneg : 0 ≤ Aold := by
    dsimp [Aold]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDhigh_pos.le
  let X : ℝ := η * ((q : ℝ) - (τ * b * (L + 1)) / η)
  let Y : ℝ := τ * (b * (q : ℝ) - b * (L + 1))
  have hXY : X ≤ Y := by
    have hmain :=
      finiteQuenchedTailExponent_mul_nat_le_tau_mul_b_nat
        (d := d) (σ := σ) (t := t) (q := q)
        hσ_pos ht (by simpa [b] using htb)
    have hmain' : η * (q : ℝ) ≤ τ * b * (q : ℝ) := by
      simpa [η, τ, b, mul_assoc] using hmain
    dsimp [X, Y]
    field_simp [hη_pos.ne']
    ring_nf
    nlinarith
  have hA_to_old : A ^ η ≤ Aold ^ τ := by
    have hgeneric :=
      rpow_three_div_den_rpow_le_of_exponent_le
        (X := X) (Y := Y) (D := Dhigh) (Den := Den)
        (η := η) (γ := τ)
        hη_pos hτ_pos hDhigh_pos hDen
        (by simpa [Dhigh, τ, η] using hDen_high) hXY
    convert hgeneric using 1
    · dsimp [A, X]
      congr 2
      field_simp [hη_pos.ne']
    · dsimp [Aold, Y]
      congr 2
      field_simp [hτ_pos.ne']
  have hAold_one : 1 ≤ Aold := by
    have hA_pow_one : 1 ≤ A ^ η := Real.one_le_rpow hA_one hη_pos.le
    exact one_le_of_one_le_rpow hAold_nonneg hτ_pos (hA_pow_one.trans hA_to_old)
  have htop_old :
      P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
        (S.card : ℝ) *
          (Real.exp (-(Aold ^ τ)) *
            weightedLinearExpKernelConst w (ρ ^ τ)) := by
    have htop :=
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hpair
        (t := t) (αbad := αbad)
        hP hStruct hΓ hσ_eq hparams (q := q)
    simpa [K, N0, Hshift, S, b, L, c, τ, Aold, ρ, w] using!
      htop ht hαt hαb hαharm hAold_one
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hc_pos : 0 < c := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    have hbα : 0 < b - αbad := sub_pos.mpr hαb
    have hfactor : 0 < 1 + b / a := by
      have hba : 0 < b / a := div_pos hb_pos ha
      linarith
    have hthird : 0 < (t - αbad) * (1 + b / a) :=
      mul_pos hgap hfactor
    have hfourth : 0 < b - αbad * (1 + b / a) :=
      sub_pos.mpr hαharm
    dsimp [c]
    exact lt_min hgap (lt_min hbα (lt_min hthird hfourth))
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ c :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hc_pos
  have hkernel_nonneg :
      0 ≤ weightedLinearExpKernelConst w (ρ ^ τ) :=
    (weightedLinearExpKernelConst_pos
      (w := w) (R := ρ ^ τ) hw_pos
      (Real.one_lt_rpow hρ_gt hτ_pos)).le
  have hexp :
      Real.exp (-(Aold ^ τ)) ≤ Real.exp (-(A ^ η)) :=
    Real.exp_le_exp.mpr (by linarith [hA_to_old])
  have hinner :
      Real.exp (-(Aold ^ τ)) * weightedLinearExpKernelConst w (ρ ^ τ) ≤
        Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ τ) :=
    mul_le_mul_of_nonneg_right hexp hkernel_nonneg
  exact htop_old.trans
    (mul_le_mul_of_nonneg_left hinner (by positivity))

/-- Crude-bottom component rewritten with the corrected finite bad-scale
exponent.  This is the deterministic conversion of the crude
`sigma * t` endpoint into the common finite exponent. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_component_bound
    {d : ℕ} [NeZero d] {σ Ccrude : ℝ}
    (hσ_pos : 0 < σ) (hCcrude : 0 < Ccrude)
    {params : QuantitativeCoarseGrainedEllipticityParams d}
    (hcomponent :
      ∀ {Centry a t αbad : ℝ},
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
          let L : ℝ :=
            (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
          let w : ℝ := ((3 ^ d : ℕ) : ℝ)
          let Aold : ℝ :=
            (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
              (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
          let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
          0 < a →
          0 < t →
          αbad < t →
          1 ≤ Aold →
          P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
            ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
              (Real.exp (-(Aold ^ σ)) *
                weightedGeometricExpKernelConst w (ρ ^ σ))) :
      ∀ {Centry a t αbad Den : ℝ},
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
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
        0 < a →
        0 < t →
        αbad < t →
        0 < Den →
        Dcrude ^ σ ≤ Den ^ η →
        1 ≤ A →
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ σ)) := by
  intro Centry a t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ha ht hαt hDen hDen_crude hA_one
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
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let Aold : ℝ :=
    (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hDcrude_pos : 0 < Dcrude := by
    dsimp [Dcrude]
    exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hΓ.thetaHat_pos 2)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDen.le
  have hAold_nonneg : 0 ≤ Aold := by
    dsimp [Aold]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDcrude_pos.le
  let X : ℝ := η * ((q : ℝ) - (σ * t * (L + 1)) / η)
  let Y : ℝ := σ * (t * (q : ℝ) - t * (L + 1))
  have hXY : X ≤ Y := by
    have hmain :=
      finiteQuenchedTailExponent_mul_nat_le_sigma_mul_t_nat
        (d := d) (σ := σ) (t := t) (q := q)
        hσ_pos ht
    have hmain' : η * (q : ℝ) ≤ σ * t * (q : ℝ) := by
      simpa [η, mul_assoc] using hmain
    dsimp [X, Y]
    field_simp [hη_pos.ne']
    ring_nf
    nlinarith
  have hA_to_old : A ^ η ≤ Aold ^ σ := by
    have hgeneric :=
      rpow_three_div_den_rpow_le_of_exponent_le
        (X := X) (Y := Y) (D := Dcrude) (Den := Den)
        (η := η) (γ := σ)
        hη_pos hσ_pos hDcrude_pos hDen
        (by simpa [Dcrude, η] using hDen_crude) hXY
    convert hgeneric using 1
    · dsimp [A, X]
      congr 2
      field_simp [hη_pos.ne']
    · dsimp [Aold, Y]
      congr 2
      field_simp [hσ_pos.ne']
  have hAold_one : 1 ≤ Aold := by
    have hA_pow_one : 1 ≤ A ^ η := Real.one_le_rpow hA_one hη_pos.le
    exact one_le_of_one_le_rpow hAold_nonneg hσ_pos (hA_pow_one.trans hA_to_old)
  have hcrude_old :
      P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
          (Real.exp (-(Aold ^ σ)) *
            weightedGeometricExpKernelConst w (ρ ^ σ)) := by
    have hold :=
      hcomponent (Centry := Centry) (a := a) (t := t) (αbad := αbad)
        hP hStruct hΓ hσ_eq hparams (q := q)
    simpa [K, N0, Hshift, S, L, w, Aold, ρ, Dcrude, mul_assoc] using
      hold ha ht hαt hAold_one
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
  have hkernel_nonneg :
      0 ≤ weightedGeometricExpKernelConst w (ρ ^ σ) :=
    (weightedGeometricExpKernelConst_pos
      (w := w) (R := ρ ^ σ) hw_pos
      (Real.one_lt_rpow hρ_gt hσ_pos)).le
  have htail_factor_nonneg :
      0 ≤ ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) := by
    positivity
  have hexp :
      Real.exp (-(Aold ^ σ)) ≤ Real.exp (-(A ^ η)) :=
    Real.exp_le_exp.mpr (by linarith [hA_to_old])
  have hinner :
      Real.exp (-(Aold ^ σ)) * weightedGeometricExpKernelConst w (ρ ^ σ) ≤
        Real.exp (-(A ^ η)) * weightedGeometricExpKernelConst w (ρ ^ σ) :=
    mul_le_mul_of_nonneg_right hexp hkernel_nonneg
  exact hcrude_old.trans
    (mul_le_mul_of_nonneg_left hinner htail_factor_nonneg)

/-- Public crude-bottom component bound with its tail parameter rewritten in
terms of the corrected finite exponent. -/
theorem measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad Den : ℝ},
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
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (σ * t * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (t - αbad)
        0 < a →
        0 < t →
        αbad < t →
        0 < Den →
        Dcrude ^ σ ≤ Den ^ η →
        1 ≤ A →
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ σ)) := by
  obtain ⟨Ccrude, hCcrude, hcomponent⟩ :=
    measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ha ht hαt hDen hDen_crude hA_one
  exact
    measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_kernel_of_component_bound
      (d := d) (σ := σ) (Ccrude := Ccrude) hσ_pos hCcrude
      (by
        intro Centry a t αbad P hP hStruct hΓ hσ_eq' hparams' q
        exact hcomponent (Centry := Centry) (a := a) (t := t)
          (αbad := αbad) hP hStruct hΓ hσ_eq' hparams' (q := q))
      (Centry := Centry) (a := a) (t := t) (αbad := αbad)
      (Den := Den) hP hStruct hΓ hσ_eq hparams (q := q)
      ha ht hαt hDen hDen_crude hA_one

/-- High-bottom component bound with the concrete mixed denominator selected. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_weighted_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
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
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        t ≤ b →
        αbad < t →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * (Cpref * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ η)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hcomponent⟩ :=
    measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_interpolated_weighted_kernel_of_denominator
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hαt hA_one
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
  let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      mixedBottomTailDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
  have hDen_bounds :=
    branch_denominator_le_mixedBottomTailDenominator_pow_eta
      (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
      hη_pos hτ_pos hσ_pos hDhigh_pos hDcrude_pos
  simpa [K, N0, Hshift, S, b, L, τ, η, w, Dhigh, Dcrude, Den, A, ρ,
    Cpref] using
    hcomponent (t := t) (αbad := αbad) (Den := Den)
      hP hStruct hΓ hσ_eq hparams (q := q)
      ht htb hαt hDen_pos hDen_bounds.1 hDen_bounds.2 hA_one

end

end Section57
end Ch05
end Book
end Homogenization
