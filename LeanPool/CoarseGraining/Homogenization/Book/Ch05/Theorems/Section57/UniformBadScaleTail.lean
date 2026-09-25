/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointSynchronized
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailAssembly

/-! # Uniform Bad Scale Tail -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Uniform endpoint bad-scale tail

This file assembles the `Γ∞` endpoint bad-scale estimate with synchronized
constants.  The endpoint exponent is `d`, not the finite-`σ` interpolation.
-/

noncomputable section

/-- Endpoint high-top component estimate with the raw high bad-pair bound
supplied externally. -/
theorem measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity_of_badPair_bound
    {d : ℕ} [NeZero d] {Cfluct Centry a : ℝ}
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (_hCentry : 0 < Centry) (ha : 0 < a)
    (hraw :
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
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        0 < Den →
        Dhigh ^ (2 : ℝ) ≤ Den ^ η →
        1 ≤ A →
        P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
          (S.card : ℝ) *
            (Real.exp (-(A ^ η)) *
              weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))) := by
  intro t αbad Den P hP hStruct hInf hparams q
  dsimp only
  intro ht hαt hαb hαharm hDen hDen_high hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let hΓ2 := hInf.toGammaSigma 2 (by norm_num : (0 : ℝ) < 2)
  have hΓ2_params : hΓ2.params = params := by
    simpa [hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using hparams
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
  let ctop : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Aold : ℝ :=
    (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) / Dhigh
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hDhigh_pos : 0 < Dhigh := by
    dsimp [Dhigh]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
      (pow_pos hInf.thetaHat_pos 2)
  have hAold_nonneg : 0 ≤ Aold := by
    dsimp [Aold]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDhigh_pos.le
  let X : ℝ := η * ((q : ℝ) - (L + 1))
  let Y : ℝ := (2 : ℝ) * (b * (q : ℝ) - b * (L + 1))
  have hXY : X ≤ Y := by
    dsimp [X, Y, η, b]
    ring_nf
    exact le_rfl
  have hA_to_old : A ^ η ≤ Aold ^ (2 : ℝ) := by
    have hgeneric :=
      rpow_three_div_den_rpow_le_of_exponent_le
        (X := X) (Y := Y) (D := Dhigh) (Den := Den)
        (η := η) (γ := (2 : ℝ))
        hη_pos (by norm_num : (0 : ℝ) < (2 : ℝ))
        hDhigh_pos hDen
        (by simpa [Dhigh, η] using hDen_high) hXY
    have hX_div : X / η = (q : ℝ) - (L + 1) := by
      dsimp [X]
      field_simp [hη_pos.ne']
    have hY_div : Y / (2 : ℝ) = b * (q : ℝ) - b * (L + 1) := by
      dsimp [Y]
      norm_num
    have hA_eq : A = (3 : ℝ) ^ (X / η) / Den := by
      dsimp [A]
      rw [hX_div]
    have hAold_eq : Aold = (3 : ℝ) ^ (Y / (2 : ℝ)) / Dhigh := by
      dsimp [Aold]
      rw [hY_div]
    simpa [hA_eq, hAold_eq] using hgeneric
  have hAold_one : 1 ≤ Aold := by
    have hA_pow_one : 1 ≤ A ^ η := Real.one_le_rpow hA_one hη_pos.le
    exact one_le_of_one_le_rpow hAold_nonneg
      (by norm_num : (0 : ℝ) < (2 : ℝ)) (hA_pow_one.trans hA_to_old)
  have htop_old :
      P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
        (S.card : ℝ) *
          (Real.exp (-(Aold ^ (2 : ℝ))) *
            weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))) := by
    have htop :=
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_badPair_bound
        (d := d) (σ := (2 : ℝ)) (Cfluct := Cfluct)
        (Centry := Centry) (a := a)
        (by norm_num : (0 : ℝ) < (2 : ℝ))
        params hCfluct _hCentry ha hraw
        (t := t) (αbad := αbad)
        hP hStruct hΓ2 rfl hΓ2_params (q := q)
    simpa [K, N0, Hshift, S, b, L, ctop, η, w, Dhigh, Aold, ρtop,
      hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using!
      htop ht hαt hαb hαharm hAold_one
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hc_pos : 0 < ctop := by
    have hgap : 0 < t - αbad := sub_pos.mpr hαt
    have hbα : 0 < b - αbad := sub_pos.mpr hαb
    have hfactor : 0 < 1 + b / a := by positivity
    have hthird : 0 < (t - αbad) * (1 + b / a) :=
      mul_pos hgap hfactor
    have hfourth : 0 < b - αbad * (1 + b / a) :=
      sub_pos.mpr hαharm
    dsimp [ctop]
    exact lt_min hgap (lt_min hbα (lt_min hthird hfourth))
  have hρ_gt : 1 < ρtop := by
    dsimp [ρtop]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ ctop :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hc_pos
  have hkernel_nonneg :
      0 ≤ weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ)) :=
    (weightedLinearExpKernelConst_pos
      (w := w) (R := ρtop ^ (2 : ℝ)) hw_pos
      (Real.one_lt_rpow hρ_gt (by norm_num : (0 : ℝ) < (2 : ℝ)))).le
  have hexp :
      Real.exp (-(Aold ^ (2 : ℝ))) ≤ Real.exp (-(A ^ η)) :=
    Real.exp_le_exp.mpr (by linarith [hA_to_old])
  have hinner :
      Real.exp (-(Aold ^ (2 : ℝ))) *
          weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ)) ≤
        Real.exp (-(A ^ η)) *
          weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hexp hkernel_nonneg
  exact htop_old.trans
    (mul_le_mul_of_nonneg_left hinner (by positivity))

/-- Synchronized endpoint bad-scale component sum before deterministic
threshold selection. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_component_sum
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
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
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let Acrude : ℝ := (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) ≤ Den ^ η →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        1 ≤ A →
        1 ≤ Acrude →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        P.real (badScaleEvent Hshift t αbad q) ≤
          (S.card : ℝ) *
              (Real.exp (-(A ^ η)) *
                weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))) +
            ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
              (Real.exp (-(A ^ η)) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hhighRaw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := (2 : ℝ)) (by norm_num) params
  obtain ⟨Ccrude, hCcrude, hzeroRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_eq_zero_of_gammaInfinity
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Den P hP hStruct hInf hparams q
  dsimp only
  intro ht hα_nonneg hαt hαb hαharm hαa htb hDen
    hDen_top hDen_bottom hA_one hAcrude_one hq_large
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
  let ctop : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let Acrude : ℝ := (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have htop :
      P.real (highTopBadScaleEvent Hshift K a t αbad q) ≤
        (S.card : ℝ) *
          (Real.exp (-(A ^ η)) *
            weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))) := by
    simpa [K, N0, Hshift, S, b, L, ctop, η, w, Dhigh, A, ρtop] using
      measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity_of_badPair_bound
        (d := d) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        params hCfluct hCentry ha hhighRaw
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hInf hparams (q := q)
        ht hαt hαb hαharm hDen hDen_top hA_one
  have hbottom :
      P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
        ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
          (Real.exp (-(A ^ η)) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)) := by
    simpa [K, N0, Hshift, S, b, L, η, w, Dhigh, Dcrude, A, ρbottom,
      Cbottom] using
      measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity_of_row_bound
        (d := d) (Cfluct := Cfluct) (Ccrude := Ccrude)
        (Centry := Centry) (a := a) params
        (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity_of_bounds
          (d := d) (Cfluct := Cfluct) (Ccrude := Ccrude)
          (Centry := Centry) (a := a)
          params hCfluct hCcrude hCentry ha
          (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high_gammaInfinity_of_badPair_bound
            (d := d) (Cfluct := Cfluct) (Centry := Centry) (a := a)
            params hCfluct hCentry ha hhighRaw)
          (measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_eq_zero_of_crudeA_one_gammaInfinity_of_badPair_zero
            (d := d) (Ccrude := Ccrude) params hCcrude hzeroRaw))
        (t := t) (αbad := αbad) (Den := Den)
        hP hStruct hInf hparams (q := q)
        ht hαt htb hDen hDen_bottom hA_one
  have hcrude :
      P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) ≤ 0 := by
    have hz :
        P.real (crudeBottomBadScaleEvent Hshift K a t αbad q) = 0 := by
      simpa [K, N0, Hshift, L, Acrude, Dcrude] using
        (measureReal_shiftedCrudeBottomBadScaleEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity_of_pair_zero
          (d := d) (Ccrude := Ccrude) params
          (measureReal_shiftedCrudeBottomPairEvent_quenchedProbeEnvelope_eq_zero_gammaInfinity_of_badPair_zero
            (d := d) (Ccrude := Ccrude) params hCcrude hzeroRaw))
          hP hStruct hInf hparams (q := q) ha ht hαt hAcrude_one
    rw [hz]
  have hsum :=
    measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (Rht :=
        (S.card : ℝ) *
          (Real.exp (-(A ^ η)) *
            weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))))
      (Rhb :=
        ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
          (Real.exp (-(A ^ η)) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)))
      (Rcb := 0)
      ha hα_nonneg hαt hαa
      (by simpa [K, L] using hq_large)
      htop hbottom hcrude
  linarith

/-- Endpoint component sum after selecting the common high denominator.  The
crude-bottom cutoff remains an explicit deterministic side condition. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_selected_denominator
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
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
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let Acrude : ℝ := (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        1 ≤ A →
        1 ≤ Acrude →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        P.real (badScaleEvent Hshift t αbad q) ≤
          (S.card : ℝ) *
              (Real.exp (-(A ^ η)) *
                weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))) +
            ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
              (Real.exp (-(A ^ η)) *
                weightedGeometricExpKernelConst w (ρbottom ^ η)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hcomp⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_component_sum
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hInf hparams q
  dsimp only
  intro ht hα_nonneg hαt hαb hαharm hαa htb hA_one hAcrude_one hq_large
  let K : ℝ := quenchedProbeEnvelopeConst d
  let b : ℝ := (d : ℝ) / 2
  let η : ℝ := ((d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
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
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      uniformEndpointHighDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
  have hη_one : 1 ≤ η := by
    dsimp [η]
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
  have hDen_top :
      Dhigh ^ (2 : ℝ) ≤ Den ^ η := by
    simpa [Den, η] using
      uniformEndpointHighDenominator_dom_top
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
        hDhigh_pos.le ht (by simpa [b, η] using htb) hη_one
  have hDen_bottom :
      Dhigh ^ (2 : ℝ) *
          (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η := by
    simpa [Den, η] using
      uniformEndpointHighDenominator_dom_bottom
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η) hη_one
  simpa [K, b, η, Dhigh, Dcrude, Den] using
    hcomp (t := t) (αbad := αbad) (Den := Den)
      hP hStruct hInf hparams (q := q)
      ht hα_nonneg hαt hαb hαharm hαa htb hDen_pos
      hDen_top hDen_bottom hA_one hAcrude_one hq_large

end

end Section57
end Ch05
end Book
end Homogenization
