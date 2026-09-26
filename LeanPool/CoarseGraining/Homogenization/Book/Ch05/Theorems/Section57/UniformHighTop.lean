/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighBottom
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailDenominator

/-! # Uniform High Top -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# The localized high-top branch at the uniform endpoint

The high-top branch uses the finite `Γ_2` consequence of the uniform endpoint.
Since the localized top exponent is `2 * d / 2`, this branch already has the
endpoint `Γ_d` exponent after a deterministic denominator rewrite.
-/

noncomputable section

/-- Endpoint high-top component estimate after rewriting the localized
`Γ_2` branch with the endpoint exponent `d`. -/
theorem measureReal_shiftedHighTopBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ,
      0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
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
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hraw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := (2 : ℝ)) (by norm_num) params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
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
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hDen.le
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
        params hCfluct hCentry ha hraw
        (t := t) (αbad := αbad)
        hP hStruct hΓ2 rfl hΓ2_params (q := q)
    simpa [K, N0, Hshift, S, b, L, ctop, η, w, Dhigh, Aold, ρtop,
      hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using!
      htop ht hαt hαb hαharm hAold_one
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
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

end

end Section57
end Ch05
end Book
end Homogenization
