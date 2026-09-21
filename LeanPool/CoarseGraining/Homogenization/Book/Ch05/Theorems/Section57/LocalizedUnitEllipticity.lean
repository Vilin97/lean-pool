/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteSupTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LimitNormalization
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

/-! # Localized Unit Ellipticity -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# Localized limiting-normalized unit ellipticity

This file gives the stationarity transfer and finite-sup tail bound for the
unit-cube ellipticity observable normalized by the limiting scalar matrix.
-/

noncomputable section

theorem aemeasurable_limitWeightedUnitEllipticityObservableOnCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) {sUpper sLower : ℝ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) :
    AEMeasurable
      (limitWeightedUnitEllipticityObservableOnCube hP hStruct
        Q sUpper sLower) P := by
  exact
    ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q hsUpper).const_mul
      (barSigmaLimit hP hStruct)⁻¹).add
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hsLower).const_mul
        (barSigmaLimit hP hStruct))

/-- The localized limiting-normalized unit ellipticity observable has the same
law as the origin observable on every scale-zero cube. -/
theorem map_limitWeightedUnitEllipticityObservableOnCube_eq_origin_of_scale_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {U : TriadicCube d} (hUscale : U.scale = 0)
    {sUpper sLower : ℝ} (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) :
    Measure.map
        (limitWeightedUnitEllipticityObservableOnCube hP hStruct U
          sUpper sLower) P =
      Measure.map
        (limitWeightedUnitEllipticityObservable hP hStruct sUpper sLower) P := by
  classical
  let L : ℝ := barSigmaLimit hP hStruct
  let X0 : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct sUpper sLower
  let XU : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservableOnCube hP hStruct U sUpper sLower
  have hX0_aemeas : AEMeasurable X0 P := by
    simpa [X0] using
      aemeasurable_limitWeightedUnitEllipticityObservableOnCube
        hP hStruct (originCube d 0) hsUpper hsLower
  let z : Fin d → ℤ := Ch04.scaleTranslationShift 0 U
  have hUeq : U = translateCube z (originCube d 0) := by
    simpa [z] using
      (Section52.translateCube_originCube_zero_eq_of_scale_zero U hUscale).symm
  have hΛae :
      (fun a : RegCoeffField d => Ch04.LambdaSqCoeffField U sUpper (.finite 1) a)
        =ᵐ[P]
      fun a => Ch04.LambdaSqCoeffField (originCube d 0) sUpper (.finite 1)
        (translateReg (intVecToRealVec z) a) := by
    have hcov :=
      Ch04.LambdaSqCoeffField_originCube_zero_translateByInt_ae
        hP hStruct.stationary z sUpper (.finite 1)
    simpa [hUeq] using hcov
  have hlambdaAe :
      (fun a : RegCoeffField d => Ch04.lambdaSqCoeffField U sLower (.finite 1) a)
        =ᵐ[P]
      fun a => Ch04.lambdaSqCoeffField (originCube d 0) sLower (.finite 1)
        (translateReg (intVecToRealVec z) a) := by
    have hcov :=
      Ch04.lambdaSqCoeffField_originCube_zero_translateByInt_ae
        hP hStruct.stationary z sLower (.finite 1)
    simpa [hUeq] using hcov
  have hae :
      XU =ᵐ[P] fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a) := by
    filter_upwards [hΛae, hlambdaAe] with a hΛ hlambda
    dsimp [XU, X0, limitWeightedUnitEllipticityObservableOnCube,
      limitWeightedUnitEllipticityObservable, L]
    rw [hΛ, hlambda]
  calc
    Measure.map XU P =
        Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
          Measure.map_congr hae
    _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
          symm
          exact AEMeasurable.map_map_of_aemeasurable
            (by simpa [hStruct.stationary z] using hX0_aemeas)
            (measurable_translateReg (intVecToRealVec z)).aemeasurable
    _ = Measure.map X0 P := by
          rw [hStruct.stationary z]
    _ = Measure.map
        (limitWeightedUnitEllipticityObservable hP hStruct sUpper sLower) P := by
          rfl

/-- The Γσ tail of the limiting-normalized unit ellipticity observable
transfers to every scale-zero cube. -/
theorem isBigO_limitWeightedUnitEllipticityObservableOnCube_of_scale_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {U : TriadicCube d} (hUscale : U.scale = 0) :
    IsBigO P (gammaSigma hΓ.sigma)
      (limitWeightedUnitEllipticityObservableOnCube hP hStruct U
        hΓ.params.sUpper hΓ.params.sLower)
      (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat) := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hmap :=
    map_limitWeightedUnitEllipticityObservableOnCube_eq_origin_of_scale_zero
      hP hStruct hUscale hΓ.sUpper_pos hΓ.sLower_pos
  have hXU_aemeas :
      AEMeasurable
        (limitWeightedUnitEllipticityObservableOnCube hP hStruct U
          hΓ.params.sUpper hΓ.params.sLower) P :=
    aemeasurable_limitWeightedUnitEllipticityObservableOnCube
      hP hStruct U hΓ.sUpper_pos hΓ.sLower_pos
  have hX0_aemeas :
      AEMeasurable
        (limitWeightedUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower) P := by
    simpa using
      aemeasurable_limitWeightedUnitEllipticityObservableOnCube
        hP hStruct (originCube d 0) hΓ.sUpper_pos hΓ.sLower_pos
  exact
    (Ch04.isBigO_gammaSigma_iff_of_map_eq_map_aemeasurable
      (μ := P) (σ := hΓ.sigma)
      (A := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat)
      hXU_aemeas hX0_aemeas hmap).2
      (by simpa using hΓ.limitWeightedUnitEllipticityObservable_isBigO)

/-- Scale-zero descendant supremum of the limiting-normalized unit ellipticity
inside `\cu_m`. -/
noncomputable def localizedLimitWeightedUnitEllipticitySup
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d) (m : ℕ) :
    RegCoeffField d → ℝ :=
  fun a =>
    let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
    let D : Finset (TriadicCube d) := descendantsAtScale Q 0
    let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube])
    D.sup' hD (fun U =>
      limitWeightedUnitEllipticityObservableOnCube hP hStruct U
        params.sUpper params.sLower a)

/-- A collapsed bound on the localized limiting-normalized unit ellipticity
supremum controls the Ch2 upper and lower unit-ellipticity suprema at any
larger exponent. -/
theorem scaleZero_ellipticity_sup_bounds_of_localizedLimitWeightedUnitEllipticitySup_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {t M : ℝ}
    (hUpper_t : hΓ.params.sUpper < t)
    (hLower_t : hΓ.params.sLower < t)
    (hsup :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        M ^ (2 : ℕ)) :
    let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ);
    let D : Finset (TriadicCube d) := descendantsAtScale Q 0;
    let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube]);
    let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha;
    (barSigmaLimit hP hStruct)⁻¹ *
          D.sup' hD (fun U => Ch02.LambdaSq U t (.finite 1) F) ≤
        M ^ (2 : ℕ) ∧
      barSigmaLimit hP hStruct *
          D.sup' hD (fun U => (Ch02.lambdaSq U t (.finite 1) F)⁻¹) ≤
        M ^ (2 : ℕ) := by
  classical
  intro Q D hD F
  let L : ℝ := barSigmaLimit hP hStruct
  let Obs : TriadicCube d → ℝ := fun U =>
    limitWeightedUnitEllipticityObservableOnCube hP hStruct U
      hΓ.params.sUpper hΓ.params.sLower a
  have hL_pos : 0 < L := by
    simpa [L] using hΓ.barSigmaLimit_pos
  have hL_inv_pos : 0 < L⁻¹ := inv_pos.mpr hL_pos
  have hloc :
      D.sup' hD Obs ≤ M ^ (2 : ℕ) := by
    simpa [localizedLimitWeightedUnitEllipticitySup, Q, D, hD, Obs] using hsup
  have hupperPoint :
      ∀ U ∈ D, L⁻¹ * Ch02.LambdaSq U t (.finite 1) F ≤ Obs U := by
    intro U hU
    have hΛ_eq :
        Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a =
          Ch02.LambdaSq U hΓ.params.sUpper (.finite 1) F := by
      simp [Ch04.LambdaSqCoeffField, F, ha]
    have hΛ_mono :
        Ch02.LambdaSq U t (.finite 1) F ≤
          Ch02.LambdaSq U hΓ.params.sUpper (.finite 1) F :=
      Ch02.LambdaSq_finite_antitone U F hΓ.sUpper_pos hUpper_t
        (by norm_num : (1 : ℝ) ≤ 1)
    have hupper_nonneg :
        0 ≤ Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a :=
      Ch04.LambdaSqCoeffField_finite_nonneg U a hΓ.sUpper_pos
        (by norm_num : (1 : ℝ) ≤ 1)
    have hlower_nonneg :
        0 ≤
          (Ch04.lambdaSqCoeffField U hΓ.params.sLower (.finite 1) a)⁻¹ :=
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg U a hΓ.sLower_pos
          (by norm_num : (1 : ℝ) ≤ 1))
    calc
      L⁻¹ * Ch02.LambdaSq U t (.finite 1) F
          ≤ L⁻¹ * Ch02.LambdaSq U hΓ.params.sUpper (.finite 1) F :=
            mul_le_mul_of_nonneg_left hΛ_mono hL_inv_pos.le
      _ =
          L⁻¹ * Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a := by
            rw [hΛ_eq]
      _ ≤
          L⁻¹ * Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a +
            L * (Ch04.lambdaSqCoeffField U hΓ.params.sLower (.finite 1) a)⁻¹ := by
            exact le_add_of_nonneg_right (mul_nonneg hL_pos.le hlower_nonneg)
      _ = Obs U := by
            simp [Obs, limitWeightedUnitEllipticityObservableOnCube, L]
  have hlowerPoint :
      ∀ U ∈ D, L * (Ch02.lambdaSq U t (.finite 1) F)⁻¹ ≤ Obs U := by
    intro U hU
    have hlambda_eq :
        Ch04.lambdaSqCoeffField U hΓ.params.sLower (.finite 1) a =
          Ch02.lambdaSq U hΓ.params.sLower (.finite 1) F := by
      simp [Ch04.lambdaSqCoeffField, F, ha]
    have hlambda_mono :
        Ch02.lambdaSq U hΓ.params.sLower (.finite 1) F ≤
          Ch02.lambdaSq U t (.finite 1) F :=
      Ch02.lambdaSq_finite_mono U F hΓ.sLower_pos hLower_t
        (by norm_num : (1 : ℝ) ≤ 1)
    have hlambda_lower_pos :
        0 < Ch02.lambdaSq U hΓ.params.sLower (.finite 1) F :=
      Ch02.lambdaSq_finite_pos U F hΓ.sLower_pos
        (by norm_num : (1 : ℝ) ≤ 1)
    have hinv_le :
        (Ch02.lambdaSq U t (.finite 1) F)⁻¹ ≤
          (Ch02.lambdaSq U hΓ.params.sLower (.finite 1) F)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlambda_lower_pos hlambda_mono
    have hupper_nonneg :
        0 ≤ Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a :=
      Ch04.LambdaSqCoeffField_finite_nonneg U a hΓ.sUpper_pos
        (by norm_num : (1 : ℝ) ≤ 1)
    calc
      L * (Ch02.lambdaSq U t (.finite 1) F)⁻¹
          ≤ L * (Ch02.lambdaSq U hΓ.params.sLower (.finite 1) F)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv_le hL_pos.le
      _ =
          L * (Ch04.lambdaSqCoeffField U hΓ.params.sLower (.finite 1) a)⁻¹ := by
            rw [hlambda_eq]
      _ ≤
          L⁻¹ * Ch04.LambdaSqCoeffField U hΓ.params.sUpper (.finite 1) a +
            L * (Ch04.lambdaSqCoeffField U hΓ.params.sLower (.finite 1) a)⁻¹ := by
            exact le_add_of_nonneg_left
              (mul_nonneg hL_inv_pos.le hupper_nonneg)
      _ = Obs U := by
            simp [Obs, limitWeightedUnitEllipticityObservableOnCube, L]
  have hupperScaled :
      L⁻¹ * D.sup' hD (fun U => Ch02.LambdaSq U t (.finite 1) F) ≤
        D.sup' hD Obs := by
    rw [Finset.mul₀_sup' hL_inv_pos.le
      (fun U => Ch02.LambdaSq U t (.finite 1) F) D hD]
    exact Finset.sup'_le hD _ fun U hU =>
      (hupperPoint U hU).trans (Finset.le_sup' (f := Obs) hU)
  have hlowerScaled :
      L * D.sup' hD (fun U => (Ch02.lambdaSq U t (.finite 1) F)⁻¹) ≤
        D.sup' hD Obs := by
    rw [Finset.mul₀_sup' hL_pos.le
      (fun U => (Ch02.lambdaSq U t (.finite 1) F)⁻¹) D hD]
    exact Finset.sup'_le hD _ fun U hU =>
      (hlowerPoint U hU).trans (Finset.le_sup' (f := Obs) hU)
  exact ⟨hupperScaled.trans hloc, hlowerScaled.trans hloc⟩

theorem measureReal_localizedLimitWeightedUnitEllipticitySup_tail_le_card_mul_exp
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (m : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) :
    let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ);
    let D : Finset (TriadicCube d) := descendantsAtScale Q 0;
    P.real
        {a : RegCoeffField d |
          (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat) * lam <
            localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a} ≤
      (D.card : ℝ) * Real.exp (-(lam ^ hΓ.sigma)) := by
  classical
  intro Q D
  let : IsProbabilityMeasure P := hP.isProbability
  let A : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U =>
      limitWeightedUnitEllipticityObservableOnCube hP hStruct U
        hΓ.params.sUpper hΓ.params.sLower
  let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube])
  have hX :
      ∀ U ∈ D, IsBigO P (gammaSigma hΓ.sigma) (X U) A := by
    intro U hU
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    simpa [X, A] using
      isBigO_limitWeightedUnitEllipticityObservableOnCube_of_scale_zero
        hP hStruct hΓ hUscale
  simpa [localizedLimitWeightedUnitEllipticitySup, Q, D, hD, A, X] using
    measureReal_finiteSup_tail_le_card_mul_exp_of_isBigO
      (μ := P) (s := D) (hs := hD) (X := X)
      (A := A) (lam := lam) (σ := hΓ.sigma) hlam hX

end

end Section57
end Ch05
end Book
end Homogenization
