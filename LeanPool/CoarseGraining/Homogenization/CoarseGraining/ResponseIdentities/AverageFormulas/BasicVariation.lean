/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations

/-! # Basic Variation -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Average formulas (part 1) -- basic variation and pairing identities

basic_cg_identities_linear_response (sq and linear form), average-pairing
and polarization identities, and the average-gradient / average-flux
coordinate / vector identities for IsResponseMaximizer data.
-/

theorem basic_cg_identities_linear_response_sq_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (w : AHarmonicFunction a U) :
    (volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))) ^ 2 ≤
      volumeAverage U (scalarVariationEnergyIntegrand a w) * (2 * ResponseJ U p q a) := by
  let cross : ℝ :=
    volumeAverage U
      (fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)))
  let energyW : ℝ := volumeAverage U (scalarVariationEnergyIntegrand a w)
  let energyU : ℝ := volumeAverage U (scalarVariationEnergyIntegrand a u)
  have hfirst :
      volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
          volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
        cross := by
    unfold cross
    exact basic_cg_identities_first_variation_eq_of_isResponseMaximizer
      U a p q hInt u hmax w
  have henergyW_nonneg :
      0 ≤ energyW := by
    unfold energyW
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      U a hEll w
  have hquad :
      ∀ t : ℝ, 0 ≤ energyU - 2 * t * cross + t ^ 2 * energyW := by
    intro t
    let udiff :=
      AHarmonicFunction.subOfIntegrable u (t • w) (hInt.weakFlux u) (hInt.weakFlux (t • w))
    have hnonneg :
        0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a udiff) :=
      volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        U a hEll udiff
    have hsplit :=
      volumeAverage_scalarVariationEnergyIntegrand_subOfIntegrable U a hInt u (t • w)
    have hsmul_energy :
        volumeAverage U (scalarVariationEnergyIntegrand a (t • w)) = t ^ 2 * energyW := by
      unfold energyW
      simpa using volumeAverage_scalarVariationEnergyIntegrand_smul U a t w
    have hsmul_cross :
        volumeAverage U
            (fun x => vecDot ((t • w).toH1.grad x)
              (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
          t * cross := by
      unfold cross
      have hfun :
          (fun x => vecDot ((t • w).toH1.grad x)
              (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
            t • fun x => vecDot (w.toH1.grad x)
              (matVecMul (symmPart (a x)) (u.toH1.grad x)) := by
        funext x
        change
          vecDot (t • w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) =
            t * vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))
        rw [vecDot_smul_left]
      rw [hfun, volumeAverage_smul]
    have hnonneg' : 0 ≤ energyU + t ^ 2 * energyW - 2 * (t * cross) := by
      unfold energyU energyW cross
      linarith [hnonneg, hsplit, hsmul_energy, hsmul_cross]
    nlinarith [hnonneg']
  have hcross_sq :
      cross ^ 2 ≤ energyU * energyW := by
    exact sq_le_mul_of_quadratic_nonneg henergyW_nonneg hquad
  have hu_energy :
      ResponseJ U p q a = (1 / 2 : ℝ) * energyU := by
    unfold energyU
    exact responseJ_energy_of_isResponseMaximizer
      U a p q u hmax
      (hInt.weakFlux u) (hInt.response p q u) (hInt.firstVariation p q u u) (hInt.energy u)
  rw [hfirst]
  nlinarith

theorem basic_cg_identities_linear_response_sq_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (w : AHarmonicFunction a U) :
    (volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))) ^ 2 ≤
      volumeAverage U (scalarVariationEnergyIntegrand a w) * (2 * ResponseJ U p q a) :=
  basic_cg_identities_linear_response_sq_of_isResponseMaximizer
    U a hEll p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax w

theorem basic_cg_identities_linear_response_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (w : AHarmonicFunction a U) :
    |volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * ResponseJ U p q a) := by
  have hsq := basic_cg_identities_linear_response_sq_of_isResponseMaximizer
    U a hEll p q hInt u hmax w
  have henergy_nonneg :
      0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      U a hEll w
  have hresp_nonneg : 0 ≤ 2 * ResponseJ U p q a := by
    nlinarith [responseJ_nonneg U p q a]
  have hroot :=
    Real.abs_le_sqrt hsq
  rw [Real.sqrt_mul henergy_nonneg] at hroot
  simpa [mul_assoc, mul_left_comm, mul_comm] using hroot

theorem basic_cg_identities_linear_response_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (w : AHarmonicFunction a U) :
    |volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * ResponseJ U p q a) :=
  basic_cg_identities_linear_response_of_isResponseMaximizer
    U a hEll p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax w

theorem basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a) (w : AHarmonicFunction a U) :
    volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
      vecDot q (fun i => volumeAverage U (fun x => w.toH1.grad x i)) -
        vecDot p (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)) := by
  have hgrad :
      volumeAverage U (fun x => vecDot q (w.toH1.grad x)) =
        vecDot q (fun i => volumeAverage U (fun x => w.toH1.grad x i)) := by
    calc
      volumeAverage U (fun x => vecDot q (w.toH1.grad x))
          = volumeAverage U (fun x => ∑ i, q i * w.toH1.grad x i) := by
              simp [vecDot]
      _ = ∑ i, volumeAverage U (fun x => q i * w.toH1.grad x i) := by
            rw [volumeAverage_sum (U := U) (s := Finset.univ)
              (f := fun i x => q i * w.toH1.grad x i)]
            intro i hi
            have hsingle :
                (fun x => q i * w.toH1.grad x i) =
                  fun x => vecDot (Pi.single i (q i)) (w.toH1.grad x) := by
              funext x
              rw [vecDot, Finset.sum_eq_single i]
              · simp
              · intro j hj hji
                simp [Pi.single_eq_of_ne hji]
              · simp
            rw [hsingle]
            exact hInt.grad (Pi.single i (q i)) w
      _ = ∑ i, q i * volumeAverage U (fun x => w.toH1.grad x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using! (volumeAverage_smul U (q i) (fun x => w.toH1.grad x i))
      _ = vecDot q (fun i => volumeAverage U (fun x => w.toH1.grad x i)) := by
            simp [vecDot]
  have hflux :
      volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
        vecDot p (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)) := by
    calc
      volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
          volumeAverage U (fun x => ∑ i, p i * matVecMul (a x) (w.toH1.grad x) i) := by
              simp [vecDot]
      _ = ∑ i, volumeAverage U (fun x => p i * matVecMul (a x) (w.toH1.grad x) i) := by
            rw [volumeAverage_sum (U := U) (s := Finset.univ)
              (f := fun i x => p i * matVecMul (a x) (w.toH1.grad x) i)]
            intro i hi
            have hsingle :
                (fun x => p i * matVecMul (a x) (w.toH1.grad x) i) =
                  fun x => vecDot (Pi.single i (p i)) (matVecMul (a x) (w.toH1.grad x)) := by
              funext x
              rw [vecDot, Finset.sum_eq_single i]
              · simp
              · intro j hj hji
                simp [Pi.single_eq_of_ne hji]
              · simp
            rw [hsingle]
            exact hInt.flux (Pi.single i (p i)) w
      _ = ∑ i, p i * volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using!
              (volumeAverage_smul U (p i) (fun x => matVecMul (a x) (w.toH1.grad x) i))
      _ = vecDot p (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)) := by
            simp [vecDot]
  rw [hgrad, hflux]

theorem
    basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux_of_isEllipticFieldOn
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (w : AHarmonicFunction a U) :
    volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
      vecDot q (fun i => volumeAverage U (fun x => w.toH1.grad x i)) -
        vecDot p (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)) :=
  basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
    U a p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w

theorem basic_cg_identities_polarization_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q p' q' : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u u' : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmax' : IsResponseMaximizer U p' q' a u') :
    volumeAverage U
        (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a := by
  let udiff := AHarmonicFunction.subOfIntegrable u u' (hInt.weakFlux u) (hInt.weakFlux u')
  have hmax_diff :=
    basic_cg_identities_sub_isResponseMaximizer_of_isResponseMaximizer
      U a p q p' q' hInt u u' hmax hmax'
  have hu_energy :=
    responseJ_energy_of_isResponseMaximizer U a p q u hmax
      (hInt.weakFlux u) (hInt.response p q u) (hInt.firstVariation p q u u) (hInt.energy u)
  have hu'_energy :=
    responseJ_energy_of_isResponseMaximizer U a p' q' u' hmax'
      (hInt.weakFlux u') (hInt.response p' q' u') (hInt.firstVariation p' q' u' u')
      (hInt.energy u')
  have hdiff_energy :=
    responseJ_energy_of_isResponseMaximizer U a (p - p') (q - q') udiff hmax_diff
      (hInt.weakFlux udiff) (hInt.response (p - p') (q - q') udiff)
      (hInt.firstVariation (p - p') (q - q') udiff udiff) (hInt.energy udiff)
  have hsplit := volumeAverage_scalarVariationEnergyIntegrand_subOfIntegrable U a hInt u u'
  linarith [hu_energy, hu'_energy, hdiff_energy, hsplit]

theorem basic_cg_identities_polarization_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q p' q' : Vec d)
    (u u' : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmax' : IsResponseMaximizer U p' q' a u') :
    volumeAverage U
        (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a :=
  basic_cg_identities_polarization_of_isResponseMaximizer
    U a p q p' q' (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u u' hmax hmax'

theorem basic_cg_identities_average_pairing_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q p' q' : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u u' : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmax' : IsResponseMaximizer U p' q' a u') :
    volumeAverage U (fun x => vecDot q' (u.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p' (matVecMul (a x) (u.toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a := by
  have hfirst :=
    basic_cg_identities_first_variation_eq_of_isResponseMaximizer
      U a p' q' hInt u' hmax' u
  have hsymm :
      volumeAverage U
          (fun x => vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u'.toH1.grad x))) =
        volumeAverage U
          (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
    refine congrArg (volumeAverage U) ?_
    funext x
    exact vecDot_matVecMul_symmPart_comm (a x) (u.toH1.grad x) (u'.toH1.grad x)
  calc
    volumeAverage U (fun x => vecDot q' (u.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p' (matVecMul (a x) (u.toH1.grad x))) =
      volumeAverage U
        (fun x => vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u'.toH1.grad x))) := hfirst
    _ = volumeAverage U
        (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := hsymm
    _ = ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a :=
      basic_cg_identities_polarization_of_isResponseMaximizer
        U a p q p' q' hInt u u' hmax hmax'

theorem basic_cg_identities_average_pairing_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q p' q' : Vec d)
    (u u' : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmax' : IsResponseMaximizer U p' q' a u') :
    volumeAverage U (fun x => vecDot q' (u.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p' (matVecMul (a x) (u.toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a :=
  basic_cg_identities_average_pairing_of_isResponseMaximizer
    U a p q p' q' (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u u' hmax hmax'

theorem basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (i : Fin d) (u' : AHarmonicFunction a U)
    (hmax' : IsResponseMaximizer U 0 (Pi.single i 1) a u') :
    volumeAverage U (fun x => u.toH1.grad x i) =
      ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a := by
  have hpair :
      volumeAverage U (fun x => u.toH1.grad x i) -
          volumeAverage U (fun x => (0 : ℝ)) =
        ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
          ResponseJ U p (q - Pi.single i 1) a := by
    simpa [vecDot_single_left, vecDot_zero_left, sub_eq_add_neg] using
      basic_cg_identities_average_pairing_of_isResponseMaximizer
        U a p q 0 (Pi.single i 1) hInt u u' hmax hmax'
  have hzero : volumeAverage U (fun x => (0 : ℝ)) = 0 := by
    unfold volumeAverage
    simp
  simpa [hzero, sub_eq_add_neg] using hpair

theorem basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (i : Fin d) (u' : AHarmonicFunction a U)
    (hmax' : IsResponseMaximizer U 0 (Pi.single i 1) a u') :
    volumeAverage U (fun x => u.toH1.grad x i) =
      ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a :=
  basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer
    U a p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax i u' hmax'

theorem basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (i : Fin d) (u' : AHarmonicFunction a U)
    (hmax' : IsResponseMaximizer U (Pi.single i 1) 0 a u') :
    volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i) =
      ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a := by
  have hpair :=
    basic_cg_identities_average_pairing_of_isResponseMaximizer
      U a p q (Pi.single i 1) 0 hInt u u' hmax hmax'
  have hpair' :
      volumeAverage U (fun x => (0 : ℝ)) -
          volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i) =
        ResponseJ U p q a + ResponseJ U (Pi.single i 1) 0 a -
          ResponseJ U (p - Pi.single i 1) q a := by
    simpa [vecDot_single_left, vecDot_zero_left, sub_eq_add_neg] using hpair
  have hzero : volumeAverage U (fun x => (0 : ℝ)) = 0 := by
    unfold volumeAverage
    simp
  have hpair'' :
      -volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i) =
        ResponseJ U p q a + ResponseJ U (Pi.single i 1) 0 a -
          ResponseJ U (p - Pi.single i 1) q a := by
    simpa [hzero, sub_eq_add_neg] using hpair'
  linarith

theorem basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (i : Fin d) (u' : AHarmonicFunction a U)
    (hmax' : IsResponseMaximizer U (Pi.single i 1) 0 a u') :
    volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i) =
      ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a :=
  basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer
    U a p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax i u' hmax'

theorem basic_cg_identities_average_gradient_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a := by
  funext i
  exact basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer
    U a p q hInt u hmax i (uGrad i) (hmaxGrad i)

theorem basic_cg_identities_average_gradient_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a :=
  basic_cg_identities_average_gradient_of_isResponseMaximizer
    U a p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax uGrad hmaxGrad

theorem basic_cg_identities_average_flux_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a := by
  funext i
  exact basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer
    U a p q hInt u hmax i (uFlux i) (hmaxFlux i)

theorem basic_cg_identities_average_flux_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a :=
  basic_cg_identities_average_flux_of_isResponseMaximizer
    U a p q (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    u hmax uFlux hmaxFlux

end

end Homogenization
