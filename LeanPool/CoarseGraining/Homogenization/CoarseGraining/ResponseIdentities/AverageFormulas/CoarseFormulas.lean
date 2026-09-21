/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.BasicVariation

/-! # Coarse Formulas -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Average formulas (part 2) -- sigma-coarse formulas

energy-average / responseJ-zero formulas under IsSigmaStarCoarse and
IsSigmaCoarse, their deterministicCoarseBlockMatrix / coarseBlockMatrix
variants, and the corresponding average-gradient / average-flux formula
theorems for IsResponseMaximizer data.
-/

theorem basic_cg_identities_energy_average_gradient_canonical_of_isSigmaStarCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (w : AHarmonicFunction a U)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U 0
      (matVecMul (sigmaStarCoarse U a)
        (fun i => volumeAverage U (fun x => w.toH1.grad x i))) a u) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => w.toH1.grad x i))
          (matVecMul (sigmaStarCoarse U a)
            (fun i => volumeAverage U (fun x => w.toH1.grad x i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  let avgGrad : Vec d := fun i => volumeAverage U (fun x => w.toH1.grad x i)
  let qbar : Vec d := matVecMul (sigmaStarCoarse U a) avgGrad
  have hzero : volumeAverage U (fun _ => (0 : ℝ)) = 0 := volumeAverage_zero U
  have havg :
      volumeAverage U (fun x => vecDot qbar (w.toH1.grad x)) = vecDot qbar avgGrad := by
    have hpair :=
      basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
        U a 0 qbar hInt w
    have hpair' :
        volumeAverage U (fun x => vecDot qbar (w.toH1.grad x)) -
            volumeAverage U (fun _ => (0 : ℝ)) =
          vecDot qbar avgGrad := by
      simpa [avgGrad, qbar, vecDot] using hpair
    linarith
  have hlin :=
    basic_cg_identities_linear_response_of_isResponseMaximizer
      U a hEll 0 qbar hInt u hmax w
  have hSigmaEq : sigmaStarCoarse U a = sigmaStar :=
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet
  have hresp :
      ResponseJ U 0 qbar a =
        (1 / 2 : ℝ) * vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) := by
    rcases hS with ⟨_, hSresp⟩
    have hInvMul : matVecMul sigmaStar⁻¹ (matVecMul sigmaStar avgGrad) = avgGrad := by
      rw [matVecMul_mul, Matrix.nonsing_inv_mul sigmaStar hdet]
      funext i
      simp [matVecMul, Matrix.one_apply]
    unfold qbar
    rw [hSigmaEq, hSresp]
    calc
      (1 / 2 : ℝ) * vecDot (matVecMul sigmaStar avgGrad)
          (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar avgGrad)) =
        (1 / 2 : ℝ) * vecDot (matVecMul sigmaStar avgGrad) avgGrad := by
          rw [hInvMul]
      _ = (1 / 2 : ℝ) * vecDot avgGrad (matVecMul sigmaStar avgGrad) := by
          rw [vecDot_comm]
  have hlin' :
      |vecDot qbar avgGrad| ≤
        Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
          Real.sqrt
            (vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad)) := by
    have hlin0 :
        |volumeAverage U (fun x => vecDot qbar (w.toH1.grad x)) -
            volumeAverage U (fun _ => (0 : ℝ))| ≤
          Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
            Real.sqrt (vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad)) := by
      simpa [hresp, avgGrad, qbar, vecDot, mul_assoc, mul_left_comm, mul_comm] using hlin
    rw [havg, hzero] at hlin0
    simpa using hlin0
  have hquad_nonneg :
      0 ≤ vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) := by
    have hresp_nonneg : 0 ≤ ResponseJ U 0 qbar a := responseJ_nonneg U 0 qbar a
    rw [hresp] at hresp_nonneg
    nlinarith
  have hqbarEq :
      vecDot qbar avgGrad =
        vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) := by
    unfold qbar
    rw [vecDot_comm]
  have henergy_nonneg :
      0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U a hEll w
  have hsq :
      vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) ^ 2 ≤
        volumeAverage U (scalarVariationEnergyIntegrand a w) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) := by
    have hlin'' :
        vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) ≤
          Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
            Real.sqrt (vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad)) := by
      have hlinAbs := hlin'
      rw [hqbarEq] at hlinAbs
      rw [abs_of_nonneg hquad_nonneg] at hlinAbs
      exact hlinAbs
    nlinarith [hlin'', Real.sq_sqrt henergy_nonneg, Real.sq_sqrt hquad_nonneg]
  have hmain :
      vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) ≤
        volumeAverage U (scalarVariationEnergyIntegrand a w) := by
    nlinarith [hsq, hquad_nonneg]
  nlinarith [hmain]

theorem
    basic_cg_identities_energy_average_gradient_canonical_of_isSigmaStarCoarse_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a U)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U 0
      (matVecMul (sigmaStarCoarse U a)
        (fun i => volumeAverage U (fun x => w.toH1.grad x i))) a u) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => w.toH1.grad x i))
          (matVecMul (sigmaStarCoarse U a)
            (fun i => volumeAverage U (fun x => w.toH1.grad x i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) :=
  basic_cg_identities_energy_average_gradient_canonical_of_isSigmaStarCoarse
    U a hEll hS hdet (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
    w u hmax

theorem responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p 0 a = (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
  rcases hSigma with ⟨_, hSigmaResp⟩
  have hp := hSigmaResp p
  have hb :
      vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) =
        vecDot p (matVecMul sigma p) +
          vecDot p (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    unfold bCoarse
    calc
      vecDot p (matVecMul (sigma + matTranspose kappa * sigmaStar⁻¹ * kappa) p)
        = vecDot p (matVecMul sigma p + matVecMul (matTranspose kappa * sigmaStar⁻¹ * kappa) p) := by
            rw [add_matVecMul]
      _ = vecDot p (matVecMul sigma p) +
            vecDot p (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
            rw [vecDot_add_right, matVecMul_mul, matVecMul_mul]
  rw [hb]
  linarith

theorem basic_cg_identities_responseJ_zero_formula_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p 0 a = (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) :=
  responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse hSigma p

theorem basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    basic_cg_identities_responseJ_zero_formula_of_isSigmaCoarse U a hSigma p

theorem basic_cg_identities_energy_average_flux_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (w : AHarmonicFunction a U)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U
      (-matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))
      0 a u) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
            (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  let avgFlux : Vec d := fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)
  let B : Mat d := bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)
  let pbar : Vec d := -matVecMul B⁻¹ avgFlux
  by_cases hBdet : IsUnit B.det
  · have hzero : volumeAverage U (fun _ => (0 : ℝ)) = 0 := volumeAverage_zero U
    have havg :
        volumeAverage U (fun x => vecDot pbar (matVecMul (a x) (w.toH1.grad x))) =
          vecDot pbar avgFlux := by
      have hpair :=
        basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
          U a pbar 0 hInt w
      have hpair' :
          volumeAverage U (fun _ => (0 : ℝ)) -
              volumeAverage U (fun x => vecDot pbar (matVecMul (a x) (w.toH1.grad x))) =
            -vecDot pbar avgFlux := by
        simpa [avgFlux, pbar, vecDot] using hpair
      linarith
    have hlin :=
      basic_cg_identities_linear_response_of_isResponseMaximizer
        U a hEll pbar 0 hInt u hmax w
    have hBmul : matVecMul B pbar = -avgFlux := by
      unfold pbar
      rw [matVecMul_neg, matVecMul_mul, Matrix.mul_nonsing_inv B hBdet]
      funext i
      simp [matVecMul, Matrix.one_apply, avgFlux]
    have hresp :
        ResponseJ U pbar 0 a =
          (1 / 2 : ℝ) * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
      rw [basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
        U a hS hK hSigma hdet]
      calc
        (1 / 2 : ℝ) * vecDot pbar (matVecMul B pbar) =
          (1 / 2 : ℝ) * vecDot pbar (-avgFlux) := by
            rw [hBmul]
        _ = (1 / 2 : ℝ) * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
            unfold pbar
            rw [vecDot_neg_right, vecDot_neg_left, neg_neg, vecDot_comm]
    have hlin' :
        |vecDot pbar avgFlux| ≤
          Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
            Real.sqrt (vecDot avgFlux (matVecMul B⁻¹ avgFlux)) := by
      have hlin0 :
          |volumeAverage U (fun _ => (0 : ℝ)) -
              volumeAverage U (fun x => vecDot pbar (matVecMul (a x) (w.toH1.grad x)))| ≤
            Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
              Real.sqrt (vecDot avgFlux (matVecMul B⁻¹ avgFlux)) := by
        simpa [hresp, avgFlux, B, pbar, vecDot, mul_assoc, mul_left_comm, mul_comm] using hlin
      rw [hzero, havg, sub_eq_add_neg] at hlin0
      simpa using hlin0
    have hquad_nonneg :
        0 ≤ vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
      have hresp_nonneg : 0 ≤ ResponseJ U pbar 0 a := responseJ_nonneg U pbar 0 a
      rw [hresp] at hresp_nonneg
      nlinarith
    have hpbarEq :
        vecDot pbar avgFlux = -vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
      unfold pbar
      rw [vecDot_neg_left, vecDot_comm]
    have henergy_nonneg :
        0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a w) :=
      volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U a hEll w
    have hsq :
        vecDot avgFlux (matVecMul B⁻¹ avgFlux) ^ 2 ≤
          volumeAverage U (scalarVariationEnergyIntegrand a w) *
            vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
      have hlin'' :
          vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
            Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
              Real.sqrt (vecDot avgFlux (matVecMul B⁻¹ avgFlux)) := by
        have hlinAbs := hlin'
        rw [hpbarEq] at hlinAbs
        rw [abs_neg, abs_of_nonneg hquad_nonneg] at hlinAbs
        exact hlinAbs
      nlinarith [hlin'', Real.sq_sqrt henergy_nonneg, Real.sq_sqrt hquad_nonneg]
    have hmain :
        vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
          volumeAverage U (scalarVariationEnergyIntegrand a w) := by
      nlinarith [hsq, hquad_nonneg]
    nlinarith [hmain]
  · have hBinv : B⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit B hBdet
    have henergy_nonneg :
        0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a w) :=
      volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U a hEll w
    rw [hBinv]
    simp [matVecMul, vecDot]
    nlinarith

theorem basic_cg_identities_energy_average_flux_canonical_of_isSigmaCoarse_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a U)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U
      (-matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))
      0 a u) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
            (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) :=
  basic_cg_identities_energy_average_flux_canonical_of_isSigmaCoarse
    U a hEll hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w u hmax

theorem basic_cg_identities_responseJ_zero_formula_deterministicCoarseBlockMatrix_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p) := by
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
    hS hK hSigma hdet]
  simpa [blockMatrixOfDeterministicData] using
    basic_cg_identities_responseJ_zero_formula_of_isSigmaCoarse U a hSigma p

theorem basic_cg_identities_responseJ_zero_formula_coarseBlockMatrix_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
  rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact basic_cg_identities_responseJ_zero_formula_deterministicCoarseBlockMatrix_of_isSigmaCoarse
    U a hS hK hSigma hdet p

theorem basic_cg_identities_responseJ_formula_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) - vecDot p q +
        vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
  rcases hS with ⟨_, hSresp⟩
  have hq := hSresp q
  have hk := hK p q
  have hp := basic_cg_identities_responseJ_zero_formula_of_isSigmaCoarse U a hSigma p
  linarith

theorem basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) - vecDot p q +
        vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    basic_cg_identities_responseJ_formula_of_isSigmaCoarse U a hS hK hSigma p q

theorem basic_cg_identities_responseJ_formula_deterministicCoarseBlockMatrix_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p) := by
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
    hS hK hSigma hdet]
  calc
    ResponseJ U p q a =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) - vecDot p q +
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
      exact basic_cg_identities_responseJ_formula_of_isSigmaCoarse U a hS hK hSigma p q
    _ = (1 / 2 : ℝ) * vecDot q (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperLeft p) := by
      simp [blockMatrixOfDeterministicData, sub_eq_add_neg, matVecMul_mul,
        neg_matVecMul, vecDot_neg_right, add_assoc]

theorem basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
  rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact basic_cg_identities_responseJ_formula_deterministicCoarseBlockMatrix_of_isSigmaCoarse
    U a hS hK hSigma hdet p q

theorem basic_cg_identities_average_gradient_formula_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) := by
  funext i
  let e : Vec d := Pi.single i 1
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  rcases hS with ⟨_, hSresp⟩
  have hcoord :=
    basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer
      U a p q hInt u hmax i (uGrad i) (hmaxGrad i)
  have hq :
      ResponseJ U 0 q a + ResponseJ U 0 e a - ResponseJ U 0 (q - e) a =
        vecDot e (matVecMul sigmaStar⁻¹ q) := by
    rw [hSresp q, hSresp e, hSresp (q - e)]
    simpa [e] using half_vecDot_sub_polarization_of_isSymm hSInvSymm q e
  have hdot_p : vecDot p (q - e) = vecDot p q - vecDot p e := by
    simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
  have hdot_k :
      vecDot (q - e) (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) -
          vecDot e (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hmain :
      ResponseJ U p q a + ResponseJ U 0 e a - ResponseJ U p (q - e) a =
        -vecDot p e + vecDot e (matVecMul sigmaStar⁻¹ q) +
          vecDot e (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    linarith [hq, hK p q, hK p (q - e), hdot_p, hdot_k]
  calc
    volumeAverage U (fun x => u.toH1.grad x i) =
      ResponseJ U p q a + ResponseJ U 0 e a - ResponseJ U p (q - e) a := hcoord
    _ = -vecDot p e + vecDot e (matVecMul sigmaStar⁻¹ q) +
          vecDot e (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := hmain
    _ = (-p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) i := by
      simp [e, matVecMul_add, vecDot_single_left, vecDot_single_right]
      ring

theorem basic_cg_identities_average_flux_formula_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p := by
  funext i
  let e : Vec d := Pi.single i 1
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hBsymm := bCoarse_isSymm_of_isSigmaCoarse hS hSigma
  have hcoord :=
    basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer
      U a p q hInt u hmax i (uFlux i) (hmaxFlux i)
  have hB :
      ResponseJ U (p - e) 0 a - ResponseJ U p 0 a - ResponseJ U e 0 a =
        -vecDot e (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
    have hp := responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse hSigma p
    have he := responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse hSigma e
    have hpe := responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse hSigma (p - e)
    have hquad := half_vecDot_sub_sub_of_isSymm hBsymm p e
    linarith
  have hdot_q : vecDot (p - e) q = vecDot p q - vecDot e q := by
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hdot_k :
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa (p - e))) =
        vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa e)) := by
    simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_neg_right]
  have hmain :
      ResponseJ U (p - e) q a - ResponseJ U p q a - ResponseJ U e 0 a =
        vecDot e q - vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa e)) -
          vecDot e (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
    linarith [hB, hK (p - e) q, hK p q, hdot_q, hdot_k]
  have hmiddle :
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa e)) =
        vecDot e (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q)) := by
    calc
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa e)) =
        vecDot (matVecMul kappa e) (matVecMul sigmaStar⁻¹ q) := by
          rw [vecDot_matVecMul_comm_of_isSymm hSInvSymm q (matVecMul kappa e)]
      _ = vecDot e (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q)) := by
          rw [vecDot_matVecMul_transpose]
  calc
    volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i) =
      ResponseJ U (p - e) q a - ResponseJ U p q a - ResponseJ U e 0 a := hcoord
    _ = vecDot e q - vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa e)) -
          vecDot e (matVecMul (bCoarse sigma sigmaStar kappa) p) := hmain
    _ = vecDot e q - vecDot e (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q)) -
          vecDot e (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
      rw [hmiddle]
    _ = (q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
          matVecMul (bCoarse sigma sigmaStar kappa) p) i := by
      simp [e, sub_eq_add_neg, vecDot_single_left]

theorem basic_cg_identities_average_gradient_formula_canonical_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet] using
    basic_cg_identities_average_gradient_formula_of_isResponseMaximizer
      U a hS hK p q hInt u hmax uGrad hmaxGrad

theorem basic_cg_identities_average_flux_formula_canonical_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    basic_cg_identities_average_flux_formula_of_isResponseMaximizer
      U a hS hK hSigma p q hInt u hmax uFlux hmaxFlux

theorem basic_cg_identities_average_gradient_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p := by
  calc
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
        -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) := by
      exact basic_cg_identities_average_gradient_formula_canonical_of_isResponseMaximizer
        U a hS hK hdet p q hInt u hmax uGrad hmaxGrad
    _ = -p + matVecMul (sigmaStarInvCoarse U a) q +
          matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p) := by
      simp [matVecMul_add, add_assoc]
    _ = -p + matVecMul (sigmaStarInvCoarse U a) q +
          matVecMul ((sigmaStarInvCoarse U a) * (kappaCoarse U a)) p := by
      rw [matVecMul_mul]
    _ = -p + matVecMul (sigmaStarInvCoarse U a) q +
          matVecMul (sigmaStarInvKappaCoarse U a) p := by
      rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
        eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
        ← sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]
    _ = -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
          matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p := by
      simp [deterministicCoarseBlockMatrix, sub_eq_add_neg, neg_matVecMul, add_assoc]

theorem basic_cg_identities_average_flux_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p := by
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
    hS hK hSigma hdet]
  calc
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
        q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
          matVecMul (bCoarse sigma sigmaStar kappa) p := by
      exact basic_cg_identities_average_flux_formula_of_isResponseMaximizer
        U a hS hK hSigma p q hInt u hmax uFlux hmaxFlux
    _ = q + matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperRight q -
          matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperLeft p := by
      simp [blockMatrixOfDeterministicData, sub_eq_add_neg, matVecMul_mul,
        neg_matVecMul, add_assoc]

theorem basic_cg_identities_average_gradient_formula_coarseBlockMatrix_of_isResponseMaximizer
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uGrad : Fin d → AHarmonicFunction a U)
    (hmaxGrad : ∀ i : Fin d, IsResponseMaximizer U 0 (Pi.single i 1) a (uGrad i)) :
    (fun i => volumeAverage U (fun x => u.toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p := by
  rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact basic_cg_identities_average_gradient_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    U a hS hK hdet p q hInt u hmax uGrad hmaxGrad

theorem basic_cg_identities_average_flux_formula_coarseBlockMatrix_of_isResponseMaximizer
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p q : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (uFlux : Fin d → AHarmonicFunction a U)
    (hmaxFlux : ∀ i : Fin d, IsResponseMaximizer U (Pi.single i 1) 0 a (uFlux i)) :
    (fun i => volumeAverage U (fun x => matVecMul (a x) (u.toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p := by
  rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact basic_cg_identities_average_flux_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    U a hS hK hSigma hdet p q hInt u hmax uFlux hmaxFlux

end

end Homogenization
