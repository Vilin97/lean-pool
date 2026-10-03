/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientEstimates

/-! # Gradient Matrix

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- The matrix of first spatial partial derivatives, with output component
as the first index and differentiation direction as the second. -/
def spatialGradientMatrix (f : Vec 2 → Vec 2) (x : Vec 2) :
    Fin 2 → Fin 2 → ℝ :=
  fun i j => fderiv ℝ f x (coordinateVector 2 j) i

/-- Evaluating a linear map on the two coordinate vectors and then taking its
two output coordinates is a norm-nonincreasing map into the entrywise matrix
norm. -/
noncomputable def gradientMatrixOfCLM :
    (VecOne 2 →L[ℝ] Vec 2) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  ContinuousLinearMap.mk
    { toFun := fun A i j => A (coordinateVectorOne 2 j) i
      map_add' := by
        intro A B
        ext i j
        simp
      map_smul' := by
        intro c A
        ext i j
        simp }
    (by fun_prop)

theorem gradientMatrixOfCLM_norm_le (A : VecOne 2 →L[ℝ] Vec 2) :
    ‖gradientMatrixOfCLM A‖ ≤ ‖A‖ := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  rw [pi_norm_le_iff_of_nonempty]
  intro j
  calc
    ‖gradientMatrixOfCLM A i j‖ = ‖A (coordinateVectorOne 2 j) i‖ := rfl
    _ ≤ ‖A (coordinateVectorOne 2 j)‖ := norm_le_pi_norm _ _
    _ ≤ ‖A‖ * ‖coordinateVectorOne 2 j‖ := A.le_opNorm _
    _ = ‖A‖ := by rw [coordinateVectorOne_norm]; ring

theorem gradientMatrixOfCLM_opNorm_le : ‖gradientMatrixOfCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  calc
    ‖gradientMatrixOfCLM A‖ ≤ ‖A‖ := gradientMatrixOfCLM_norm_le A
    _ = 1 * ‖A‖ := by ring

/-- Lifting the paper gradient matrix to the `ℓ¹` coordinate realization
agrees with evaluating the derivative of the lifted vector field on coordinate
vectors. -/
theorem lift_spatialGradientMatrix_eq
    (f : Vec 2 → Vec 2) (hf : ContDiff ℝ 1 f) (z : VecOne 2) :
    liftVecOne (spatialGradientMatrix f) z =
      gradientMatrixOfCLM (fderiv ℝ (liftVecOne f) z) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcomp := (hdiff (vecOneEquiv 2 z)).hasFDerivAt.comp z
    (vecOneEquiv 2).hasFDerivAt
  have hderiv : fderiv ℝ (liftVecOne f) z =
      (fderiv ℝ f (vecOneEquiv 2 z)).comp (vecOneEquiv 2).toContinuousLinearMap := by
    simpa [liftVecOne, vecOneEquiv, PiLp.coe_continuousLinearEquiv] using hcomp.fderiv
  have hbasis (j : Fin 2) :
      vecOneEquiv 2 (coordinateVectorOne 2 j) = coordinateVector 2 j := by
    ext k
    by_cases hk : k = j <;>
      simp [vecOneEquiv, coordinateVectorOne, coordinateVector, hk]
  ext i j
  change fderiv ℝ f (vecOneEquiv 2 z) (coordinateVector 2 j) i =
    fderiv ℝ (liftVecOne f) z (coordinateVectorOne 2 j) i
  rw [hderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hbasis j]

/-- The order-`n` derivative seminorm of the gradient matrix is bounded by
the order-`n+1` derivative seminorm of the underlying vector field. -/
theorem spatialGradientMatrix_derivativeSup_le
    (f : Vec 2 → Vec 2) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    derivativeSup n (spatialGradientMatrix f) ≤ derivativeSup (n + 1) f := by
  let F : VecOne 2 → Vec 2 := liftVecOne f
  let H : VecOne 2 → (Fin 2 → Fin 2 → ℝ) :=
    fun z => gradientMatrixOfCLM (fderiv ℝ F z)
  have hFderiv : ContDiff ℝ ∞ (fun z : VecOne 2 => fderiv ℝ F z) := by
    have hF : ContDiff ℝ ∞ F := by
      dsimp [F, liftVecOne]
      exact hf.comp_continuousLinearMap (g := (vecOneEquiv 2).toContinuousLinearMap)
    exact hF.fderiv_right (by simp)
  have hLift : liftVecOne (spatialGradientMatrix f) = H := by
    funext z
    exact lift_spatialGradientMatrix_eq f
      ((hf.of_le (by norm_num : (1 : ℕ) ≤ ∞))) z
  have hpoint (z : VecOne 2) :
      ‖iteratedFDeriv ℝ n (liftVecOne (spatialGradientMatrix f)) z‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) F z‖ := by
    rw [hLift]
    have hcomp := gradientMatrixOfCLM.iteratedFDeriv_comp_left
      (hFderiv.contDiffAt (x := z)) (i := n) (by simp)
    rw [show H = gradientMatrixOfCLM ∘ (fun z => fderiv ℝ F z) by rfl]
    rw [hcomp]
    calc
      ‖gradientMatrixOfCLM.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun z => fderiv ℝ F z) z)‖ ≤
          ‖gradientMatrixOfCLM‖ *
            ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ F z) z‖ :=
        gradientMatrixOfCLM.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ F z) z‖ := by
        calc
          _ = ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ F z) z‖ *
              ‖gradientMatrixOfCLM‖ := by rw [mul_comm]
          _ ≤ ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ F z) z‖ :=
            mul_le_of_le_one_right (norm_nonneg _)
              gradientMatrixOfCLM_opNorm_le
      _ = ‖iteratedFDeriv ℝ (n + 1) F z‖ := norm_iteratedFDeriv_fderiv
  calc
    derivativeSup n (spatialGradientMatrix f) ≤
        operatorDerivativeSup n (spatialGradientMatrix f) :=
      derivativeSup_le_operatorDerivativeSup _
    _ ≤ derivativeSup (n + 1) f := by
      unfold operatorDerivativeSup
      rw [eLpNormEssSup_eq_essSup_enorm]
      apply essSup_le_of_ae_le _ ?_
      filter_upwards [operatorDerivative_ae_le_derivativeSup (n := n + 1) f]
        with x hx
      calc
        ‖‖iteratedFDeriv ℝ n (liftVecOne (spatialGradientMatrix f))
            (WithLp.toLp 1 x)‖‖ₑ =
          ENNReal.ofReal ‖iteratedFDeriv ℝ n
            (liftVecOne (spatialGradientMatrix f)) (WithLp.toLp 1 x)‖ := by simp
        _ ≤ ENNReal.ofReal ‖iteratedFDeriv ℝ (n + 1) (liftVecOne f)
            (WithLp.toLp 1 x)‖ := ENNReal.ofReal_le_ofReal
              (hpoint (WithLp.toLp 1 x))
        _ = ‖iteratedFDeriv ℝ (n + 1) (liftVecOne f)
            (WithLp.toLp 1 x)‖ₑ := by simp
        _ ≤ derivativeSup (n + 1) f := hx

theorem GradientMatrix.one_add_nat_mul_le_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    1 + (n : ℝ) * a ≤ (1 + a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ 1 + a)
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hquad : 0 ≤ (n : ℝ) * a ^ 2 := mul_nonneg hnnonneg (sq_nonneg a)
    push_cast
    nlinarith [hmul, hquad]

/-- The all-order gradient seminorm estimate (10670), reduced to the
corresponding order-`n+1` transport estimate. This theorem is in the consumed
equal-radius, dimension-two form. -/
theorem spatialGradientMatrix_snorm_le_of_nextOrder
    (f : Vec 2 → Vec 2) (hf : ContDiff ℝ ∞ f) (n : ℕ)
    {C_f C_g R τ : ℝ}
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hτ : 0 ≤ τ) (hT : τ ≤ 1 / (8 * C_f * R))
    (hnext : snorm f (n + 1) (R * (1 + 8 * τ * C_f * R)) ≤
      ENNReal.ofReal (16 * C_g * τ)) :
    snorm (spatialGradientMatrix f) n
        (R * (1 + 8 * τ * C_f * R) ^ 2) ≤ ENNReal.ofReal (8 * C_g / C_f) := by
  let a : ℝ := 8 * C_f * τ * R
  let RY : ℝ := R * (1 + a)
  let Rgrad : ℝ := R * (1 + a) ^ 2
  let coef : ℝ := (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2
  let K : ℝ := (8 * C_g / C_f) * n.factorial / (n + 1 : ℝ) ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    have hden : 0 < 8 * C_f * R := by positivity
    have hsmall := (le_div_iff₀ hden).mp hT
    dsimp [a]
    nlinarith [hsmall]
  have hRY : 0 < RY := by dsimp [RY]; positivity
  have hRgrad : 0 < Rgrad := by dsimp [Rgrad]; positivity
  have hRYupper : RY ≤ 2 * R := by
    dsimp [RY]
    calc
      R * (1 + a) ≤ R * 2 := mul_le_mul_of_nonneg_left (by linarith) hR.le
      _ = 2 * R := by ring
  have hCfτRY : C_f * τ * RY ≤ a / 4 := by
    have h := mul_le_mul_of_nonneg_left hRYupper (mul_nonneg hCf.le hτ)
    dsimp [a] at h ⊢
    nlinarith [h]
  have hRgradFactor : Rgrad = RY * (1 + a) := by
    dsimp [Rgrad, RY]
    ring
  have hratio : 2 * C_f * τ * coef * RY ≤ (1 + a) ^ n := by
    by_cases hn0 : n = 0
    · subst n
      norm_num [coef]
      nlinarith [hCfτRY, ha1]
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hcoef : coef ≤ (n : ℝ) := by
        dsimp [coef]
        rw [div_le_iff₀ (by positivity : 0 < (n + 2 : ℝ) ^ 2)]
        nlinarith
      have hcoef0 : 0 ≤ coef := by dsimp [coef]; positivity
      have hfirst : 2 * C_f * τ * coef * RY ≤ (a / 2) * n := by
        calc
          2 * C_f * τ * coef * RY = 2 * (C_f * τ * RY) * coef := by ring
          _ ≤ 2 * (a / 4) * coef :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hCfτRY (by norm_num)) hcoef0
          _ ≤ 2 * (a / 4) * n :=
            mul_le_mul_of_nonneg_left hcoef (by positivity)
          _ = (a / 2) * n := by ring
      have hBern := GradientMatrix.one_add_nat_mul_le_pow ha n
      have hpowNonneg : 0 ≤ (1 + a) ^ n := by positivity
      calc
        _ ≤ (a / 2) * n := hfirst
        _ ≤ (1 + a) ^ n / 2 := by nlinarith [hBern]
        _ ≤ (1 + a) ^ n := by nlinarith
  have hratioPow : 2 * C_f * τ * coef * RY ^ (n + 1) ≤ Rgrad ^ n := by
    have hmul := mul_le_mul_of_nonneg_right hratio (pow_nonneg hRY.le n)
    calc
      _ = (2 * C_f * τ * coef * RY) * RY ^ n := by rw [pow_succ]; ring
      _ ≤ (1 + a) ^ n * RY ^ n := hmul
      _ = RY ^ n * (1 + a) ^ n := by ac_rfl
      _ = (RY * (1 + a)) ^ n := by rw [← mul_pow]
      _ = Rgrad ^ n := by rw [← hRgradFactor]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hscale :
      16 * C_g * τ * ((n + 1).factorial : ℝ) * RY ^ (n + 1) /
          (n + 2 : ℝ) ^ 2 ≤
        (8 * C_g / C_f) * Rgrad ^ n * n.factorial /
          (n + 1 : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hratioPow hK
    have hleft :
        16 * C_g * τ * ((n + 1).factorial : ℝ) * RY ^ (n + 1) /
            (n + 2 : ℝ) ^ 2 = K * (2 * C_f * τ * coef * RY ^ (n + 1)) := by
      dsimp [K, coef]
      rw [Nat.factorial_succ]
      push_cast
      field_simp [ne_of_gt hCf]
      ring
    have hright :
        K * Rgrad ^ n =
          (8 * C_g / C_f) * Rgrad ^ n * n.factorial /
            (n + 1 : ℝ) ^ 2 := by
      dsimp [K]
      ring
    calc
      _ = K * (2 * C_f * τ * coef * RY ^ (n + 1)) := hleft
      _ ≤ K * Rgrad ^ n := hmul
      _ = _ := hright
  have hRYpaper : RY = R * (1 + 8 * τ * C_f * R) := by
    dsimp [RY, a]
    ring
  have hnext' : snorm f (n + 1) RY ≤ ENNReal.ofReal (16 * C_g * τ) := by
    rw [hRYpaper]
    exact hnext
  have hYderiv := derivativeSup_le_of_snorm_le f hRY hnext'
  have hD : derivativeSup n (spatialGradientMatrix f) ≤ ENNReal.ofReal
      ((8 * C_g / C_f) * Rgrad ^ n * n.factorial /
        (n + 1 : ℝ) ^ 2) := by
    calc
      derivativeSup n (spatialGradientMatrix f) ≤ derivativeSup (n + 1) f :=
        spatialGradientMatrix_derivativeSup_le f hf n
      _ ≤ ENNReal.ofReal
          (16 * C_g * τ * ((n + 1).factorial : ℝ) * RY ^ (n + 1) /
            (n + 2 : ℝ) ^ 2) := by
              have hden : ((n + 1 : ℕ) : ℝ) + 1 = (n + 2 : ℝ) := by
                push_cast
                ring
              rw [hden] at hYderiv
              simpa [RY] using hYderiv
      _ ≤ ENNReal.ofReal
          ((8 * C_g / C_f) * Rgrad ^ n * n.factorial /
            (n + 1 : ℝ) ^ 2) := ENNReal.ofReal_le_ofReal hscale
  have hsnorm := snorm_le_of_derivativeSup_le
    (spatialGradientMatrix f) hRgrad hD
  have hRgradPaper : Rgrad = R * (1 + 8 * τ * C_f * R) ^ 2 := by
    dsimp [Rgrad, a]
    ring
  rw [← hRgradPaper]
  exact hsnorm

theorem GradientMatrix.derivativeSup_zero_eq_eLpNormEssSup
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) : derivativeSup 0 f = eLpNormEssSup f (vecVolume d) := by
  simp [derivativeSup, partialSup, orderedPartial]

theorem GradientMatrix.snorm_zero_eq_derivativeSup
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (R : ℝ) : snorm f 0 R = derivativeSup 0 f := by
  simp [snorm]

end AVenhance.FaaDiBruno

end
