/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Operator.Basic

/-! # The flow version of the spectral homogeneous H⁻¹ estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization

noncomputable section

/-- Pointwise operator-norm form of the source's near-identity condition. The
sum controls both the forward and inverse derivatives. -/
def FlowDerivativeNearIdentity {d : ℕ}
    (X : PeriodicVolumePreservingDiffeomorphism d) : Prop :=
  ∀ x,
    ‖fderiv ℝ X.toFun x - ContinuousLinearMap.id ℝ (Vec d)‖ +
      ‖fderiv ℝ X.invFun x - ContinuousLinearMap.id ℝ (Vec d)‖ ≤ 1 / 2

theorem HMinusOneErgodicFlow.scalarDerivative_opNorm_le_coordEnergy {d : ℕ}
    (T : Vec d →L[ℝ] ℝ) :
    ‖T‖ ≤ (d : ℝ) * Real.sqrt
      (∑ i : Fin d, (T (basisVec i)) ^ 2) := by
  let E : ℝ := ∑ i : Fin d, (T (basisVec i)) ^ 2
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hcoeff (i : Fin d) : ‖T (basisVec i)‖ ≤ Real.sqrt E := by
    have hsq : (T (basisVec i)) ^ 2 ≤ E := by
      dsimp [E]
      exact Finset.single_le_sum (fun j hj => sq_nonneg (T (basisVec j)))
        (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa [sq_abs, Real.sq_sqrt hE] using hsq
  have hrepr (v : Vec d) : v = ∑ i : Fin d, v i • basisVec i := by
    ext j
    classical
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · intro hj
      simp at hj
  apply T.opNorm_le_bound (by positivity)
  intro v
  have hvmap : T v = ∑ i : Fin d, v i • T (basisVec i) := by
    calc
      T v = T (∑ i : Fin d, v i • basisVec i) := congrArg T (hrepr v)
      _ = ∑ i : Fin d, T (v i • basisVec i) := map_sum T _ _
      _ = _ := by simp only [map_smul]
  rw [hvmap]
  calc
    ‖∑ i : Fin d, v i • T (basisVec i)‖ ≤
        ∑ i : Fin d, ‖v i • T (basisVec i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ‖v‖ * Real.sqrt E := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hvi : |v i| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      exact mul_le_mul hvi (hcoeff i) (norm_nonneg _) (norm_nonneg v)
    _ = (d : ℝ) * (Real.sqrt E * ‖v‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    _ = ((d : ℝ) * Real.sqrt E) * ‖v‖ := by ring

theorem HMinusOneErgodicFlow.derivative_norm_le_three_halves {d : ℕ}
    (X : PeriodicVolumePreservingDiffeomorphism d)
    (hnear : FlowDerivativeNearIdentity X) (x : Vec d) :
    ‖fderiv ℝ X.toFun x‖ ≤ 3 / 2 := by
  have hdist : ‖fderiv ℝ X.toFun x - ContinuousLinearMap.id ℝ (Vec d)‖ ≤
      1 / 2 :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hnear x)
  calc
    ‖fderiv ℝ X.toFun x‖ =
        ‖(fderiv ℝ X.toFun x - ContinuousLinearMap.id ℝ (Vec d)) +
          ContinuousLinearMap.id ℝ (Vec d)‖ := by congr 1; abel
    _ ≤ ‖fderiv ℝ X.toFun x - ContinuousLinearMap.id ℝ (Vec d)‖ +
          ‖ContinuousLinearMap.id ℝ (Vec d)‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 := by
      exact add_le_add hdist ContinuousLinearMap.norm_id_le
    _ = 3 / 2 := by norm_num

theorem HMinusOneErgodicFlow.scalarDerivative_comp_energy_bound {d : ℕ}
    (hd : 0 < d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (X : PeriodicVolumePreservingDiffeomorphism d)
    (hDX : ∀ x, ‖fderiv ℝ X.toFun x‖ ≤ 3 / 2)
    (x : Vec d) :
    (∑ i : Fin d,
      (fderiv ℝ (fun y => φ (X.toFun y)) x (basisVec i)) ^ 2) ≤
      (3 * (d : ℝ) ^ 2) ^ 2 *
        (∑ j : Fin d,
          (fderiv ℝ φ (X.toFun x) (basisVec j)) ^ 2) := by
  let T : Vec d →L[ℝ] ℝ := fderiv ℝ φ (X.toFun x)
  let A : Vec d →L[ℝ] Vec d := fderiv ℝ X.toFun x
  let E : ℝ := ∑ j : Fin d, (T (basisVec j)) ^ 2
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun j hj => sq_nonneg _
  have hT := HMinusOneErgodicFlow.scalarDerivative_opNorm_le_coordEnergy T
  have hcomp : fderiv ℝ (fun y => φ (X.toFun y)) x = T.comp A := by
    dsimp [T, A]
    exact fderiv_comp x
      ((hφ.contDiffAt (x := X.toFun x)).differentiableAt (by norm_num))
      ((X.contDiff_toFun.contDiffAt (x := x)).differentiableAt (by norm_num))
  have hAi (i : Fin d) : ‖A (basisVec i)‖ ≤ 3 / 2 := by
    have hbi : ‖basisVec i‖ = 1 := by
      simp [basisVec, Pi.norm_single]
    calc
      ‖A (basisVec i)‖ ≤ ‖A‖ * ‖basisVec i‖ := A.le_opNorm _
      _ ≤ (3 / 2) * 1 := by rw [hbi]; exact mul_le_mul_of_nonneg_right (hDX x) (by norm_num)
      _ = 3 / 2 := by ring
  have hcoord (i : Fin d) :
      ‖T (A (basisVec i))‖ ≤ (3 / 2) * (d : ℝ) * Real.sqrt E := by
    calc
      ‖T (A (basisVec i))‖ ≤ ‖T‖ * ‖A (basisVec i)‖ := T.le_opNorm _
      _ ≤ ((d : ℝ) * Real.sqrt E) * (3 / 2) :=
        mul_le_mul hT (hAi i) (by positivity) (by positivity)
      _ = (3 / 2) * (d : ℝ) * Real.sqrt E := by ring
  have hsum :
      (∑ i : Fin d, ‖T (A (basisVec i))‖ ^ 2) ≤
        (d : ℝ) * ((3 / 2) * (d : ℝ) * Real.sqrt E) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin d, ((3 / 2) * (d : ℝ) * Real.sqrt E) ^ 2 :=
        Finset.sum_le_sum fun i hi => by
          exact pow_le_pow_left₀ (by positivity) (hcoord i) 2
      _ = _ := by simp
  have hpower : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 := by
    have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hdsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
      calc
        (d : ℝ) = 1 * (d : ℝ) := by ring
        _ ≤ (d : ℝ) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right hdreal (by positivity)
        _ = (d : ℝ) ^ 2 := by ring
    calc
      (d : ℝ) ^ 3 = (d : ℝ) ^ 2 * (d : ℝ) := by ring
      _ ≤ (d : ℝ) ^ 2 * (d : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hdsq (sq_nonneg _)
      _ = (d : ℝ) ^ 4 := by ring
  have henergy :
      (d : ℝ) * ((3 / 2) * (d : ℝ) * Real.sqrt E) ^ 2 ≤
        (3 * (d : ℝ) ^ 2) ^ 2 * E := by
    calc
      _ = (9 / 4 : ℝ) * (d : ℝ) ^ 3 * E := by
        rw [mul_pow, Real.sq_sqrt hE]
        ring
      _ ≤ 9 * (d : ℝ) ^ 4 * E := by
        have hpowNonneg : 0 ≤ (d : ℝ) ^ 3 := by positivity
        have hcoeff : (9 / 4 : ℝ) * (d : ℝ) ^ 3 ≤
            9 * (d : ℝ) ^ 3 := by nlinarith [hpowNonneg]
        calc
          _ = ((9 / 4 : ℝ) * (d : ℝ) ^ 3) * E := by ring
          _ ≤ (9 * (d : ℝ) ^ 3) * E := mul_le_mul_of_nonneg_right hcoeff hE
          _ = (9 * E) * (d : ℝ) ^ 3 := by ring
          _ ≤ (9 * E) * (d : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left hpower (by positivity)
          _ = 9 * (d : ℝ) ^ 4 * E := by ring
      _ ≤ (3 * (d : ℝ) ^ 2) ^ 2 * E := by
        rw [show (3 * (d : ℝ) ^ 2) ^ 2 = 9 * (d : ℝ) ^ 4 by ring]
  calc
    _ = ∑ i : Fin d, ‖T (A (basisVec i))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, sq_abs]
    _ ≤ _ := hsum.trans henergy

theorem HMinusOneErgodicFlow.periodic_derivative {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsZPeriodic φ)
    (x : Vec d) (k : Fin d → ℤ) :
    fderiv ℝ φ (x + latticeVector k) = fderiv ℝ φ x := by
  let v := latticeVector k
  have htranslation : HasFDerivAt (fun y : Vec d => y + v)
      (ContinuousLinearMap.id ℝ (Vec d)) x := (hasFDerivAt_id x).add_const v
  have hφdiff : DifferentiableAt ℝ φ (x + v) :=
    (hφ.contDiffAt (x := x + v)).differentiableAt (by norm_num)
  have hcomp := hφdiff.hasFDerivAt.comp x htranslation
  have hchain : fderiv ℝ (fun y => φ (y + v)) x =
      fderiv ℝ φ (x + v) := by
    have h := hcomp.fderiv
    simpa [Function.comp_def] using h
  have hfun : (fun y => φ (y + v)) = φ := by
    funext y
    exact hper y k
  rw [hfun] at hchain
  exact hchain.symm

/-- Sum of squares of the coordinate derivatives of a scalar field. -/
def HMinusOneErgodicFlow.coordinateGradientDensity {d : ℕ}
    (φ : Vec d → ℝ) : Vec d → ℝ := fun x =>
  ∑ i : Fin d, (fderiv ℝ φ x (basisVec i)) ^ 2

theorem HMinusOneErgodicFlow.coordinateGradientDensity_periodic {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : IsZPeriodic φ) :
    IsZPeriodic (HMinusOneErgodicFlow.coordinateGradientDensity φ) := by
  intro x k
  simp only [HMinusOneErgodicFlow.coordinateGradientDensity]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun T : Vec d →L[ℝ] ℝ => (T (basisVec i)) ^ 2)
    (HMinusOneErgodicFlow.periodic_derivative hφ hper x k)

/-- The near-identity derivative bounds control the rescaled gradient norm of
every smooth periodic test after composition with the flow. -/
theorem gradientTestMap_le_of_nearIdentity {d : ℕ}
    (hd : 0 < d) (X : PeriodicVolumePreservingDiffeomorphism d)
    (hnear : FlowDerivativeNearIdentity X) :
    let L : ℝ := 3 * (d : ℝ) ^ 2
    ∀ (φ : Vec d → ℝ), ContDiff ℝ ∞ φ → IsZPeriodic φ →
      gradientL2SquaredAverage φ ≤ 1 →
      gradientL2SquaredAverage (fun x => L⁻¹ * φ (X.toFun x)) ≤ 1 := by
  dsimp
  let L : ℝ := 3 * (d : ℝ) ^ 2
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hDX : ∀ x, ‖fderiv ℝ X.toFun x‖ ≤ 3 / 2 :=
    HMinusOneErgodicFlow.derivative_norm_le_three_halves X hnear
  intro φ hφ hper hgrad
  let comp : Vec d → ℝ := fun x => φ (X.toFun x)
  let ψ : Vec d → ℝ := fun x => L⁻¹ * comp x
  let q : Vec d → ℝ := HMinusOneErgodicFlow.coordinateGradientDensity φ
  have hcompSmooth : ContDiff ℝ ∞ comp := by
    exact hφ.comp X.contDiff_toFun
  have hψSmooth : ContDiff ℝ ∞ ψ := by
    exact contDiff_const.mul hcompSmooth
  have hqContinuous : Continuous q := by
    unfold q HMinusOneErgodicFlow.coordinateGradientDensity
    apply continuous_finsetSum
    intro i hi
    exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  have hqPeriodic : IsZPeriodic q :=
    HMinusOneErgodicFlow.coordinateGradientDensity_periodic hφ hper
  have hqXContinuous : Continuous (fun x => q (X.toFun x)) := by
    exact hqContinuous.comp X.contDiff_toFun.continuous
  have hψContinuousEnergy : Continuous (fun x =>
      ∑ i : Fin d, (fderiv ℝ ψ x (basisVec i)) ^ 2) := by
    have hψC2 : ContDiff ℝ 1 ψ := hψSmooth.of_le (by norm_num)
    apply continuous_finsetSum
    intro i hi
    exact ((hψC2.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  have hqXInt : IntegrableOn (fun x => q (X.toFun x)) (Torus.unitCell d)
      (volume : Measure (Vec d)) := by
    exact continuous_unitCell_integrable hqXContinuous
  have hψEnergyInt : IntegrableOn (fun x =>
      ∑ i : Fin d, (fderiv ℝ ψ x (basisVec i)) ^ 2)
      (Torus.unitCell d) (volume : Measure (Vec d)) := by
    exact continuous_unitCell_integrable hψContinuousEnergy
  have hpoint x :
      (∑ i : Fin d, (fderiv ℝ ψ x (basisVec i)) ^ 2) ≤ q (X.toFun x) := by
    have hscale (i : Fin d) :
        fderiv ℝ ψ x (basisVec i) = L⁻¹ *
          fderiv ℝ comp x (basisVec i) := by
      change fderiv ℝ (fun y => L⁻¹ * comp y) x (basisVec i) = _
      rw [fderiv_const_mul
        ((hcompSmooth.contDiffAt (x := x)).differentiableAt (by norm_num)) L⁻¹]
      simp [smul_eq_mul]
    have hcomposition := HMinusOneErgodicFlow.scalarDerivative_comp_energy_bound hd hφ X hDX x
    have hEcomp :
        (∑ i : Fin d,
          (fderiv ℝ comp x (basisVec i)) ^ 2) ≤
          L ^ 2 * q (X.toFun x) := by
      simpa [L, q, HMinusOneErgodicFlow.coordinateGradientDensity] using hcomposition
    calc
      _ = L⁻¹ ^ 2 *
          (∑ i : Fin d, (fderiv ℝ comp x (basisVec i)) ^ 2) := by
            simp_rw [hscale, mul_pow]
            rw [Finset.mul_sum]
      _ ≤ L⁻¹ ^ 2 * (L ^ 2 * q (X.toFun x)) := by
            apply mul_le_mul_of_nonneg_left hEcomp
            positivity
      _ = q (X.toFun x) := by
            field_simp [ne_of_gt hL]
  have hcell : gradientL2SquaredAverage ψ ≤ cellAverage (fun x => q (X.toFun x)) := by
    unfold gradientL2SquaredAverage
    rw [cellAverage_eq_torusUnitCellIntegral, cellAverage_eq_torusUnitCellIntegral]
    exact setIntegral_mono_on hψEnergyInt hqXInt (Torus.measurableSet_unitCell d)
      (by intro x hx; exact hpoint x)
  calc
    gradientL2SquaredAverage ψ ≤ cellAverage (fun x => q (X.toFun x)) := hcell
    _ = cellAverage q := cellAverage_comp_flow_eq q hqPeriodic X
    _ = gradientL2SquaredAverage φ := by
      unfold gradientL2SquaredAverage q HMinusOneErgodicFlow.coordinateGradientDensity
      rfl
    _ ≤ 1 := hgrad

end

end AVenhance.Infra.Ergodic
