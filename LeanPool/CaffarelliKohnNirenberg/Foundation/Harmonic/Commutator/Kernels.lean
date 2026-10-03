/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Commutator.KernelsBasic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kernels

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

theorem newtonianKernel_eq_scaled (m j l : Fin 3) (x : CKN.Vec 3) :
    newtonianKernel m j l x = -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x := by
  rfl

theorem newtonianKernel_size_bound {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l : Fin 3) :
    |newtonianKernel m j l x| ≤
      (24 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-4 : ℝ) := by
  let r := CKN.vecEuclideanNorm x
  have hr : 0 < r := by
    dsimp [r]
    apply lt_of_le_of_ne (CKN.vecEuclideanNorm_nonneg x)
    intro h
    apply hx
    exact CKN.vecEuclideanNorm_eq_zero_iff.mp h.symm
  have hcoord (i : Fin 3) : |x i| ≤ r :=
    abs_apply_le_vecEuclideanNorm x i
  have hr4 : r ^ (-4 : ℝ) = (r ^ 4)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hr5 : r ^ (-5 : ℝ) = (r ^ 5)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hr7 : r ^ (-7 : ℝ) = (r ^ 7)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_num
  have hterm₁ :
      |15 * x m * x j * x l * (r ^ 7)⁻¹| ≤ 15 * r ^ (-4 : ℝ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15),
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
    calc
      15 * |x m| * |x j| * |x l| * (r ^ 7)⁻¹ ≤
          15 * r * r * r * (r ^ 7)⁻¹ := by
        gcongr
        · exact hcoord m
        · exact hcoord j
        · exact hcoord l
      _ = 15 * r ^ (-4 : ℝ) := by
        rw [hr4]
        field_simp [hr.ne']
  have hterm₂ (a b : Fin 3) :
      |3 * x a * (r ^ 5)⁻¹| ≤ 3 * r ^ (-4 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg
      (inv_nonneg.mpr (pow_nonneg hr.le _))]
    calc
      3 * |x a| * (r ^ 5)⁻¹ ≤ 3 * r * (r ^ 5)⁻¹ := by
        gcongr
        exact hcoord a
      _ = 3 * r ^ (-4 : ℝ) := by
        rw [hr4]
        field_simp [hr.ne']
  have hdelta (p : Prop) [Decidable p] (a : ℝ) :
      |(if p then (1 : ℝ) else 0) * a| ≤ |a| := by
    by_cases hp : p <;> simp [hp]
  rw [newtonianKernel_eq_scaled]
  unfold inverseThirdFormula
  rw [abs_mul]
  have hscale : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hinner :
      |-15 * x m * x j * x l * (r ^ 7)⁻¹ +
          3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| ≤
        24 * r ^ (-4 : ℝ) := by
    have hsum :
        |(if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m| ≤
        |x j| + |x l| + |x m| := by
      calc
        _ ≤ |(if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l| +
            |(if l = j then 1 else 0) * x m| := abs_add_le _ _
        _ ≤ (|(if m = l then 1 else 0) * x j| +
            |(if m = j then 1 else 0) * x l|) +
            |(if l = j then 1 else 0) * x m| := by
          exact add_le_add_left
            (abs_add_le ((if m = l then 1 else 0) * x j)
              ((if m = j then 1 else 0) * x l)) _
        _ ≤ |x j| + |x l| + |x m| := by
          exact add_le_add (add_le_add (hdelta (m = l) (x j))
            (hdelta (m = j) (x l))) (hdelta (l = j) (x m))
    have hsumKernel :
        |3 * ((if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| ≤
        9 * r ^ (-4 : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      calc
        3 * |(if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m| * (r ^ 5)⁻¹ ≤
            3 * (|x j| + |x l| + |x m|) * (r ^ 5)⁻¹ := by
          gcongr
        _ ≤ 3 * (r + r + r) * (r ^ 5)⁻¹ := by
          gcongr <;> exact hcoord _
        _ = 9 * r ^ (-4 : ℝ) := by
          rw [hr4]
          field_simp [hr.ne']
          ring_nf
    calc
      _ ≤ |15 * x m * x j * x l * (r ^ 7)⁻¹| +
          |3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹| := by
        rw [show -15 * x m * x j * x l * (r ^ 7)⁻¹ =
          -(15 * x m * x j * x l * (r ^ 7)⁻¹) by ring_nf]
        simpa only [abs_neg] using (abs_add_le
          (-(15 * x m * x j * x l * (r ^ 7)⁻¹))
          (3 * ((if m = l then 1 else 0) * x j +
            (if m = j then 1 else 0) * x l +
            (if l = j then 1 else 0) * x m) * (r ^ 5)⁻¹))
      _ ≤ 24 * r ^ (-4 : ℝ) := by
        exact (add_le_add hterm₁ hsumKernel).trans_eq (by ring_nf)
  rw [show CKN.vecEuclideanNorm x = r by rfl]
  rw [abs_neg, abs_of_nonneg hscale]
  apply (mul_le_mul_of_nonneg_left hinner hscale).trans_eq
  field_simp [ne_of_gt Real.pi_pos]


private theorem spatialDeriv_newtonianPotential {x : CKN.Vec 3} (hx : x ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv newtonianPotential i x =
      -(4 * Real.pi)⁻¹ * CKN.spatialDeriv radialInverse i x := by
  have h := (hasFDerivAt_radialInverse hx).const_mul (-(4 * Real.pi)⁻¹)
  have hi := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec i)) h.fderiv
  rw [CKN.spatialDeriv]
  change (fderiv ℝ (fun y => -(4 * Real.pi)⁻¹ * radialInverse y) x)
      (CKN.basisVec i) = _
  rw [hi]
  simp only [smul_apply, smul_eq_mul]
  have hrad := hasFDerivAt_radialInverse hx
  have hirad := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec i)) hrad.fderiv
  rw [CKN.spatialDeriv, hirad]
  simp only [smul_apply, smul_eq_mul]

private theorem spatialDeriv_second_newtonianPotential
    {x : CKN.Vec 3} (hx : x ≠ 0) (i j : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv newtonianPotential i) j x =
      -(4 * Real.pi)⁻¹ * CKN.spatialDeriv (firstFormula i) j x := by
  have hEq : (fun y => CKN.spatialDeriv newtonianPotential i y) =ᶠ[𝓝 x]
      (fun y => -(4 * Real.pi)⁻¹ * firstFormula i y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [spatialDeriv_newtonianPotential hy i]
    rw [spatialDeriv_radialInverse hy i]
    rfl
  have h := (hasFDerivAt_firstFormula hx i).const_mul (-(4 * Real.pi)⁻¹)
  have h' := h.congr_of_eventuallyEq hEq
  have hj := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec j)) h'.fderiv
  rw [CKN.spatialDeriv, hj]
  simp only [smul_apply, smul_eq_mul]
  have hbase := hasFDerivAt_firstFormula hx i
  have hjbase := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec j)) hbase.fderiv
  rw [CKN.spatialDeriv, hjbase]

theorem newtonianKernel_eq_iterated_spatialDeriv
    {x : CKN.Vec 3} (hx : x ≠ 0) (m j l : Fin 3) :
    CKN.spatialDeriv
        (CKN.spatialDeriv (CKN.spatialDeriv newtonianPotential l) j) m x =
      newtonianKernel m j l x := by
  have hEq : (fun y =>
      CKN.spatialDeriv (CKN.spatialDeriv newtonianPotential l) j y) =ᶠ[𝓝 x]
      (fun y => -(4 * Real.pi)⁻¹ * secondFormula l j y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [spatialDeriv_second_newtonianPotential hy l j]
    rw [spatialDeriv_firstFormula hy l j]
    rfl
  have h := (hasFDerivAt_secondFormula hx l j).const_mul (-(4 * Real.pi)⁻¹)
  have h' := h.congr_of_eventuallyEq hEq
  have hm := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec m)) h'.fderiv
  rw [CKN.spatialDeriv, hm]
  simp only [smul_apply, smul_eq_mul]
  have hformula : CKN.spatialDeriv (secondFormula l j) m x =
      inverseThirdFormula m j l x := by
    exact (spatialDeriv_secondFormula hx l j m).trans
      (spatialDeriv_third_radialInverse hx l j m).symm |>.trans
      (third_derivative_inverse_norm hx m j l)
  have hsecond := hasFDerivAt_secondFormula hx l j
  have hmsecond := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec m)) hsecond.fderiv
  rw [CKN.spatialDeriv] at hformula
  rw [hmsecond] at hformula
  rw [hformula]
  rfl

end
end CKN.Foundation.Harmonic.Commutator
