/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.UShear
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Explicit differential identities for the Section 3 shear fields. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section3

theorem spaceGrad_sineCoordinate (A ω : ℝ) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => A * Real.sin (ω * y i)) x j =
      if j = i then A * ω * Real.cos (ω * x i) else 0 := by
  unfold AVenhance.spaceGrad
  have hproj : HasFDerivAt (fun y : Vec 2 => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x :=
    hasFDerivAt_apply (𝕜 := ℝ) i x
  have hlin : HasFDerivAt (fun y : Vec 2 => ω * y i)
      (ω • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x := by
    exact hproj.const_mul ω
  have hsin := (Real.hasDerivAt_sin (ω * x i)).comp_hasFDerivAt x hlin
  have hfun := hsin.const_mul A
  have hderiv : fderiv ℝ (fun y : Vec 2 => A * Real.sin (ω * y i)) x =
      A • Real.cos (ω * x i) • ω •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i := by
    simpa only [Function.comp_apply] using hfun.fderiv
  rw [hderiv]
  by_cases hji : j = i
  · subst j
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply,
      ite_true]
    ring
  · have hij : i ≠ j := Ne.symm hji
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply,
      hji, hij, ite_false, smul_zero]

/-- The stream function is a coordinate sine (or zero), with frequency
`2π/ε_m`. -/
theorem psi_sineCoordinate {β : ℝ} {Λ m : ℕ} (k : ℤ) (x : Vec 2) :
    AVenhance.psi β Λ m k x =
      AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
        (if k % 4 = 1 then
          Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 0)
        else if k % 4 = 3 then
          Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 1)
        else 0) := by
  unfold AVenhance.psi AVenhance.psi0
  simp only [Pi.smul_apply, smul_eq_mul]
  have hcoord (i : Fin 2) :
      2 * Real.pi * ((AVenhance.epsilon β Λ m)⁻¹ * x i) =
        (2 * Real.pi / AVenhance.epsilon β Λ m) * x i := by
    rw [div_eq_mul_inv]
    ring
  simp_rw [hcoord]

/-- The stream function is a single coordinate sine (or zero), with
frequency `2π/ε_m`. -/
theorem psi_spaceGrad_formula {β : ℝ} {Λ m : ℕ} (k : ℤ) (x : Vec 2)
    (hε : AVenhance.epsilon β Λ m ≠ 0) :
    AVenhance.spaceGrad (AVenhance.psi β Λ m k) x =
      if k % 4 = 1 then
        ![AVenhance.a β Λ m * AVenhance.epsilon β Λ m *
            (2 * Real.pi) * Real.cos
              (2 * Real.pi * x 0 / AVenhance.epsilon β Λ m), 0]
      else if k % 4 = 3 then
        ![0, AVenhance.a β Λ m * AVenhance.epsilon β Λ m *
            (2 * Real.pi) * Real.cos
              (2 * Real.pi * x 1 / AVenhance.epsilon β Λ m)]
      else 0 := by
  have hform := psi_sineCoordinate (β := β) (Λ := Λ) (m := m) k
  have hfreq (z : ℝ) :
      (2 * Real.pi / AVenhance.epsilon β Λ m) * z =
        2 * Real.pi * z / AVenhance.epsilon β Λ m := by
    field_simp [hε]
  have hcoef : AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
      (2 * Real.pi / AVenhance.epsilon β Λ m) =
        AVenhance.a β Λ m * AVenhance.epsilon β Λ m * (2 * Real.pi) := by
    field_simp [hε]
  by_cases h1 : k % 4 = 1
  · have hfun : AVenhance.psi β Λ m k = fun y =>
        AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
          Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * y 0) := by
      funext y
      rw [hform y]
      simp only [ite_eq_left h1]
    rw [hfun]
    simp only [ite_eq_left h1]
    funext j
    rw [spaceGrad_sineCoordinate]
    fin_cases j <;> simp [hcoef, hfreq]
  · by_cases h3 : k % 4 = 3
    · have hfun : AVenhance.psi β Λ m k = fun y =>
          AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
            Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * y 1) := by
        funext y
        rw [hform y]
        simp only [ite_eq_right h1, ite_eq_left h3]
      rw [hfun]
      simp only [ite_eq_right h1, ite_eq_left h3]
      funext j
      rw [spaceGrad_sineCoordinate]
      fin_cases j <;> simp [hcoef, hfreq]
    · have hfun : AVenhance.psi β Λ m k = fun _ => 0 := by
        funext y
        rw [hform y]
        simp only [ite_eq_right h1, ite_eq_right h3, mul_zero]
      rw [hfun]
      simp only [ite_eq_right h1, ite_eq_right h3]
      funext j
      simp [AVenhance.spaceGrad]

/-- The rotation matrix is the counterclockwise quarter-turn. -/
theorem ShearFormula.sigmaMat_mulVec_formula (v : Vec 2) :
    AVenhance.sigmaMat.mulVec v = ![-v 1, v 0] := by
  funext i
  fin_cases i <;> simp [AVenhance.sigmaMat, Matrix.mulVec_apply_eq_sum,
    Fin.sum_univ_two]

/-- `u_{m,k}=σ∇ψ_{m,k}` (source `e.ukm.explicit` and `e.def.streamr`). -/
theorem uShear_eq_sigma_spaceGrad {β : ℝ} {Λ m : ℕ} (k : ℤ) (x : Vec 2)
    (hε : AVenhance.epsilon β Λ m ≠ 0) :
  AVenhance.uShear β Λ m k x =
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (AVenhance.psi β Λ m k) x) := by
  rw [ShearFormula.sigmaMat_mulVec_formula, psi_spaceGrad_formula k x hε]
  by_cases h1 : k % 4 = 1
  · simp only [AVenhance.uShear, ite_eq_left h1]
    ext i
    fin_cases i
    · simp
    · simp only [Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero]
      ring_nf
  · by_cases h3 : k % 4 = 3
    · simp only [AVenhance.uShear, ite_eq_right h1, ite_eq_left h3]
      ext i
      fin_cases i
      · simp only [Matrix.cons_val_zero', Matrix.cons_val_one,
          Matrix.cons_val_zero]
        ring_nf
      · simp
    · simp only [AVenhance.uShear, ite_eq_right h1, ite_eq_right h3]
      ext i
      fin_cases i <;> simp

end AVenhance.Infra.Section3
