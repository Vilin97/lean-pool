/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowIBP
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# An explicit viscous shear flow

The velocity has one component, depending only on the transverse coordinate
and time. Its spatial gradient has only the entry in row zero, column one.
-/

@[expose] public section

open Set MeasureTheory
open CKN.Foundation.Parabolic


namespace CKN

/-- A decaying sinusoidal shear velocity. -/
noncomputable def shearFlow (z : ParabolicPoint) : Vec3 :=
  fun i => if i = 0 then Real.exp (-z.2) * Real.sin (z.1 1) else 0

/-- The explicit spatial gradient of the shear velocity. -/
noncomputable def shearFlowGrad (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j => if i = 0 ∧ j = 1 then Real.exp (-z.2) * Real.cos (z.1 1) else 0

/-- The scalar amplitude of the velocity. -/
noncomputable def shearAmplitude (z : Vec3 × ℝ) : ℝ :=
  Real.exp (-z.2) * Real.sin (z.1 1)

/-- The transverse derivative of the amplitude. -/
noncomputable def shearSlope (z : Vec3 × ℝ) : ℝ :=
  Real.exp (-z.2) * Real.cos (z.1 1)

/-- The scalar amplitude is smooth on the ordinary product space. -/
theorem shearAmplitude_smooth : ContDiff ℝ (⊤ : ℕ∞) shearAmplitude := by
  unfold shearAmplitude
  fun_prop

/-- The transverse slope is smooth on the ordinary product space. -/
theorem shearSlope_smooth : ContDiff ℝ (⊤ : ℕ∞) shearSlope := by
  unfold shearSlope
  fun_prop

/-- The vector velocity is smooth. -/
theorem shearFlow_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => shearFlow z) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [shearFlow, hi, ite_true]
    fun_prop
  · simp only [shearFlow, hi, ite_false]
    exact contDiff_const

/-- The explicit gradient is smooth. -/
theorem shearFlowGrad_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => shearFlowGrad z) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  by_cases hij : i = 0 ∧ j = 1
  · rcases hij with ⟨rfl, rfl⟩
    simp only [shearFlowGrad, and_self, ite_true]
    fun_prop
  · simp only [shearFlowGrad, hij, ite_false]
    exact contDiff_const

/-- The shear is nonzero at a point strictly inside its time interval. -/
theorem shearFlow_ne_zero :
    ∃ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo (0 : ℝ) 1),
      shearFlow z ≠ 0 := by
  refine ⟨(![0, Real.pi / 2, 0], (1 / 2 : ℝ)), ?_, ?_⟩
  · change True ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
    norm_num
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    simp [shearFlow] at h0

/-- Spatial derivatives of the scalar amplitude. -/
theorem shearAmplitude_spatial (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial shearAmplitude j z = if j = 1 then shearSlope z else 0 := by
  have h := ((hasFDerivAt_apply (1 : Fin 3) z.1).sin).const_mul (Real.exp (-z.2))
  change (fderiv ℝ (fun x : Vec3 => Real.exp (-z.2) * Real.sin (x 1)) z.1)
    (basisVec j) = _
  rw [h.fderiv]
  by_cases hj : j = 1 <;> simp [hj, shearSlope, basisVec, eq_comm]

/-- Spatial derivatives of the transverse slope. -/
theorem shearSlope_spatial (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial shearSlope j z = if j = 1 then -shearAmplitude z else 0 := by
  have h := ((hasFDerivAt_apply (1 : Fin 3) z.1).cos).const_mul (Real.exp (-z.2))
  change (fderiv ℝ (fun x : Vec3 => Real.exp (-z.2) * Real.cos (x 1)) z.1)
    (basisVec j) = _
  rw [h.fderiv]
  by_cases hj : j = 1 <;> simp [hj, shearAmplitude, basisVec, eq_comm]

/-- The amplitude satisfies exponential time decay. -/
theorem shearAmplitude_time (z : Vec3 × ℝ) :
    timePartial shearAmplitude z = -shearAmplitude z := by
  have h := (((hasDerivAt_id z.2).neg).exp).mul_const (Real.sin (z.1 1))
  change (fderiv ℝ (fun s : ℝ => Real.exp ((-id) s) * Real.sin (z.1 1)) z.2) 1 = _
  rw [h.hasFDerivAt.fderiv]
  simp [shearAmplitude]

/-- The supplied matrix is the weak spatial gradient on every open spatial set. -/
theorem shearFlow_weakGradient (U : Set Vec3) (s : ℝ) (i : Fin 3) :
    HasWeakGradientOn U (fun x => shearFlow (x, s) i)
      (fun x => shearFlowGrad (x, s) i) := by
  by_cases hi : i = 0
  · subst i
    have hs : ContDiff ℝ 1 (fun x : Vec3 => shearAmplitude (x, s)) := by
      exact (shearAmplitude_smooth.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
    have hw := HasWeakGradientOn.of_contDiff (U := U) hs
    intro j
    convert hw j using 1
    · rfl
    · funext x
      have hd := shearAmplitude_spatial (x, s) j
      simpa [spatialPartial, shearFlowGrad, shearSlope] using hd.symm
  · have hw := HasWeakGradientOn.of_contDiff (U := U)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)))
    have he : (fun x => shearFlowGrad (x, s) i) = (fun _ : Vec3 => (0 : Vec3)) := by
      funext x j
      simp [shearFlowGrad, hi]
    rw [he]
    simp only [shearFlow, hi, ite_false]
    convert hw using 1
    funext x j
    simp

end CKN
