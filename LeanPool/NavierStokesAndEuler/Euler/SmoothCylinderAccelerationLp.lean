/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual material acceleration has cylinder L² bounds with the
small source amplitudes retained. The product term uses one bounded
derivative coefficient and one L² velocity factor. -/

@[expose] public section


noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff BoundedContinuousFunction ENNReal

/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationLp1 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationLp2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] LiftTangent))
    := inferInstance
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
acceleration lᵖ. -/
local instance instSmoothCylinderAccelerationLp3 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _
local instance instSmoothCylinderAccelerationLp4 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := ⟨rfl⟩
local instance instSmoothCylinderAccelerationLp5 (n : ℕ) : FiniteDimensional ℝ (LiftTangent
    [×n]→L[ℝ] LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective

variable (P T : ℝ) [Fact (0 < P)]
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)

/-- Acceleration Lᵖ radius, given by `4*R+S+S₁`. -/
def accelerationLpRadius (R S S₁ : ℝ) : ℝ := 4*R+S+S₁

theorem accelerationField_memLp_and_bound (B R C S C₁ S₁ : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hC₁ : 0 ≤ C₁) (hS₁ : 0 ≤ S₁)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hLp : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial : ℝ) ^ 2)
    (hLp₁ : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm₁ : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C₁ * S₁ ^ j * (j.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P (accelerationField T A A₁ t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (accelerationField T A A₁ t) q n)
        2 (liftMeasure P)).toReal ≤
          (C₁+3*B*R*C)*(accelerationLpRadius R S S₁)^n*(n.factorial : ℝ)^2 := by
  let U := accelerationLpRadius R S S₁
  have hU : 0 ≤ U := by dsimp [U,accelerationLpRadius]; positivity
  have hRU : 4*R ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  have hSU : S ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  have hS₁U : S₁ ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  let f : LiftTangent → LiftTangent →L[ℝ] LiftTangent := fderiv ℝ (A.field t : LiftTangent →
      LiftTangent)
  let g : LiftTangent → LiftTangent := A.field t
  have hf : ContDiff ℝ ∞ f := (A.smooth t).fderiv_right (m := ∞) (by simp)
  have hg : ContDiff ℝ ∞ g := A.smooth t
  have hfB (j : ℕ) (q : LiftDomain P) :
      ‖iteratedFDeriv ℝ j f (sectionPoint P q)‖ ≤ (B*R)*majorant U 0 j := by
    rw [norm_iteratedFDeriv_fderiv]
    have h := field_jet_bound T A B R hb (j+1) t (sectionPoint P q)
    calc
      _ ≤ B*majorant R 1 j := by simpa only [majorant,mul_assoc] using h
      _ ≤ B*(R*majorant (4*R) 0 j) :=
        mul_le_mul_of_nonneg_left (majorant_one_le_radius_four R hR j) hB
      _ ≤ (B*R)*majorant U 0 j := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (majorant_radius_mono (4*R) U (by positivity) hRU 0 j)
          (mul_nonneg hB hR)
  have hgC (j : ℕ) :
      (eLpNorm (fun q => iteratedFDeriv ℝ j g (sectionPoint P q)) 2 (liftMeasure P)).toReal ≤
        C*majorant U 0 j := by
    calc
      _ ≤ C*S^j*(j.factorial : ℝ)^2 := hNorm t j
      _ = C*majorant S 0 j := by simp only [majorant,Nat.add_zero,mul_assoc]
      _ ≤ C*majorant U 0 j :=
        mul_le_mul_of_nonneg_left (majorant_radius_mono S U hS hSU 0 j) hC
  have hm : AEStronglyMeasurable
      (fun q => iteratedFDeriv ℝ n (fun y => f y (g y)) (sectionPoint P q)) (liftMeasure P) :=
    (((hf.clm_apply hg).continuous_iteratedFDeriv (m := n) (by simp)).measurable.comp
      (sectionPoint_measurable P)).aestronglyMeasurable
  obtain ⟨hp,hn⟩ := EulerGevreyProductLp.clm_apply_memLp_and_bound (liftMeasure P) (sectionPoint P)
    f g hf hg n hm U (B*R) C hU (mul_nonneg hB hR) hC 0 0
    (fun j _ => hfB j) (fun j _ => hLp t j) (fun j _ => hgC j)
  let v : LiftDomain P → LiftTangent [×n]→L[ℝ] LiftTangent :=
    fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n
  let w : LiftDomain P → LiftTangent [×n]→L[ℝ] LiftTangent :=
    fun q => iteratedFDeriv ℝ n (fun y => f y (g y)) (sectionPoint P q)
  have he : (fun q => jetSeries P (accelerationField T A A₁ t) q n) = v+w := by
    funext q
    exact fun_iteratedFDeriv_add_apply ((A₁.smooth t).contDiffAt.of_le (by simp))
      ((hf.clm_apply hg).contDiffAt.of_le (by simp))
  have hv : MemLp v 2 (liftMeasure P) := hLp₁ t n
  have hw : MemLp w 2 (liftMeasure P) := hp
  let H : Fin 2 → LiftDomain P → ℝ := fun i q => if i=0 then ‖v q‖ else ‖w q‖
  have hH (i : Fin 2) : MemLp (H i) 2 (liftMeasure P) := by
    fin_cases i
    · exact hv.norm
    · exact hw.norm
  have hmacc : AEStronglyMeasurable
      (fun q => jetSeries P (accelerationField T A A₁ t) q n) (liftMeasure P) :=
    (((accelerationField_contDiff T A A₁ t).continuous_iteratedFDeriv (m := n) (by
        simp)).measurable.comp
      (sectionPoint_measurable P)).aestronglyMeasurable
  have hdom (q : LiftDomain P) : ‖jetSeries P (accelerationField T A A₁ t) q n‖ ≤
      ∑ i : Fin 2, H i q := by
    rw [congrFun he q]
    simpa only [Fin.sum_univ_two,H,ite_true,Fin.isValue,one_ne_zero,ite_false,Pi.add_apply]
      using norm_add_le (v q) (w q)
  obtain ⟨hacc,hreal⟩ := EulerGevreyProductLp.finite_domination (liftMeasure P) Finset.univ
    (fun q => jetSeries P (accelerationField T A A₁ t) q n) hmacc H (fun i _ => hH i) hdom
  refine ⟨hacc,?_⟩
  have hreal' : (eLpNorm (fun q => jetSeries P (accelerationField T A A₁ t) q n)
      2 (liftMeasure P)).toReal ≤ (eLpNorm v 2 (liftMeasure P)).toReal+(eLpNorm w 2 (liftMeasure
          P)).toReal := by
    simpa only [Fin.sum_univ_two,H,ite_true,Fin.isValue,one_ne_zero,ite_false,eLpNorm_norm] using
        hreal
  have hn₁ : (eLpNorm v 2 (liftMeasure P)).toReal ≤ C₁*majorant U 0 n := by
    apply (hNorm₁ t n).trans
    simpa only [majorant,Nat.add_zero,mul_assoc] using
      mul_le_mul_of_nonneg_left (majorant_radius_mono S₁ U hS₁ hS₁U 0 n) hC₁
  exact hreal'.trans ((add_le_add hn₁ hn).trans_eq (by
    simp only [majorant,Nat.add_zero]; dsimp [U]; ring))

variable (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hA₁ : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A₁.field t (z.1, (c : ℝ) + z.2) = A₁.field t z)

include hA hA₁ in
omit [Fact (0 < P)] in
theorem accelerationField_deck (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent)
    :
    accelerationField T A A₁ t (z.1,(c : ℝ)+z.2)=accelerationField T A A₁ t z := by
  have hd : fderiv ℝ (A.field t : LiftTangent → LiftTangent) (z.1,(c : ℝ)+z.2) =
      fderiv ℝ (A.field t : LiftTangent → LiftTangent) z := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : LiftTangent [×1]→L[ℝ] LiftTangent => L (fun _ => v))
      (iteratedFDeriv_deck P (A.field t : LiftTangent → LiftTangent) (fun d w => hA d t w) 1 c z)
    simpa only [iteratedFDeriv_one_apply] using h
  simp only [accelerationField,hA,hA₁,hd]

end EulerSmoothCylinderFlow
