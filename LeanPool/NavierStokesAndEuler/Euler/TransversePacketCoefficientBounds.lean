/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Algebra.Order.Star.Real

/-! Explicit polynomial coefficient budgets for the actual transverse potential and slow curl. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Data

open Set EulerSmoothLimit EulerMeanCoefficients EulerGevrey EulerOperatorGevreyCalculus
  EulerSourceNormalCoefficient EulerSourcePotentialCoefficient EulerTransverseBoundedFrame
  EulerTimeLpGramGevrey
open scoped ContDiff BoundedContinuousFunction

/-- Corrector coefficient radius, given by `R+4*Ri+1`. -/
def correctorCoefficientRadius (R Ri : ℝ) : ℝ := R+4*Ri+1

/-- Corrector coefficient amplitude, given by `1+C+3*C^2+3*Ri*C+27*(3*Ri*C)^2*(3*C^2)`. -/
def correctorCoefficientAmplitude (C Ri : ℝ) : ℝ :=
  1+C+3*C^2+3*Ri*C+27*(3*Ri*C)^2*(3*C^2)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCoefficientBounds1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCoefficientBounds2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCoefficientBounds3 : NormedAddCommGroup PotentialField :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds4 : NormedSpace ℝ PotentialField :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,PotentialField)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds5 : NormedAddCommGroup C(Icc (0 : ℝ)
    D.T,PotentialField) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds6 : NormedSpace ℝ C(Icc (0 : ℝ)
    D.T,PotentialField) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCoefficientBounds7 : NormedAddCommGroup (Space →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds8 : NormedSpace ℝ (Space →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds9 : NormedAddCommGroup NormalField :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds10 : NormedSpace ℝ NormalField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,NormalField)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds11 : NormedAddCommGroup C(Icc (0 : ℝ)
    D.T,NormalField) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,NormalField)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds12 : NormedSpace ℝ C(Icc (0 : ℝ)
    D.T,NormalField) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCoefficientBounds13 : NormedAddCommGroup (Space →ᵇ Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds14 : NormedSpace ℝ (Space →ᵇ Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds15 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space
    →ᵇ Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCoefficientBounds16 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ
    Space) := inferInstance

/-- All four coefficients used in C and C_t follow from the original F⁻¹ and M bounds. -/
theorem corrector_coefficient_bounds (R C Ri : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hRi : 0 ≤ Ri)
    (hInv : 2 * gramCost D.normalLower C 1 * (R + 1) ≤ Ri)
    (hI : ∀ n t x, ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C * majorant R 0 n)
    (hM : ∀ n t x, ‖iteratedFDeriv ℝ n (D.M.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C * majorant R 0 n) :
    0 ≤ correctorCoefficientRadius R Ri ∧ 0 ≤ correctorCoefficientAmplitude C Ri ∧
    ∀ n a,
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤
        correctorCoefficientAmplitude C Ri*majorant (correctorCoefficientRadius R Ri) 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
        correctorCoefficientAmplitude C Ri*majorant (correctorCoefficientRadius R Ri) 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
        correctorCoefficientAmplitude C Ri*majorant (correctorCoefficientRadius R Ri) 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
        correctorCoefficientAmplitude C Ri*majorant (correctorCoefficientRadius R Ri) 0 n := by
  let Rc := correctorCoefficientRadius R Ri
  let Cc := correctorCoefficientAmplitude C Ri
  have hRc : 0 ≤ Rc := by dsimp [Rc,correctorCoefficientRadius]; positivity
  have hRR : R ≤ Rc := by dsimp [Rc,correctorCoefficientRadius]; linarith
  have hIR : 4*Ri ≤ Rc := by dsimp [Rc,correctorCoefficientRadius]; linarith
  have hN : 0 ≤ 3*Ri*C := by positivity
  have hD : 0 ≤ 3*C^2 := by positivity
  have hDt : 0 ≤ 27*(3*Ri*C)^2*(3*C^2) := by positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc,correctorCoefficientAmplitude]; positivity
  have hC0 : C ≤ Cc := by dsimp [Cc,correctorCoefficientAmplitude]; nlinarith
  have hC1 : 3*C^2 ≤ Cc := by dsimp [Cc,correctorCoefficientAmplitude]; nlinarith
  have hCN : 3*Ri*C ≤ Cc := by dsimp [Cc,correctorCoefficientAmplitude]; nlinarith
  have hCT : 27*(3*Ri*C)^2*(3*C^2) ≤ Cc := by
    dsimp [Cc,correctorCoefficientAmplitude]
    nlinarith
  have hIb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C*majorant Rc 0 n :=
    (D.FInv.norm_iteratedFDeriv_translation_le n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hI n) a).trans
        (mul_le_mul_of_nonneg_left (majorant_radius_mono R Rc hR hRR 0 n) hC)
  have hMb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ C*majorant Rc 0 n :=
    (D.M.norm_iteratedFDeriv_translation_le n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hM n) a).trans
        (mul_le_mul_of_nonneg_left (majorant_radius_mono R Rc hR hRR 0 n) hC)
  have hnormal (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
      ‖iteratedFDeriv ℝ n (D.normal.field t : Space → Space) x‖ ≤ C*majorant R 0 n :=
    normalCoefficient_derivative_bound D.m₀ D.FInv D.m₀_unit n (C*majorant R 0 n) (hI n) t x
  have hNb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath
        (normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower)) a‖ ≤
          (3*Ri*C)*majorant Rc 0 n :=
    (normalFunctional_translation_bound D.normal D.normalLower D.normalLower_pos D.normal_lower
      R C Ri hR hC hInv hnormal n a).trans
        (mul_le_mul_of_nonneg_left (majorant_radius_mono (4*Ri) Rc (by positivity) hIR 0 n) hN)
  have hKb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
        (3*Ri*C)*majorant Rc 0 n :=
    (potentialCoefficient_translation_bound D.normal D.normalLower D.normalLower_pos D.normal_lower
      R C Ri hR hC hInv hnormal n a).trans
        (mul_le_mul_of_nonneg_left (majorant_radius_mono (4*Ri) Rc (by positivity) hIR 0 n) hN)
  have hIt (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤ (3*C^2)*majorant Rc 0
          n := by
    simpa only [pow_two, mul_assoc] using D.inverseDerivative_bound Rc C C hRc hC hC hIb hMb n a
  have hmt (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.normalDerivative) a‖ ≤ (3*C^2)*majorant Rc 0
          n := by
    simpa only [pow_two, mul_assoc] using D.normalDerivative_bound Rc C C hRc hC hC hIb hMb n a
  have hKt (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
        (27*(3*Ri*C)^2*(3*C^2))*majorant Rc 0 n :=
    potentialTimePath_bound D.normal D.normalDerivative D.normalLower D.normalLower_pos
        D.normal_lower
      D.normalDerivative_orbit Rc (3*Ri*C) (3*C^2) hRc hN hD hNb hmt n a
  refine ⟨hRc,hCc,fun n a => ?_⟩
  have hmj := majorant_nonneg Rc hRc 0 n
  exact ⟨(hIb n a).trans (mul_le_mul_of_nonneg_right hC0 hmj),
    (hIt n a).trans (mul_le_mul_of_nonneg_right hC1 hmj),
    (hKb n a).trans (mul_le_mul_of_nonneg_right hCN hmj),
    (hKt n a).trans (mul_le_mul_of_nonneg_right hCT hmj)⟩

end EulerTransversePacketProvider.Data
