/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Analysis.FourthOrderODE.SmoothKernel
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic

/-!
# Explicit affine zero modes of the free--free beam

`SmoothKernel` proves that every smooth free zero mode is affine.  This file
constructs the reverse inclusion and records injectivity of the two-parameter
representation.  Together the two files identify the smooth kernel exactly.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Classical

noncomputable section

/-- Real affine fourth-order derivative data. -/
noncomputable def realAffineData (a b : ℝ) : FourthOrderData where
  f0 := fun x => a + b * x
  f1 := fun _ => b
  f2 := fun _ => 0
  f3 := fun _ => 0
  f4 := fun _ => 0
  continuous0 := continuous_const.add (continuous_const.mul continuous_id)
  continuous1 := continuous_const
  continuous2 := continuous_const
  continuous3 := continuous_const
  continuous4 := continuous_const
  deriv0 := fun x => by
    simpa [add_comm] using ((hasDerivAt_id x).const_mul b).add_const a
  deriv1 := fun x => hasDerivAt_const x b
  deriv2 := fun x => hasDerivAt_const x 0
  deriv3 := fun x => hasDerivAt_const x 0

/-- Value of the real affine mode at `x`. -/
@[simp] theorem realAffineData_f0 (a b x : ℝ) :
    (realAffineData a b).f0 x = a + b * x := rfl

/-- Its first derivative is the slope. -/
@[simp] theorem realAffineData_f1 (a b x : ℝ) :
    (realAffineData a b).f1 x = b := rfl

/-- Its second derivative vanishes. -/
@[simp] theorem realAffineData_f2 (a b x : ℝ) :
    (realAffineData a b).f2 x = 0 := rfl

/-- Its third derivative vanishes. -/
@[simp] theorem realAffineData_f3 (a b x : ℝ) :
    (realAffineData a b).f3 x = 0 := rfl

/-- Its fourth derivative vanishes -- which is what makes it a kernel element of `u'''' = 0`. -/
@[simp] theorem realAffineData_f4 (a b x : ℝ) :
    (realAffineData a b).f4 x = 0 := rfl

/-- Every real affine function satisfies the free endpoint conditions. -/
theorem realAffineData_freeBoundary (a b : ℝ) :
    (realAffineData a b).FreeBoundary := by
  simp [FourthOrderData.FreeBoundary]

/-- Every real affine function is a zero mode. -/
theorem realAffineData_zeroMode (a b : ℝ) :
    (∀ x, (realAffineData a b).f4 x = 0) ∧
      (realAffineData a b).FreeBoundary := by
  exact ⟨fun _ => rfl, realAffineData_freeBoundary a b⟩

/-- Parameters of a real affine datum are recovered from its value and first
derivative at zero. -/
theorem realAffineData_parameters
    {a b c d : ℝ}
    (h0 : (realAffineData a b).f0 0 = (realAffineData c d).f0 0)
    (h1 : (realAffineData a b).f1 0 = (realAffineData c d).f1 0) :
    a = c ∧ b = d := by
  constructor
  · simpa using h0
  · simpa using h1

/-- The two-parameter real affine representation is injective. -/
theorem realAffineData_injective :
    Function.Injective (fun p : ℝ × ℝ => realAffineData p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun u : FourthOrderData => u.f0 0) h
  have h1 := congrArg (fun u : FourthOrderData => u.f1 0) h
  obtain ⟨hac, hbd⟩ := realAffineData_parameters h0 h1
  cases hac
  cases hbd
  rfl

/-- Complex affine fourth-order derivative data. -/
noncomputable def complexAffineData (a b : ℂ) : ComplexFourthOrderData where
  f0 := fun x => a + (x : ℂ) * b
  f1 := fun _ => b
  f2 := fun _ => 0
  f3 := fun _ => 0
  f4 := fun _ => 0
  continuous0 := continuous_const.add
    (Complex.continuous_ofReal.mul continuous_const)
  continuous1 := continuous_const
  continuous2 := continuous_const
  continuous3 := continuous_const
  continuous4 := continuous_const
  deriv0 := fun x => by
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
      (hasDerivAt_id x).ofReal_comp
    simpa [add_comm] using (hx.mul_const b).add_const a
  deriv1 := fun x => hasDerivAt_const x b
  deriv2 := fun x => hasDerivAt_const x 0
  deriv3 := fun x => hasDerivAt_const x 0

/-- Value of the complex affine mode at `x`. -/
@[simp] theorem complexAffineData_f0 (a b : ℂ) (x : ℝ) :
    (complexAffineData a b).f0 x = a + (x : ℂ) * b := rfl

/-- Its first derivative is the slope. -/
@[simp] theorem complexAffineData_f1 (a b : ℂ) (x : ℝ) :
    (complexAffineData a b).f1 x = b := rfl

/-- Its second derivative vanishes. -/
@[simp] theorem complexAffineData_f2 (a b : ℂ) (x : ℝ) :
    (complexAffineData a b).f2 x = 0 := rfl

/-- Its third derivative vanishes. -/
@[simp] theorem complexAffineData_f3 (a b : ℂ) (x : ℝ) :
    (complexAffineData a b).f3 x = 0 := rfl

/-- Its fourth derivative vanishes, the complex counterpart of `realAffineData_f4`. -/
@[simp] theorem complexAffineData_f4 (a b : ℂ) (x : ℝ) :
    (complexAffineData a b).f4 x = 0 := rfl

/-- Every complex affine function satisfies the free endpoint conditions. -/
theorem complexAffineData_freeBoundary (a b : ℂ) :
    (complexAffineData a b).FreeBoundary := by
  simp [ComplexFourthOrderData.FreeBoundary]

/-- The complex affine parametrization is injective. -/
theorem complexAffineData_injective :
    Function.Injective (fun p : ℂ × ℂ => complexAffineData p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun u : ComplexFourthOrderData => u.f0 0) h
  have h1 := congrArg (fun u : ComplexFourthOrderData => u.f1 0) h
  simp at h0 h1
  simp [h0, h1]

end

end Classical
end FreeBeam
end DavisKahan
end TauCeti
