/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Analysis.FourthOrderODE.SmoothGreenIdentity
import LeanPool.DavisKahan.DavisKahan.Analysis.FourthOrderODE.ComplexGreenIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The smooth kernel of the free--free fourth derivative

The zero eigenspace of the free--free beam is the two-dimensional space of
affine functions.  This file proves the smooth-core statement directly from
the fundamental theorem of calculus.

No polynomial classification theorem is required.  Starting from `u'''' = 0`,
the endpoint conditions give `u''' = 0` and `u'' = 0`; hence `u'` is constant
and `u` is affine.  Both real- and complex-valued versions are included.
-/

open Set
open scoped Interval

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

noncomputable section

/-- Fundamental theorem in a form convenient for repeatedly integrating a
specified derivative from zero. -/
theorem eq_zero_value_add_intervalIntegral
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f f' : ℝ → G)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (x : ℝ) :
    f x = f 0 + ∫ t in (0 : ℝ)..x, f' t := by
  have hftc : (∫ t in (0 : ℝ)..x, f' t) = f x - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t)
      (hf'.intervalIntegrable _ _)
  rw [hftc]
  abel

/-- A differentiable Banach-valued function with zero derivative and zero value
at the origin vanishes identically. -/
theorem eq_zero_of_hasDerivAt_zero
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : ℝ → G)
    (hf : ∀ x, HasDerivAt f 0 x)
    (h0 : f 0 = 0) :
    ∀ x, f x = 0 := by
  intro x
  have h := eq_zero_value_add_intervalIntegral f (fun _ => (0 : G))
    hf continuous_const x
  simpa [h0] using h

/-- A function with constant derivative is affine. -/
theorem eq_affine_of_hasDerivAt_const
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : ℝ → G) (c : G)
    (hf : ∀ x, HasDerivAt f c x) :
    ∀ x, f x = f 0 + x • c := by
  intro x
  have h := eq_zero_value_add_intervalIntegral f (fun _ => c)
    hf continuous_const x
  simpa [intervalIntegral.integral_const] using h

namespace FourthOrderData

/-- If the fourth derivative vanishes, the free condition at zero forces the
third derivative to vanish everywhere. -/
theorem f3_eq_zero_of_f4_eq_zero
    (u : FourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f3 x = 0 := by
  apply eq_zero_of_hasDerivAt_zero u.f3
  · intro x
    simpa [h4 x] using u.deriv3 x
  · exact hu.2.1

/-- Under the same hypotheses, the second derivative vanishes everywhere. -/
theorem f2_eq_zero_of_f4_eq_zero
    (u : FourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f2 x = 0 := by
  have h3 := f3_eq_zero_of_f4_eq_zero u h4 hu
  apply eq_zero_of_hasDerivAt_zero u.f2
  · intro x
    simpa [h3 x] using u.deriv2 x
  · exact hu.1

/-- The first derivative of a smooth zero mode is constant. -/
theorem f1_eq_initial_of_f4_eq_zero
    (u : FourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f1 x = u.f1 0 := by
  have h2 := f2_eq_zero_of_f4_eq_zero u h4 hu
  intro x
  have haff := eq_affine_of_hasDerivAt_const u.f1 0
    (fun y => by simpa [h2 y] using u.deriv1 y) x
  simpa using haff

/-- Every real smooth free--free zero mode is affine. -/
theorem f0_eq_affine_of_f4_eq_zero
    (u : FourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f0 x = u.f0 0 + x * u.f1 0 := by
  have h1 := f1_eq_initial_of_f4_eq_zero u h4 hu
  intro x
  have haff := eq_affine_of_hasDerivAt_const u.f0 (u.f1 0)
    (fun y => by simpa [h1 y] using u.deriv0 y) x
  simpa [smul_eq_mul] using haff

/-- The real smooth kernel is contained in the affine two-parameter family. -/
theorem exists_affine_representation
    (u : FourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∃ a b : ℝ, ∀ x, u.f0 x = a + b * x := by
  refine ⟨u.f0 0, u.f1 0, ?_⟩
  intro x
  rw [f0_eq_affine_of_f4_eq_zero u h4 hu x]
  ring

end FourthOrderData

namespace ComplexFourthOrderData

/-- The third derivative of a complex smooth free zero mode vanishes. -/
theorem f3_eq_zero_of_f4_eq_zero
    (u : ComplexFourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f3 x = 0 := by
  apply eq_zero_of_hasDerivAt_zero u.f3
  · intro x
    simpa [h4 x] using u.deriv3 x
  · exact hu.2.1

/-- The second derivative of a complex smooth free zero mode vanishes. -/
theorem f2_eq_zero_of_f4_eq_zero
    (u : ComplexFourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f2 x = 0 := by
  have h3 := f3_eq_zero_of_f4_eq_zero u h4 hu
  apply eq_zero_of_hasDerivAt_zero u.f2
  · intro x
    simpa [h3 x] using u.deriv2 x
  · exact hu.1

/-- The first derivative of a complex smooth free zero mode is constant. -/
theorem f1_eq_initial_of_f4_eq_zero
    (u : ComplexFourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f1 x = u.f1 0 := by
  have h2 := f2_eq_zero_of_f4_eq_zero u h4 hu
  intro x
  have haff := eq_affine_of_hasDerivAt_const u.f1 0
    (fun y => by simpa [h2 y] using u.deriv1 y) x
  simpa using haff

/-- Every complex smooth free--free zero mode is affine. -/
theorem f0_eq_affine_of_f4_eq_zero
    (u : ComplexFourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∀ x, u.f0 x = u.f0 0 + x • u.f1 0 := by
  have h1 := f1_eq_initial_of_f4_eq_zero u h4 hu
  exact eq_affine_of_hasDerivAt_const u.f0 (u.f1 0)
    (fun y => by simpa [h1 y] using u.deriv0 y)

/-- The complex smooth kernel is contained in the complex affine family. -/
theorem exists_affine_representation
    (u : ComplexFourthOrderData)
    (h4 : ∀ x, u.f4 x = 0)
    (hu : u.FreeBoundary) :
    ∃ a b : ℂ, ∀ x, u.f0 x = a + (x : ℂ) * b := by
  refine ⟨u.f0 0, u.f1 0, ?_⟩
  intro x
  rw [f0_eq_affine_of_f4_eq_zero u h4 hu x]
  simp only [Complex.real_smul]

end ComplexFourthOrderData

end

end FreeBeam
end DavisKahan
end TauCeti
