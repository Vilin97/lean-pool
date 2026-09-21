/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Smooth-core Green identities for the free--free beam

This scratch module proves the classical integration-by-parts identities that
must underlie any Sobolev realization of the fourth derivative on `[0,1]`.
It is independent of the choice of completed graph domain.

A fourth-order datum stores five real functions together with four derivative
relations.  The Green boundary concomitant

`u v''' - u' v'' + u'' v' - u''' v`

has derivative `u v'''' - u'''' v`.  The free endpoint conditions kill the
concomitant.  A second concomitant gives positivity:

`integral u u'''' = integral (u'')^2`.

These are the exact algebraic boundary identities needed in the later
closed-operator symmetry and positivity proofs.  The complex version follows
by applying the real result to real and imaginary parts, or by repeating the
same proof with conjugation as a real-linear operation.
-/

open Set
open scoped Interval

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

noncomputable section

/-- Classical fourth-order derivative data on the real line.  Continuity is
recorded explicitly so all interval integrals needed by the fundamental theorem
are immediately available. -/
structure FourthOrderData where
  f0 : ℝ → ℝ
  f1 : ℝ → ℝ
  f2 : ℝ → ℝ
  f3 : ℝ → ℝ
  f4 : ℝ → ℝ
  continuous0 : Continuous f0
  continuous1 : Continuous f1
  continuous2 : Continuous f2
  continuous3 : Continuous f3
  continuous4 : Continuous f4
  deriv0 : ∀ x, HasDerivAt f0 (f1 x) x
  deriv1 : ∀ x, HasDerivAt f1 (f2 x) x
  deriv2 : ∀ x, HasDerivAt f2 (f3 x) x
  deriv3 : ∀ x, HasDerivAt f3 (f4 x) x

namespace FourthOrderData

/-- Free--free endpoint conditions for the second and third derivatives. -/
def FreeBoundary (u : FourthOrderData) : Prop :=
  u.f2 0 = 0 ∧ u.f3 0 = 0 ∧ u.f2 1 = 0 ∧ u.f3 1 = 0

/-- Lagrange's fourth-order boundary concomitant. -/
def greenBoundary (u v : FourthOrderData) (x : ℝ) : ℝ :=
  u.f0 x * v.f3 x - u.f1 x * v.f2 x +
    u.f2 x * v.f1 x - u.f3 x * v.f0 x

/-- The derivative of the fourth-order Green concomitant is the skew
fourth-derivative pairing. -/
theorem hasDerivAt_greenBoundary
    (u v : FourthOrderData) (x : ℝ) :
    HasDerivAt (greenBoundary u v)
      (u.f0 x * v.f4 x - u.f4 x * v.f0 x) x := by
  have h :=
    ((((u.deriv0 x).mul (v.deriv3 x)).sub
      ((u.deriv1 x).mul (v.deriv2 x))).add
      ((u.deriv2 x).mul (v.deriv1 x))).sub
      ((u.deriv3 x).mul (v.deriv0 x))
  have heq : u.f0 x * v.f4 x - u.f4 x * v.f0 x =
      u.f1 x * v.f3 x + u.f0 x * v.f4 x -
          (u.f2 x * v.f2 x + u.f1 x * v.f3 x) +
          (u.f3 x * v.f1 x + u.f2 x * v.f2 x) -
        (u.f4 x * v.f0 x + u.f3 x * v.f1 x) := by ring
  rw [heq]
  exact h

/-- The Green integrand is continuous. -/
theorem continuous_greenIntegrand (u v : FourthOrderData) :
    Continuous fun x => u.f0 x * v.f4 x - u.f4 x * v.f0 x :=
  (u.continuous0.mul v.continuous4).sub
    (u.continuous4.mul v.continuous0)

/-- Fourth-order Green formula before imposing boundary conditions. -/
theorem integral_green_formula (u v : FourthOrderData) :
    (∫ x in (0 : ℝ)..1,
        (u.f0 x * v.f4 x - u.f4 x * v.f0 x)) =
      greenBoundary u v 1 - greenBoundary u v 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_greenBoundary u v x)
    ((continuous_greenIntegrand u v).intervalIntegrable _ _)

/-- The Green concomitant vanishes at either free endpoint. -/
theorem greenBoundary_eq_zero_of_freeEndpoint
    (u v : FourthOrderData) {x : ℝ}
    (hu2 : u.f2 x = 0) (hu3 : u.f3 x = 0)
    (hv2 : v.f2 x = 0) (hv3 : v.f3 x = 0) :
    greenBoundary u v x = 0 := by
  unfold greenBoundary
  rw [hu2, hu3, hv2, hv3]
  ring

/-- Green symmetry for two smooth free--free beam functions. -/
theorem integral_free_green_symmetry
    (u v : FourthOrderData)
    (hu : u.FreeBoundary) (hv : v.FreeBoundary) :
    (∫ x in (0 : ℝ)..1, u.f0 x * v.f4 x) =
      ∫ x in (0 : ℝ)..1, u.f4 x * v.f0 x := by
  rcases hu with ⟨hu20, hu30, hu21, hu31⟩
  rcases hv with ⟨hv20, hv30, hv21, hv31⟩
  have hgreen := integral_green_formula u v
  have h0 : greenBoundary u v 0 = 0 :=
    greenBoundary_eq_zero_of_freeEndpoint u v hu20 hu30 hv20 hv30
  have h1 : greenBoundary u v 1 = 0 :=
    greenBoundary_eq_zero_of_freeEndpoint u v hu21 hu31 hv21 hv31
  rw [h0, h1, sub_zero] at hgreen
  have hc1 : Continuous fun x : ℝ => u.f0 x * v.f4 x :=
    u.continuous0.mul v.continuous4
  have hc2 : Continuous fun x : ℝ => u.f4 x * v.f0 x :=
    u.continuous4.mul v.continuous0
  have hsplit := intervalIntegral.integral_sub
    (hc1.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1)
    (hc2.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1)
  rw [hsplit] at hgreen
  linarith

/-- Boundary expression for the free-beam energy identity. -/
def energyBoundary (u : FourthOrderData) (x : ℝ) : ℝ :=
  u.f0 x * u.f3 x - u.f1 x * u.f2 x

/-- The energy boundary expression differentiates to
`u u'''' - (u'')^2`. -/
theorem hasDerivAt_energyBoundary
    (u : FourthOrderData) (x : ℝ) :
    HasDerivAt (energyBoundary u)
      (u.f0 x * u.f4 x - u.f2 x ^ 2) x := by
  have h := ((u.deriv0 x).mul (u.deriv3 x)).sub
    ((u.deriv1 x).mul (u.deriv2 x))
  have heq : u.f0 x * u.f4 x - u.f2 x ^ 2 =
      u.f1 x * u.f3 x + u.f0 x * u.f4 x -
        (u.f2 x * u.f2 x + u.f1 x * u.f3 x) := by ring
  rw [heq]
  exact h

/-- The free-beam energy integrand is continuous. -/
theorem continuous_energyIntegrand (u : FourthOrderData) :
    Continuous fun x => u.f0 x * u.f4 x - u.f2 x ^ 2 :=
  (u.continuous0.mul u.continuous4).sub
    (u.continuous2.pow 2)

/-- Energy identity with its endpoint term visible. -/
theorem integral_energy_formula (u : FourthOrderData) :
    (∫ x in (0 : ℝ)..1, (u.f0 x * u.f4 x - u.f2 x ^ 2)) =
      energyBoundary u 1 - energyBoundary u 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_energyBoundary u x)
    ((continuous_energyIntegrand u).intervalIntegrable _ _)

/-- The energy boundary term vanishes when the second and third derivatives
vanish at the endpoint. -/
theorem energyBoundary_eq_zero_of_freeEndpoint
    (u : FourthOrderData) {x : ℝ}
    (hu2 : u.f2 x = 0) (hu3 : u.f3 x = 0) :
    energyBoundary u x = 0 := by
  unfold energyBoundary
  rw [hu2, hu3]
  ring

/-- Positivity identity on the smooth free--free beam core. -/
theorem integral_free_energy
    (u : FourthOrderData) (hu : u.FreeBoundary) :
    (∫ x in (0 : ℝ)..1, u.f0 x * u.f4 x) =
      ∫ x in (0 : ℝ)..1, u.f2 x ^ 2 := by
  rcases hu with ⟨hu20, hu30, hu21, hu31⟩
  have henergy := integral_energy_formula u
  have h0 : energyBoundary u 0 = 0 :=
    energyBoundary_eq_zero_of_freeEndpoint u hu20 hu30
  have h1 : energyBoundary u 1 = 0 :=
    energyBoundary_eq_zero_of_freeEndpoint u hu21 hu31
  rw [h0, h1, sub_zero] at henergy
  have hc1 : Continuous fun x : ℝ => u.f0 x * u.f4 x :=
    u.continuous0.mul u.continuous4
  have hc2 : Continuous fun x : ℝ => u.f2 x ^ 2 := u.continuous2.pow 2
  have hsplit := intervalIntegral.integral_sub
    (hc1.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1)
    (hc2.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1)
  rw [hsplit] at henergy
  linarith

/-- Nonnegativity of the smooth free-beam quadratic form. -/
theorem integral_free_energy_nonneg
    (u : FourthOrderData) (hu : u.FreeBoundary) :
    0 ≤ ∫ x in (0 : ℝ)..1, u.f0 x * u.f4 x := by
  rw [integral_free_energy u hu]
  exact intervalIntegral.integral_nonneg
    (le_of_lt zero_lt_one)
    (fun x _ => sq_nonneg (u.f2 x))

end FourthOrderData

end

end FreeBeam
end DavisKahan
end TauCeti
