/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Existence
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Energy identities for absolutely continuous curves

The chain rule is separated from the ODE existence construction.  It applies to any
absolutely-continuous curve in a real inner-product space and can therefore be reused for linear
equations with measurable coefficients.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.ODE

variable {E : Type*} [NormedAddCommGroup E]

/-- Squaring the norm preserves absolute continuity on a compact interval. -/
theorem _root_.AbsolutelyContinuousOnInterval.norm_sq {y : ℝ → E} {a b : ℝ}
    (hy : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖y t‖ ^ 2) a b := by
  have hnormMap : LipschitzWith (1 : NNReal) (fun z : E => ‖z‖) :=
    lipschitzWith_one_norm
  have hnorm : AbsolutelyContinuousOnInterval (fun t => ‖y t‖) a b :=
    hnormMap.comp_absolutelyContinuousOnInterval hy
  have hsq := hnorm.mul hnorm
  exact hsq.congr (by intro t ht; simp [pow_two])

/-- The norm-square chain rule at every differentiability point. -/
theorem _root_.HasDerivAt.norm_sq_inner {y : ℝ → E} {y' : E} {t : ℝ}
    [InnerProductSpace ℝ E]
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => ‖y s‖ ^ 2) (2 * inner ℝ (y t) y') t := by
  simpa using hy.norm_sq

/-- Integral energy identity from the a.e. chain-rule derivative. -/
theorem integral_energy_eq_norm_sq_sub {y q : ℝ → E} {a b : ℝ}
    [InnerProductSpace ℝ E]
    (hy : AbsolutelyContinuousOnInterval (fun t => ‖y t‖ ^ 2) a b)
    (hq : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s => ‖y s‖ ^ 2) (2 * inner ℝ (y t) (q t)) t) :
    ∫ t in a..b, 2 * inner ℝ (y t) (q t) = ‖y b‖ ^ 2 - ‖y a‖ ^ 2 := by
  rw [← hy.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hq] with t ht
  intro hmem
  exact (ht (uIoc_subset_uIcc hmem)).deriv.symm

/-- The integral energy formula for an absolutely-continuous solution with an a.e. derivative. -/
theorem IsLinearIntegralSolution.energy_identity
    [CompleteSpace E]
    [InnerProductSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {f y : ℝ → E} {y₀ : E} {a b : ℝ}
    (hab : a ≤ b)
    (hy : IsLinearIntegralSolution A f y₀ a b y)
    (h_rhs : IntervalIntegrable (linearRhs A f y) volume a b) :
    ∫ t in a..b,
      2 * inner ℝ (y t) (A t (y t) + f t) = ‖y b‖ ^ 2 - ‖y a‖ ^ 2 := by
  have hACy := hy.absolutelyContinuousOnInterval hab h_rhs
  have hACsq := hACy.norm_sq
  have hderiv := hy.ae_hasDerivAt hab h_rhs
  have hchain : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s => ‖y s‖ ^ 2)
        (2 * inner ℝ (y t) (linearRhs A f y t)) t := by
    filter_upwards [hderiv] with t ht
    intro hmem
    exact (ht (by simpa [uIcc_of_le hab] using hmem)).norm_sq_inner
  simpa [linearRhs] using integral_energy_eq_norm_sq_sub hACsq hchain

/-- The squared norm of the constructed solution is absolutely continuous. -/
theorem LinearODEData.IsSolution.energy_absolutelyContinuous
     [InnerProductSpace ℝ E]
    {a b : ℝ} {hab : a ≤ b}
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    AbsolutelyContinuousOnInterval (fun t => ‖extendCurve hab u t‖ ^ 2) a b := by
  exact (hu.absolutelyContinuousOnInterval D).norm_sq

/-- A constructed solution satisfies the norm-square chain rule almost everywhere. -/
theorem LinearODEData.IsSolution.ae_energy_deriv
    [CompleteSpace E] [InnerProductSpace ℝ E]
    {a b : ℝ} {hab : a ≤ b}
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (fun s => ‖extendCurve hab u s‖ ^ 2)
        (2 * inner ℝ (extendCurve hab u t)
          (D.A t (extendCurve hab u t) + D.f t)) t := by
  filter_upwards [hu.ae_hasDerivAt D u] with t ht
  intro htmem
  simpa using (ht htmem).norm_sq_inner

end AVenhance.Infra.ODE
