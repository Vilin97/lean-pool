/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow

/-! # Ergodic estimates after a periodic volume-preserving flow -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization

noncomputable section

theorem FlowAverages.zPeriodic_comp_flow {d : ℕ} {f : Vec d → ℝ}
    (hf : IsZPeriodic f) (X : PeriodicVolumePreservingDiffeomorphism d) :
    IsZPeriodic (fun x => f (X.toFun x)) := by
  intro x k
  change f (X.toFun (x + latticeVector k)) = f (X.toFun x)
  rw [X.lattice_equivariant x k]
  exact hf (X.toFun x) k

theorem FlowAverages.zPeriodic_square {d : ℕ} {f : Vec d → ℝ}
    (hf : IsZPeriodic f) : IsZPeriodic (fun x => f x ^ 2) := by
  intro x k
  exact congrArg (fun y : ℝ => y ^ 2) (hf x k)

/-- Flow version of the basic L¹ covariance estimate. The derivative premise
is placed on `f ∘ X`, which is the function to which the Fourier estimate is
applied. Deriving it from averaged derivative bounds on `f` requires a
separate quantitative composition theorem. -/
theorem cellAverage_flow_mul_sub_le_of_composedCoordinateAnalyticL1Bounds
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (X : PeriodicVolumePreservingDiffeomorphism d)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderivComp : HasCoordinateAnalyticL1Bounds
      (fun x => (f (X.toFun x) : ℂ)) Cf r)
    {g : Vec d → ℝ} (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 1 ≤ r * (N : ℝ)) :
    |cellAverage (fun x => f x * g (X.invFun x)) -
      cellAverage f * cellAverage g| ≤
      512 * Cf * cellAverage (fun x => |g x|) *
        (∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (N : ℝ)) / 1024) := by
  have hcompSmooth : ContDiff ℝ ∞ (fun x => f (X.toFun x)) :=
    hf.comp X.contDiff_toFun
  have hcompPer := FlowAverages.zPeriodic_comp_flow hper X
  have hbase := cellAverage_mul_sub_le_of_coordinateAnalyticL1Bounds
    hd hN hcompSmooth hcompPer Cf r hCf hr hderivComp hg hfast hNr
  have hprod := cellAverage_mul_comp_inv_eq hper (hfast.isZPeriodic hN) X
  have havg := cellAverage_comp_flow_eq f hper X
  calc
    _ = |cellAverage (fun x => f (X.toFun x) * g x) -
          cellAverage (fun x => f (X.toFun x)) * cellAverage g| := by
      rw [hprod, havg]
    _ ≤ _ := hbase

end

end AVenhance.Infra.Ergodic
