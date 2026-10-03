/-
Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Tuomo Kuusi
-/
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
`H¹(U)` is modeled here by explicit witnesses: a function, a candidate weak
gradient, `L²` control on both, and the integration-by-parts identity against
smooth compactly supported tests. `H¹₀(U)` adds the usual approximation package
by smooth compactly supported functions supported in `U`.
-/

@[expose] public section

namespace Homogenization

/-- Square integrability with respect to Lebesgue measure restricted to a domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)

/-- Coordinatewise square integrability of a gradient field on a domain. -/
def GradMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

/-- Square-integrable scalar function equipped with a square-integrable weak gradient. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  /-- Scalar representative of the H¹ function. -/
  toFun : Vec d → ℝ
  /-- Coordinate weak gradient of the H¹ function. -/
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Membership in H¹ expressed by existence of a bundled function with the same representative. -/
def MemH1 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H1Function U, v.toFun = u

/-- H¹ function approximable by smooth functions compactly supported inside the domain. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  /-- Smooth compactly supported approximating sequence for the zero-boundary Sobolev function. -/
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

/-- Membership in H¹₀ expressed by existence of a bundled zero-boundary Sobolev function. -/
def MemH10 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H10Function U, v.toH1Function.toFun = u

/-- Vanishing Lebesgue integral over the specified domain. -/
noncomputable def MeanZeroOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∫ x in U, u x ∂MeasureTheory.volume = 0

end Homogenization
