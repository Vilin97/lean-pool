/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.MixedTimeSpace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart

/-!
# Mixed time--space regularity for intrinsic derivatives

The slicewise Ricci-flow API differentiates metric components in time at fixed spatial points.
This file supplies the missing local bridge when the actual scalar field on spacetime is `C²`.
The proof goes through an extended manifold chart, uses equality of mixed Euclidean derivatives,
and transfers the result back to `mvfderiv`; it does not postulate a connection derivative.
-/

@[expose] public section

@[expose] public noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [I.Boundaryless] [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
theorem hasDerivAt_mvfderiv_of_joint_contMDiff
    (F : ℝ → M → ℝ) (Fdot : M → ℝ)
    {t : ℝ}
    (hF : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => F p.1 p.2))
    (hFdot : ∀ y : M, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (x : M) (hFdotSpace : MDiffAt Fdot x) (v : TM x) :
    HasDerivAt
      (fun τ => _root_.mvfderiv (I := I) (fun y => F τ y) x v)
      (_root_.mvfderiv (I := I) Fdot x v) t := by
  let φ := extChartAt I x
  let z := φ x
  let Fchart : ℝ → E → ℝ := fun τ y => F τ (φ.symm y)
  let FdotChart : E → ℝ := fun y => Fdot (φ.symm y)
  have hcoord := (contMDiffAt_iff.mp (hF (t, x))).2
  rw [extChartAt_prod] at hcoord
  have hrange : Set.range (↑(𝓘(ℝ, ℝ).prod I)) =
      (Set.univ : Set (ℝ × E)) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange] at hcoord
  have hFcoord : ContDiffAt ℝ 2 (fun p : ℝ × E => Fchart p.1 p.2) (t, z) := by
    simpa [Fchart, z, φ, ContDiffAt, Function.comp_def,
      PartialEquiv.prod_coe_symm, chartAt_self_eq] using hcoord
  have hFdotChart : ∀ y : E,
      HasDerivAt (fun τ : ℝ => Fchart τ y) (FdotChart y) t := by
    intro y
    simpa [Fchart, FdotChart] using hFdot (φ.symm y)
  let X : ∀ y : M, TM y :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v
  let vCoord : E :=
    VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (Set.range I) z
  have hmixed := PoincareCurvature.hasDerivAt_fderiv_space_of_joint_contDiffAt
    Fchart FdotChart hFcoord hFdotChart vCoord
  have hsliceMDiff (τ : ℝ) : MDiffAt (fun y : M => F τ y) x := by
    have hcomp := ContMDiffAt.comp x (hF (τ, x))
      (contMDiffAt_const.prodMk contMDiffAt_id)
    exact hcomp.mdifferentiableAt (by norm_num)
  have hcoordEq : ∀ τ : ℝ,
      fderiv ℝ (fun y : E => Fchart τ y) z vCoord =
        _root_.mvfderiv (I := I) (fun y => F τ y) x v := by
    intro τ
    have hmv := CovariantDerivative.mvfderiv_apply_eq_fderivWithin_fixedChart
      (I := I) (M := M) (g := fun y : M => F τ y) (p := x) (y := x) (X := X)
      (mem_extChartAt_source (I := I) x) (hsliceMDiff τ)
    simpa [Fchart, vCoord, φ, z, X, CovariantDerivative.smoothExtend_apply,
      chartAt_self_eq, ModelWithCorners.Boundaryless.range_eq_univ,
      fderivWithin_univ, writtenInExtChartAt, Function.comp_def] using hmv.symm
  have hcoordEqDot :
      fderiv ℝ FdotChart z vCoord =
        _root_.mvfderiv (I := I) Fdot x v := by
    have hmv := CovariantDerivative.mvfderiv_apply_eq_fderivWithin_fixedChart
      (I := I) (M := M) (g := Fdot) (p := x) (y := x) (X := X)
      (mem_extChartAt_source (I := I) x) hFdotSpace
    simpa [FdotChart, vCoord, φ, z, X, CovariantDerivative.smoothExtend_apply,
      chartAt_self_eq, ModelWithCorners.Boundaryless.range_eq_univ,
      fderivWithin_univ, writtenInExtChartAt, Function.comp_def] using hmv.symm
  exact (hmixed.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => (hcoordEq τ).symm))).congr_deriv hcoordEqDot

end PoincareCurvature
