/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentApprox
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero

/-! # Reflection Parent Smooth Approx -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

variable {d : ℕ} {m : ℤ}

/-!
# Smooth approximation after parent-cube reflection

This file packages the clean part of the reflected-parent approximation step:
smooth convex-domain approximants on the original cube converge after all-face
reflection in the parent cube.  It intentionally does not assert that the
reflected smooth representatives are already parent-cube `H¹` functions; that
is the remaining trace/gluing bridge.
-/

/-- Smooth convex approximants on the origin cube converge, after all-face
scalar reflection, to the reflected scalar target in parent-cube `L²`. -/
theorem tendsto_toScalarL2_openCubeSet_succ_originCube_reflectedScalar_convexApproxSmoothH1
    (u : H1Function (openCubeSet (originCube d m)))
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet (originCube d m))
    (hr : 0 < r) :
    Filter.Tendsto
      (fun n =>
        toScalarL2
          (memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
            (m := m)
            (H1Function.convexApproxSmoothH1
              (U := openCubeSet (originCube d m))
              (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) u x0 hr n).memL2))
      Filter.atTop
      (nhds
        (toScalarL2
          (memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
            (m := m) u.memL2))) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  let ψ : ℕ → H1Function (openCubeSet (originCube d m)) := fun n =>
    H1Function.convexApproxSmoothH1 (U := openCubeSet (originCube d m)) hU u x0 hr n
  have hψ :
      Filter.Tendsto (fun n => (ψ n).toScalarL2) Filter.atTop
        (nhds u.toScalarL2) := by
    simpa [ψ, hU] using
      H1Function.tendsto_convexApproxSmoothH1_toScalarL2
        (U := openCubeSet (originCube d m)) hU u hball hr
  have hraw :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0) := by
    exact
      tendsto_eLpNorm_of_tendsto_toScalarL2
        (U := openCubeSet (originCube d m))
        (F := fun n => (ψ n).toFun) (G := u.toFun)
        (hF := fun n => (ψ n).memL2) (hG := u.memL2) hψ
  simpa [ψ, hU] using
    tendsto_toScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
      (m := m) (F := fun n => (ψ n).toFun) (U := u.toFun)
      (hF := fun n => (ψ n).memL2) (hU := u.memL2) hraw

/-- Smooth convex approximant gradients on the origin cube converge
coordinatewise, after all-face vector-field reflection, to the reflected
gradient target in parent-cube `L²`. -/
theorem tendsto_toScalarL2_openCubeSet_succ_originCube_reflectedGradient_convexApproxSmoothH1_coord
    (u : H1Function (openCubeSet (originCube d m)))
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet (originCube d m))
    (hr : 0 < r) (j : Fin d) :
    Filter.Tendsto
      (fun n =>
        toScalarL2
          (memScalarL2_coord_of_memVectorL2
            (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
              (m := m)
              (H1Function.convexApproxSmoothH1
                (U := openCubeSet (originCube d m))
                (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) u x0 hr n).grad_memVectorL2)
            j))
      Filter.atTop
      (nhds
        (toScalarL2
          (memScalarL2_coord_of_memVectorL2
            (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
              (m := m) u.grad_memVectorL2)
            j))) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  let ψ : ℕ → H1Function (openCubeSet (originCube d m)) := fun n =>
    H1Function.convexApproxSmoothH1 (U := openCubeSet (originCube d m)) hU u x0 hr n
  have hψ :
      Filter.Tendsto (fun n => (ψ n).gradCoordToScalarL2 j) Filter.atTop
        (nhds (u.gradCoordToScalarL2 j)) := by
    simpa [ψ, hU] using
      H1Function.tendsto_convexApproxSmoothH1_gradCoordToScalarL2
        (U := openCubeSet (originCube d m)) hU u hball hr j
  have hraw :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => (ψ n).grad x j - u.grad x j) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0) := by
    exact
      tendsto_eLpNorm_of_tendsto_toScalarL2
        (U := openCubeSet (originCube d m))
        (F := fun n x => (ψ n).grad x j) (G := fun x => u.grad x j)
        (hF := fun n => (ψ n).grad_memL2 j) (hG := u.grad_memL2 j) hψ
  simpa [ψ, hU] using
    tendsto_toScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_coord
      (m := m) (G := fun n => (ψ n).grad) (H := u.grad) j
      (hG := fun n => (ψ n).grad_memVectorL2) (hH := u.grad_memVectorL2) hraw

end

end Homogenization
