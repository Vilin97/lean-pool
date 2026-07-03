/-
Copyright (c) 2026 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

import LeanPool.NonisotopicKnots.Submission.Invariant
import LeanPool.NonisotopicKnots.Submission.Sphere

/-!
# Reusable brick: punctured `ℝ³` is simply connected

Punctured Euclidean `3`-space `{x : ℝ³ // x ≠ 0}` deformation-retracts onto the unit `2`-sphere
`S²` via radial normalization `x ↦ x / ‖x‖` and the straight-line homotopy
`(t, x) ↦ x · ((1 - t) + t / ‖x‖)` (the scalar is strictly positive, so the image stays away from
`0`).  Transporting `Submission.Sphere`'s simple connectivity of `S²` across this homotopy
equivalence shows punctured `ℝ³` is simply connected.

This is the punctured-ball ingredient for the point-removal step of the unknot side of the
benchmark (see `PLAN.md`): a single point of a `3`-manifold has a neighbourhood whose puncture is
simply connected, which is exactly what a (general, nonabelian) van Kampen gluing needs.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission.PuncturedSpace

/-- Punctured Euclidean `3`-space as a subtype. -/
abbrev Punctured : Type := {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0}

open Submission.Sphere (S2)

/-
A point of `S²` is a nonzero vector.
-/
lemma sphere_ne_zero (s : S2) : (s : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  exact fun h => by simpa [ h ] using s.2;

/-
The radial normalization `x ↦ x / ‖x‖` lands on the unit sphere.
-/
lemma norm_smul_mem (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  simp +decide [ norm_smul, hx ]

/-- Normalization map `Punctured → S²`. -/
def toSphereFun (x : Punctured) : S2 := ⟨(‖(x : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (x : EuclideanSpace ℝ (Fin 3))), norm_smul_mem _ x.2⟩

lemma continuous_toSphereFun : Continuous toSphereFun := by
  apply Continuous.subtype_mk;
  exact Continuous.smul ( continuous_norm.comp continuous_subtype_val |> Continuous.inv₀ <| fun x => norm_ne_zero_iff.mpr x.2 ) continuous_subtype_val

/-- Normalization as a continuous map. -/
def toSphere : C(Punctured, S2) := ⟨toSphereFun, continuous_toSphereFun⟩

/-- Inclusion `S² → Punctured`. -/
def fromSphereFun (s : S2) : Punctured := ⟨(s : EuclideanSpace ℝ (Fin 3)), sphere_ne_zero s⟩

lemma continuous_fromSphereFun : Continuous fromSphereFun :=
  continuous_subtype_val.subtype_mk _

/-- Inclusion as a continuous map. -/
def fromSphere : C(S2, Punctured) := ⟨fromSphereFun, continuous_fromSphereFun⟩

/-
`toSphere ∘ fromSphere = id` on `S²` (since `‖s‖ = 1`).
-/
lemma toSphere_comp_fromSphere : (toSphere.comp fromSphere) = ContinuousMap.id S2 := by
  ext s; simp [toSphere, fromSphere];
  unfold toSphereFun fromSphereFun; aesop;

/-- The positive real scalar of the radial straight-line homotopy. -/
def retractScale (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ := (1 - t) + t / ‖x‖

lemma retractScale_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ≠ 0) : 0 < retractScale t x := by
  unfold retractScale;
  cases eq_or_lt_of_le ht0 <;> cases eq_or_lt_of_le ht1 <;> first | nlinarith [ norm_pos_iff.mpr hx, div_nonneg ht0 ( norm_nonneg x ) ] | simp_all +decide [ div_eq_mul_inv ] ;

/-
The underlying map of the radial straight-line homotopy is continuous.
-/
lemma continuous_retractMap_aux :
    Continuous (fun p : ↑unitInterval × Punctured =>
      (retractScale (p.1 : ℝ) (p.2 : EuclideanSpace ℝ (Fin 3))) • (p.2 : EuclideanSpace ℝ (Fin 3))) := by
  apply_rules [ Continuous.smul, Continuous.add, continuous_const, Continuous.div ];
  · fun_prop;
  · fun_prop;
  · fun_prop;
  · exact fun x => norm_ne_zero_iff.mpr x.2.2;
  · exact continuous_subtype_val.comp continuous_snd

/-- The radial straight-line homotopy as a continuous map. -/
def retractMap : C(↑unitInterval × Punctured, Punctured) :=
  ⟨fun p => ⟨(retractScale (p.1 : ℝ) (p.2 : EuclideanSpace ℝ (Fin 3))) • (p.2 : EuclideanSpace ℝ (Fin 3)), by
    have hpos : (0:ℝ) < retractScale (p.1 : ℝ) (p.2 : EuclideanSpace ℝ (Fin 3)) :=
      retractScale_pos p.1.2.1 p.1.2.2 p.2.2
    simp only [ne_eq, smul_eq_zero, not_or]
    exact ⟨ne_of_gt hpos, p.2.2⟩⟩, by
    apply Continuous.subtype_mk continuous_retractMap_aux⟩

lemma retractMap_zero (x : Punctured) : retractMap (0, x) = x := by
  -- By definition of `retractMap`, when `t = 0`, `retractMap (0, x) = x` because `retractScale 0 x = 1` and `1 • x = x`. Hence, we can conclude that `retractMap (0, x) = x`.
  simp [retractMap, retractScale]

lemma retractMap_one (x : Punctured) : retractMap (1, x) = (fromSphere.comp toSphere) x := by
  unfold retractMap fromSphere toSphere; simp [retractScale];
  unfold fromSphereFun toSphereFun; aesop;

/-- The straight-line homotopy from the identity of punctured space to `fromSphere ∘ toSphere`. -/
def retractHomotopy :
    (ContinuousMap.id Punctured).Homotopy (fromSphere.comp toSphere) where
  toContinuousMap := retractMap
  map_zero_left := retractMap_zero
  map_one_left := retractMap_one

/-- The homotopy equivalence between punctured `ℝ³` and `S²`. -/
def hequiv : ContinuousMap.HomotopyEquiv Punctured S2 where
  toFun := toSphere
  invFun := fromSphere
  left_inv := ContinuousMap.Homotopic.symm ⟨retractHomotopy⟩
  right_inv := by rw [toSphere_comp_fromSphere]

/-- **Reusable brick.** Punctured `ℝ³` is simply connected. -/
instance : SimplyConnectedSpace Punctured :=
  hequiv.simplyConnectedSpace

end Submission.PuncturedSpace