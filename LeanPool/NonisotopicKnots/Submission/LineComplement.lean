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

import LeanPool.NonisotopicKnots.ChallengeDeps
import LeanPool.NonisotopicKnots.Submission.Invariant
import LeanPool.NonisotopicKnots.Submission.PuncturedPlane

/-!
# Reusable brick: the complement of a line in ℝ³ has abelian fundamental group

The complement of the `z`-axis in `ℝ³` deformation-retracts (linearly in the `z`-coordinate) onto
the punctured `xy`-plane, hence is homotopy equivalent to the punctured plane
`{w : ℂ // w ≠ 0}`.  Transporting `Submission.PuncturedPlane.punctured_pi1_comm` across this
homotopy equivalence shows its `π₁` is abelian.

This is an on-route brick toward the unknot side of `exists_nonisotopic_knots` (see `PLAN.md`):
under the inversion model `ℝ³ ∖ (round circle) ≅ (ℝ³ ∖ line) ∖ {pt}`, the relevant base space is
a line complement.
-/

open LeanEval.KnotTheory
open scoped Topology unitInterval

noncomputable section

namespace Submission.LineComplement

/-- The complement of the `z`-axis in `ℝ³`. -/
abbrev LineCompl : Type := {p : R3 // p 0 ≠ 0 ∨ p 1 ≠ 0}

open Submission.PuncturedPlane (Punctured)

/-
The image of a point of `LineCompl` under `p ↦ p₀ + p₁·i` is nonzero.
-/
lemma toPlane_ne (p : LineCompl) :
    ((p : R3) 0 : ℂ) + ((p : R3) 1 : ℂ) * Complex.I ≠ 0 := by
      cases p.2 <;> simp_all +decide [ Complex.ext_iff ]

/-- Map `LineCompl → Punctured`, `p ↦ p₀ + p₁·i`. -/
def toPlaneFun (p : LineCompl) : Punctured :=
  ⟨((p : R3) 0 : ℂ) + ((p : R3) 1 : ℂ) * Complex.I, toPlane_ne p⟩

lemma continuous_toPlaneFun : Continuous toPlaneFun := by
  refine' Continuous.subtype_mk _ _;
  refine' Continuous.add _ _; all_goals fun_prop

/-- `toPlaneFun` as a continuous map. -/
def toPlane : C(LineCompl, Punctured) := ⟨toPlaneFun, continuous_toPlaneFun⟩

/-
The section's image lies in the line complement.
-/
lemma fromPlane_mem (w : Punctured) :
    (EuclideanSpace.single 0 (w : ℂ).re + EuclideanSpace.single 1 (w : ℂ).im : R3) 0 ≠ 0 ∨
    (EuclideanSpace.single 0 (w : ℂ).re + EuclideanSpace.single 1 (w : ℂ).im : R3) 1 ≠ 0 := by
  by_cases hre : w.val.re = 0 <;> by_cases him : w.val.im = 0 <;> simp_all +decide [ Complex.ext_iff ];
  exact w.2 ( Complex.ext hre him )

/-- Section `Punctured → LineCompl`, `w ↦ (Re w, Im w, 0)`. -/
def fromPlaneFun (w : Punctured) : LineCompl :=
  ⟨EuclideanSpace.single 0 (w : ℂ).re + EuclideanSpace.single 1 (w : ℂ).im, fromPlane_mem w⟩

lemma continuous_fromPlaneFun : Continuous fromPlaneFun := by
  refine' continuous_induced_rng.mpr _;
  refine' Continuous.congr _ _;
  exact fun x => x.val.re • EuclideanSpace.single 0 1 + x.val.im • EuclideanSpace.single 1 1;
  · fun_prop;
  · intro x; ext i; fin_cases i <;> simp +decide [ fromPlaneFun ] ;

/-- Section as a continuous map. -/
def fromPlane : C(Punctured, LineCompl) := ⟨fromPlaneFun, continuous_fromPlaneFun⟩

/-
`toPlane ∘ fromPlane = id` on `Punctured`.
-/
lemma toPlane_comp_fromPlane : (toPlane.comp fromPlane) = ContinuousMap.id Punctured := by
  ext w; simp [toPlane, fromPlane];
  unfold toPlaneFun fromPlaneFun;
  simp +decide [ Complex.ext_iff ]

/-
The image of the deformation retraction at time `t` lies in the line complement
(the `x,y`-coordinates are untouched).
-/
lemma retract_mem (t : ℝ) (p : LineCompl) :
    (EuclideanSpace.single 0 ((p : R3) 0) + EuclideanSpace.single 1 ((p : R3) 1)
      + EuclideanSpace.single 2 ((1 - t) * (p : R3) 2) : R3) 0 ≠ 0 ∨
    (EuclideanSpace.single 0 ((p : R3) 0) + EuclideanSpace.single 1 ((p : R3) 1)
      + EuclideanSpace.single 2 ((1 - t) * (p : R3) 2) : R3) 1 ≠ 0 := by
        cases p.2 <;> simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three ]

/-
The linear deformation retraction collapsing the `z`-coordinate, as the underlying map.
-/
def retractMap : C(↑unitInterval × LineCompl, LineCompl) :=
  ⟨fun q => ⟨EuclideanSpace.single 0 ((q.2 : R3) 0) + EuclideanSpace.single 1 ((q.2 : R3) 1)
      + EuclideanSpace.single 2 ((1 - (q.1 : ℝ)) * (q.2 : R3) 2), retract_mem _ _⟩, by
        apply_rules [ Continuous.subtype_mk, Continuous.add, Continuous.mul, continuous_const, continuous_id ];
        · refine' Continuous.comp _ _;
          · fun_prop;
          · refine' continuous_pi_iff.mpr _;
            intro i; fin_cases i <;> simp +decide [ continuous_const ] ;
            fun_prop;
        · refine' Continuous.comp _ _;
          · fun_prop;
          · refine' continuous_pi_iff.mpr _;
            intro i; fin_cases i <;> simp +decide [ continuous_const ] ;
            fun_prop;
        · refine' Continuous.congr _ _;
          exact fun x => ( 1 - x.1.val ) • ( x.2.val 2 ) • EuclideanSpace.single 2 1;
          · fun_prop;
          · intro x; ext i; by_cases hi : i = 2 <;> simp +decide [ hi ] ;⟩

lemma retractMap_zero (p : LineCompl) : retractMap (0, p) = p := by
  ext i; fin_cases i <;> simp [retractMap]

lemma retractMap_one (p : LineCompl) : retractMap (1, p) = (fromPlane.comp toPlane) p := by
  -- By definition of `fromPlane` and `toPlane`, we have `fromPlane (toPlane p) = p`.
  ext i; fin_cases i <;> simp [fromPlane, toPlane];
  · unfold retractMap fromPlaneFun toPlaneFun; simp +decide [ EuclideanSpace.single_apply ] ;
  · simp +decide [ fromPlaneFun, toPlaneFun ];
    unfold retractMap; aesop;
  · unfold retractMap fromPlaneFun toPlaneFun; aesop;

/-- The deformation-retraction homotopy from `id` to `fromPlane ∘ toPlane`. -/
def retractHomotopy :
    (ContinuousMap.id LineCompl).Homotopy (fromPlane.comp toPlane) where
  toContinuousMap := retractMap
  map_zero_left := retractMap_zero
  map_one_left := retractMap_one

/-- The homotopy equivalence between the line complement and the punctured plane. -/
def hequiv : ContinuousMap.HomotopyEquiv LineCompl Punctured where
  toFun := toPlane
  invFun := fromPlane
  left_inv := ContinuousMap.Homotopic.symm ⟨retractHomotopy⟩
  right_inv := by rw [toPlane_comp_fromPlane]

/-- **Reusable brick.** The fundamental group of the complement of a line in `ℝ³` is abelian. -/
theorem lineCompl_pi1_comm (x : LineCompl) (a b : FundamentalGroup LineCompl x) :
    a * b = b * a := by
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homotopyEquiv hequiv x
  exact ψ.injective (by rw [map_mul, map_mul, Submission.PuncturedPlane.punctured_pi1_comm])

end Submission.LineComplement