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
import LeanPool.NonisotopicKnots.Submission.Pi1Comm

/-!
# Reusable brick: the punctured plane has abelian fundamental group

We build an explicit `ContinuousMap.HomotopyEquiv` between the punctured complex plane
`{z : ℂ // z ≠ 0}` and `Circle`, via the radial normalization `z ↦ z / ‖z‖` and the
straight-line homotopy `(z, t) ↦ z * ((1 - t) + t / ‖z‖)` (which stays in the punctured plane
because the scalar is strictly positive).  Transporting abelianness of `π₁(Circle)`
(`Submission.Pi1Comm.circle_fundamentalGroup_comm`) across this homotopy equivalence
(`Submission.Invariant.fundamentalGroup_mulEquiv_of_homotopyEquiv`) shows `π₁` of the punctured
plane is abelian.

This is a foundational on-route brick toward the unknot side of `exists_nonisotopic_knots`
(see `PLAN.md`).
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission.PuncturedPlane

/-- The punctured complex plane as a subtype. -/
abbrev Punctured : Type := {z : ℂ // z ≠ 0}

/-
Membership of the normalization in `Circle`.
-/
lemma norm_div_mem (z : ℂ) (hz : z ≠ 0) :
    z / (‖z‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
      simp +decide [ Submonoid.unitSphere, norm_div, norm_mul, hz ]

/-
A point of `Circle` is a nonzero complex number.
-/
lemma circle_ne_zero (c : Circle) : (c : ℂ) ≠ 0 := by
  simp +zetaDelta at *

/-- Normalization map `Punctured → Circle`, `z ↦ z / ‖z‖`. -/
def toCircleFun (z : Punctured) : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), norm_div_mem _ z.2⟩

lemma continuous_toCircleFun : Continuous toCircleFun := by
  refine' Continuous.subtype_mk _ _;
  refine' Continuous.div _ _ _;
  · exact continuous_subtype_val;
  · fun_prop;
  · aesop

/-- `toCircleFun` as a continuous map. -/
def toCircle : C(Punctured, Circle) := ⟨toCircleFun, continuous_toCircleFun⟩

/-- Inclusion `Circle → Punctured`. -/
def fromCircleFun (c : Circle) : Punctured := ⟨(c : ℂ), circle_ne_zero c⟩

lemma continuous_fromCircleFun : Continuous fromCircleFun := by
  exact Continuous.subtype_mk continuous_subtype_val _

/-- Inclusion `Circle → Punctured` as a continuous map. -/
def fromCircle : C(Circle, Punctured) := ⟨fromCircleFun, continuous_fromCircleFun⟩

/-
`toCircle ∘ fromCircle = id` on `Circle` (definitionally, since `‖c‖ = 1`).
-/
lemma toCircle_comp_fromCircle : (toCircle.comp fromCircle) = ContinuousMap.id Circle := by
  ext c; simp +decide [ toCircleFun, fromCircleFun ] ;
  convert Subtype.ext ?_;
  convert div_eq_iff _ |>.2 _;
  · norm_num [ c.2 ];
    exact circle_ne_zero c;
  · simp +decide [ fromCircle, fromCircleFun ]

/-- The positive real scalar of the radial straight-line homotopy. -/
def retractScale (t : ℝ) (z : ℂ) : ℝ := (1 - t) + t / ‖z‖

lemma retractScale_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℂ} (hz : z ≠ 0) :
    0 < retractScale t z := by
      by_cases ht : t = 0 ∨ t = 1;
      · cases ht <;> simp +decide [ *, retractScale ];
      · exact add_pos_of_nonneg_of_pos ( sub_nonneg.2 ht1 ) ( div_pos ( lt_of_le_of_ne ht0 ( Ne.symm ( by tauto ) ) ) ( norm_pos_iff.2 hz ) )

/-
The underlying map of the radial straight-line homotopy.
-/
def retractMap : C(↑unitInterval × Punctured, Punctured) :=
  ⟨fun p => ⟨(p.2 : ℂ) * ((retractScale (p.1 : ℝ) (p.2 : ℂ) : ℝ) : ℂ), by
    have : (0:ℝ) < retractScale (p.1 : ℝ) (p.2 : ℂ) :=
      retractScale_pos p.1.2.1 p.1.2.2 p.2.2
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨p.2.2, by exact_mod_cast ne_of_gt this⟩⟩, by
      refine' Continuous.subtype_mk _ _;
      refine' Continuous.mul _ _;
      · exact continuous_subtype_val.comp continuous_snd;
      · refine' Continuous.comp ( Complex.continuous_ofReal ) _;
        refine' Continuous.add _ _;
        · exact continuous_const.sub ( continuous_subtype_val.comp continuous_fst );
        · exact Continuous.div ( continuous_subtype_val.comp continuous_fst ) ( continuous_norm.comp ( continuous_subtype_val.comp continuous_snd ) ) fun p => norm_ne_zero_iff.mpr p.2.2⟩

lemma retractMap_zero (z : Punctured) : retractMap (0, z) = z := by
  ext; simp [retractMap, retractScale]

lemma retractMap_one (z : Punctured) : retractMap (1, z) = (fromCircle.comp toCircle) z := by
  ext; simp [retractMap, retractScale, fromCircle, toCircle, fromCircleFun, toCircleFun];
  ring

/-- The straight-line homotopy `(t, z) ↦ z * ((1 - t) + t / ‖z‖)` from the identity of the
punctured plane to `fromCircle ∘ toCircle`. -/
def retractHomotopy :
    (ContinuousMap.id Punctured).Homotopy (fromCircle.comp toCircle) where
  toContinuousMap := retractMap
  map_zero_left := retractMap_zero
  map_one_left := retractMap_one

/-- The explicit homotopy equivalence between the punctured plane and the circle. -/
def hequiv : ContinuousMap.HomotopyEquiv Punctured Circle where
  toFun := toCircle
  invFun := fromCircle
  left_inv := ContinuousMap.Homotopic.symm ⟨retractHomotopy⟩
  right_inv := by rw [toCircle_comp_fromCircle]

/-- **Reusable brick.** The fundamental group of the punctured plane is abelian. -/
theorem punctured_pi1_comm (x : Punctured) (a b : FundamentalGroup Punctured x) :
    a * b = b * a := by
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homotopyEquiv hequiv x
  exact ψ.injective (by rw [map_mul, map_mul, Submission.Pi1Comm.circle_fundamentalGroup_comm])

end Submission.PuncturedPlane