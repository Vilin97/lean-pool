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

/-!
# Cornerstone: the fundamental group of a topological group is abelian

This is the Eckmann–Hilton cornerstone: π₁(G, x) is abelian whenever `G` is a topological group.
The based loop space at the identity carries two compatible unital operations — concatenation
(`trans`, which induces the group law on `FundamentalGroup`) and the pointwise group product
(`mulp`) — and these satisfy the *strict* interchange law coming from
`Path.Homotopic.comp_prod_eq_prod_comp`.  Eckmann–Hilton then forces concatenation to be
commutative.

This mirrors how Mathlib proves `HomotopyGroup.commGroup` (πₙ abelian for n ≥ 2).
-/

open scoped Topology
open CategoryTheory

noncomputable section

namespace Submission.Pi1Comm

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Multiplication of `G` as a continuous map. -/
def mulCM : C(G × G, G) := ⟨fun p => p.1 * p.2, continuous_mul⟩

@[simp] lemma mulCM_apply (p : G × G) : mulCM p = p.1 * p.2 := rfl

@[simp] lemma mulCM_one : (mulCM : C(G × G, G)) (1, 1) = 1 := by simp [mulCM]

/-- The pointwise product of two based-loop classes at the identity of `G`. -/
def mulp (a b : FundamentalGroup G 1) : FundamentalGroup G 1 :=
  FundamentalGroup.fromPath
    (((Path.Homotopic.prod (FundamentalGroup.toPath a) (FundamentalGroup.toPath b)).map
        mulCM).cast mulCM_one.symm mulCM_one.symm)

/-
Left unit law for the pointwise product.
-/
lemma one_mulp (a : FundamentalGroup G 1) : mulp 1 a = a := by
  obtain ⟨ p, hp ⟩ := a;
  refine' Quotient.sound _;
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ fun ( t, x ) => p x, by continuity ⟩;
  all_goals (intros; first | rfl | exact (one_mul (_ : G)).symm)

/-
Right unit law for the pointwise product.
-/
lemma mulp_one (a : FundamentalGroup G 1) : mulp a 1 = a := by
  obtain ⟨ p, hp ⟩ := a;
  refine' Quotient.sound _;
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ fun x => p x.2, by continuity ⟩;
  all_goals (intros; first | rfl | exact (mul_one (_ : G)).symm)

/-- The pointwise product is unital, with unit the constant-loop class `1`. -/
lemma isUnital_mulp : EckmannHilton.IsUnital (mulp (G := G)) 1 :=
  EckmannHilton.IsUnital.mk { left_id := one_mulp, right_id := mulp_one }

/-
The strict interchange law between the pointwise product and concatenation
(the group law on `FundamentalGroup G 1`).
-/
lemma mulp_distrib (a b c d : FundamentalGroup G 1) :
    mulp (a * b) (c * d) = (mulp a c) * (mulp b d) := by
      rcases a with ⟨ a ⟩;
      rcases b with ⟨ b ⟩ ; rcases c with ⟨ c ⟩ ; rcases d with ⟨ d ⟩ ;
      erw [ Quotient.eq'' ];
      refine' ⟨ _, _ ⟩;
      refine' ⟨ _, _, _ ⟩;
      refine' ⟨ fun p => ( b.trans a ).extend p.2 * ( d.trans c ).extend p.2, _ ⟩;
      fun_prop;
      all_goals
        first
        | (intro x; simp only [Path.coe_toContinuousMap, Path.cast_coe, Path.extend_extends']; rfl)
        | (intro x; simp only [Path.coe_toContinuousMap, Path.cast_coe, Path.extend_extends',
             Path.trans_apply]; split_ifs <;> rfl)
        | (intro t x hx;
           simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx;
           rcases hx with rfl | rfl <;>
           simp only [ContinuousMap.coe_mk, Path.coe_toContinuousMap, Path.cast_coe,
             Path.extend_extends'] <;> rfl)

/-- **Cornerstone.** The fundamental group of a topological group at the identity is abelian. -/
theorem fundamentalGroup_one_comm (a b : FundamentalGroup G 1) : a * b = b * a := by
  have hcomm : Std.Commutative (α := FundamentalGroup G 1) (· * ·) :=
    EckmannHilton.mul_comm isUnital_mulp EckmannHilton.MulOneClass.isUnital mulp_distrib
  exact hcomm.comm a b

/-- **Cornerstone (general basepoint).** The fundamental group of a topological group is abelian. -/
theorem fundamentalGroup_comm (x : G) (a b : FundamentalGroup G x) : a * b = b * a := by
  -- transport to the identity via left translation by `x⁻¹`, a homeomorphism `G ≃ₜ G`.
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo (Homeomorph.mulLeft x⁻¹) x
  have hx : (Homeomorph.mulLeft x⁻¹) x = 1 := by simp
  rw [hx] at ψ
  exact ψ.injective (by rw [map_mul, map_mul, fundamentalGroup_one_comm])

/-- **Concrete instance.** The fundamental group of the circle `Circle` is abelian. -/
theorem circle_fundamentalGroup_comm (x : Circle) (a b : FundamentalGroup Circle x) :
    a * b = b * a :=
  fundamentalGroup_comm x a b

end Submission.Pi1Comm