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

/-!
# Toward an ambient-isotopy invariant separating the unknot and the trefoil

This file is scaffolding for the documented route in `PLAN.md`.  The very first foundational
brick that any complement-π₁ argument needs is the computation `π₁(S¹) ≅ ℤ`, which is **not**
present in this Mathlib.  We isolate that cornerstone here so it can be attempted and reused.

The eventual goal is `Submission.Helpers.no_ambient_homeo_unknot_trefoil`; see `PLAN.md` for the
full chain (restriction homeomorphism of complements, `π₁(ℝ³∖unknot) ≅ ℤ`, a surjection
`π₁(ℝ³∖trefoil) ↠ S₃`, and the gluing via π₁ functoriality).
-/

namespace Submission.Invariant

open scoped Topology

/-
Restriction of an ambient homeomorphism to complements: if `e` carries `A` onto `B`, it
restricts to a homeomorphism of the complements.  (Foundational, reusable infrastructure for the
π₁-of-complement route; see `PLAN.md`.)
-/
theorem compl_homeo_of_image_eq {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ X) (A B : Set X) (h : e '' A = B) :
    Nonempty ((↥(Aᶜ)) ≃ₜ (↥(Bᶜ))) := by
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ fun x => ⟨ e x, _ ⟩, fun x => ⟨ e.symm x, _ ⟩, _, _ ⟩;
  all_goals simp_all +decide [ Set.ext_iff, Function.LeftInverse, Function.RightInverse ];
  exact fun hx => x.2 ( by simpa using h _ |>.2 hx );
  exact fun hx => x.2 <| h _ |>.1 ⟨ _, hx, by simp +decide ⟩;
  · exact Continuous.subtype_mk ( e.continuous.comp continuous_subtype_val ) _;
  · exact Continuous.subtype_mk ( e.symm.continuous.comp continuous_subtype_val ) _

/-
**π₁ functoriality under homeomorphism.** A homeomorphism `e : X ≃ₜ Y` induces an isomorphism
of fundamental groups at corresponding basepoints.  This is the gateway lemma that turns the
complement homeomorphism `compl_homeo_of_image_eq` into a fundamental-group obstruction:
homeomorphic complements have isomorphic π₁, so any π₁ invariant separating the two complements
separates the knots.  (Reusable infrastructure for the route in `PLAN.md`.)
-/
theorem fundamentalGroup_mulEquiv_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y (e x)) := by
      refine' ⟨ _ ⟩;
      refine' { Equiv.ofBijective _ ⟨ _, _ ⟩ with .. };
      refine' fun γ => γ.map ( ContinuousMap.mk ( fun x => e x ) e.continuous ) _;
      all_goals simp +decide [ Function.Injective, Function.Surjective, FundamentalGroup.map ];
      · intro a₁ a₂ h;
        obtain ⟨ p₁, hp₁ ⟩ := a₁;
        obtain ⟨ p₂, hp₂ ⟩ := a₂;
        obtain ⟨ H, hH ⟩ := Quotient.exact h;
        refine' Quotient.sound ⟨ _, _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        exact ContinuousMap.mk ( fun p => e.symm ( H.toFun p ) ) ( e.symm.continuous.comp H.continuous );
        all_goals simp_all +decide [ ContinuousMap.mk ];
      · intro b;
        obtain ⟨ γ, hγ ⟩ := b;
        refine' ⟨ _, _ ⟩;
        refine' Quotient.mk'' _;
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ fun t => e.symm ( γ t ), e.symm.continuous.comp γ.continuous ⟩;
        all_goals simp_all +decide [ FundamentalGroupoid.map ];
        erw [ CategoryTheory.Functor.mapEnd_apply ];
        erw [ Quotient.eq'' ];
        refine' ⟨ _, _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ fun p => e ( e.symm ( γ p.2 ) ), by continuity ⟩;
        all_goals simp +decide [ hγ, ‹γ.toFun 1 = _› ]

/-
**π₁ functoriality under homotopy equivalence.** A homotopy equivalence `e : X ≃ₕ Y` induces an
isomorphism of fundamental groups at corresponding basepoints.  This strengthens
`fundamentalGroup_mulEquiv_of_homeo` (a homeomorphism is a homotopy equivalence) and is the
gateway lemma for the deformation-retract route: it lets one replace a knot complement by any
homotopy-equivalent model before computing π₁.  Built on Mathlib's
`FundamentalGroupoidFunctor.equivOfHomotopyEquiv`.
-/
theorem fundamentalGroup_mulEquiv_of_homotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y (e.toFun x)) := by
  refine' ⟨ _ ⟩;
  refine' { Equiv.ofBijective _ ⟨ _, _ ⟩ with .. };
  refine' fun γ => ( FundamentalGroupoidFunctor.equivOfHomotopyEquiv e ).functor.map γ;
  exact ( FundamentalGroupoidFunctor.equivOfHomotopyEquiv e ).functor.map_injective;
  exact CategoryTheory.Functor.map_surjective _;
  intro a b;
  exact ( FundamentalGroupoidFunctor.equivOfHomotopyEquiv e ).functor.map_comp b a

/-
**Abelianness via an injective induced π₁-homomorphism.** If a continuous map `f : X → Y`
induces an *injective* homomorphism on fundamental groups at a basepoint `x`, and `π₁(Y, f x)`
is abelian, then `π₁(X, x)` is abelian. This is the reduction used for the unknot side: to show
`π₁(ℝ³ ∖ unknot)` abelian it suffices to build a continuous "linking-phase" map into a space
with abelian π₁ (e.g. `Circle`, by `Submission.Pi1Comm.circle_fundamentalGroup_comm`) whose
induced map on `FundamentalGroup` is injective. Sound, reusable; see `PLAN.md`.
-/
theorem pi1_comm_of_injective_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hcomm : ∀ a b : FundamentalGroup Y (f x), a * b = b * a)
    (hinj : Function.Injective (FundamentalGroup.map f x)) :
    ∀ a b : FundamentalGroup X x, a * b = b * a := by
  intro a b
  apply hinj
  rw [map_mul, map_mul, hcomm]

end Submission.Invariant