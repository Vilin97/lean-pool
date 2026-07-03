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

import LeanPool.NonisotopicKnots.Submission.GenPos
import LeanPool.NonisotopicKnots.Submission.Invariant

/-!
# Point removal via general position (codimension-3)

Using the general-position square-pushoff `Submission.GenPos.square_pushoff_rel_boundary`, we
prove that removing a single point `q` from an open set `Ω ⊆ ℝ³` does not change the
commutativity of `π₁`: if `π₁(Ω)` is abelian at every basepoint then so is `π₁(Ω ∖ {q})`.

This is the general-position alternative to the abstract 2-D van Kampen amalgamation keystone
(`Submission.VanKampenInj.loop_null_in_U_of_null_in_X`): a contracting disk of a loop avoiding
`q` can be pushed off the codimension-3 point `q` rel its boundary.
-/

open scoped Topology unitInterval
open Submission.GenPos

noncomputable section

namespace Submission.PointRemovalGP

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-
**Homotopy-level point removal.**  A loop `γ` in `↥Ω` that avoids `q` and is null-homotopic
in `↥Ω` is null-homotopic through a homotopy that also avoids `q`.
-/
theorem loop_null_off_point {Ω : Set R3} (hΩ : IsOpen Ω) {q : R3}
    {x₀ : ↥Ω} (hx₀q : (x₀ : R3) ≠ q)
    (γ : Path x₀ x₀) (hγq : ∀ t, (γ t : R3) ≠ q)
    (hnull : Path.Homotopic γ (Path.refl x₀)) :
    ∃ H : Path.Homotopy γ (Path.refl x₀), ∀ p, (H p : R3) ≠ q := by
  revert hγq hx₀q;
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Path.Homotopy γ (Path.refl x₀), True := by
    exact ⟨ hnull.some, trivial ⟩;
  intro hx₀q hγq
  obtain ⟨G, hG⟩ : ∃ G : C(↑unitInterval × ↑unitInterval, R3), (∀ p, G p ∈ Ω) ∧ (∀ p, G p ≠ q) ∧ (∀ p : ↑unitInterval × ↑unitInterval, (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) → G p = (H₀ p : R3)) := by
    convert square_pushoff_rel_boundary hΩ ( ⟨ fun p => ( H₀ p : R3 ), ?_ ⟩ : C(↑unitInterval × ↑unitInterval, R3) ) ?_ ?_;
    fun_prop;
    · exact fun p => H₀ p |>.2;
    · rintro ⟨ t, s ⟩ ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Path.Homotopy ];
      exact hγq s s.2.1 s.2.2;
  refine' ⟨ _, _ ⟩;
  refine' { toContinuousMap := ⟨ fun p => ⟨ G p, hG.1 p ⟩, _ ⟩, map_zero_left := _, map_one_left := _, prop' := _ };
  all_goals norm_num [ hG ];
  exact Continuous.subtype_mk ( G.continuous ) _;
  exact fun a ha₁ ha₂ b hb₁ hb₂ => hG.2.1 _

/-- The inclusion `↥(Ω ∖ {q}) ↪ ↥Ω`. -/
def incl {Ω : Set R3} {q : R3} : C(↥(Ω \ {q}), ↥Ω) :=
  ⟨fun y => ⟨y.1, y.2.1⟩, by fun_prop⟩

/-
**Point removal preserves `π₁`-commutativity.**  If `π₁(↥Ω)` is abelian at every basepoint,
then `π₁(↥(Ω ∖ {q}))` is abelian at every basepoint.
-/
theorem point_removal_comm {Ω : Set R3} (hΩ : IsOpen Ω) {q : R3}
    (hΩcomm : ∀ (z : ↥Ω) (a b : FundamentalGroup (↥Ω) z), a * b = b * a)
    (z : ↥(Ω \ {q})) (a b : FundamentalGroup (↥(Ω \ {q})) z) : a * b = b * a := by
  apply Submission.Invariant.pi1_comm_of_injective_map (Submission.PointRemovalGP.incl) z (fun u v => hΩcomm (Submission.PointRemovalGP.incl z) u v) (by
  rw [ injective_iff_map_eq_one ];
  rintro ⟨ p ⟩ hp; simp_all +decide [ FundamentalGroup.map ] ;
  obtain ⟨ H, hH ⟩ := loop_null_off_point hΩ ( show ( z : R3 ) ≠ q from z.2.2 ) ( p.map incl.continuous ) ( fun t => by
                                                exact p t |>.2.2 ) ( by
                                                convert hp using 1;
                                                erw [ Quotient.eq' ] ; aesop; );
  refine' Quotient.sound ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ fun p => ⟨ H p, ⟨ _, _ ⟩ ⟩, _ ⟩;
  all_goals norm_num [ H.map_zero_left, H.map_one_left ];
  exact hH p;
  · fun_prop;
  · aesop;
  · aesop;
  · aesop) a b

end Submission.PointRemovalGP