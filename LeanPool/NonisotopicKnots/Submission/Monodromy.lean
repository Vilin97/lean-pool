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


/-!
# Abstract non-commutation criterion via covering-space monodromy

This file provides a *sound, fully proved, reusable* bridge lemma for the documented
covering-space route toward `Submission.Helpers.trefoil_compl_pi1_noncomm` (see `PLAN.md`).

The remaining mathematical crux — that the fundamental group of the trefoil complement is
non-abelian — is naturally proved by exhibiting

* a covering map `p : E → Q` (e.g. `Submission.ConfigCover.conf_covering`, the regular
  `S₃`-covering of the configuration/discriminant space), and
* a continuous map `f` from the complement `Ω` to the base `Q`,

and then observing that the induced **monodromy** permutations of two loops do not commute.
This file isolates the purely formal step: *if the two monodromy permutations of `a` and `b`
do not commute, then `a` and `b` do not commute in `π₁(Ω)`.*

It uses only Mathlib's covering-map monodromy API
(`IsCoveringMap.monodromy`, `IsCoveringMap.monodromy_trans_apply`) and the definitional fact
that, on the fundamental group, `(a * b).toPath = b.toPath.trans a.toPath`.
-/

open scoped Topology

namespace Submission.Monodromy

/-
Distributivity of `Path.Homotopic.Quotient.map` over `trans`.
-/
theorem map_trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (γ.trans δ).map f = (γ.map f).trans (δ.map f) := by
      obtain ⟨p, rfl⟩ := Quotient.exists_rep γ
      obtain ⟨q, rfl⟩ := Quotient.exists_rep δ;
      simp +decide [Path.Homotopic.Quotient.trans, Path.Homotopic.Quotient.map];
      erw [ Quotient.map_mk ] ; aesop

/-
**Non-commutation criterion via monodromy.**
Let `p : E → Q` be a covering map, `f : Ω → Q` continuous, and `a b` two loops at a basepoint
`x` of `Ω`.  Write `Ma`, `Mb` for the monodromy permutations of the fiber over `f x` associated
to the images of `a`, `b`.  If `Ma ∘ Mb ≠ Mb ∘ Ma`, then `a * b ≠ b * a` in `π₁(Ω, x)`.
-/
theorem noncomm_of_monodromy {Ω E Q : Type*}
    [TopologicalSpace Ω] [TopologicalSpace E] [TopologicalSpace Q]
    {p : E → Q} (cov : IsCoveringMap p) (f : C(Ω, Q)) {x : Ω}
    (a b : FundamentalGroup Ω x)
    (hne : cov.monodromy (a.toPath.map f) ∘ cov.monodromy (b.toPath.map f)
         ≠ cov.monodromy (b.toPath.map f) ∘ cov.monodromy (a.toPath.map f)) :
    a * b ≠ b * a := by
      contrapose! hne; simp_all +decide [ funext_iff ] ;
      intro y hy; replace hne := congr_arg ( fun z => z.toPath.map f ) hne; simp_all +decide [ FundamentalGroup.toPath ] ;
      convert congr_arg ( fun z => cov.monodromy z ⟨ y, hy ⟩ ) hne using 1 <;> simp +decide [ FundamentalGroup.toArrow ];
      · rw [ ← IsCoveringMap.monodromy_trans_apply ];
        rw [ ← map_trans ];
        congr! 1;
      · rw [ ← IsCoveringMap.monodromy_trans_apply ];
        rw [ ← map_trans ];
        congr! 1

end Submission.Monodromy