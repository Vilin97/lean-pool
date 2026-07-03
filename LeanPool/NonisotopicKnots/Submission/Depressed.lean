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

import LeanPool.NonisotopicKnots.Submission.Vieta
import LeanPool.NonisotopicKnots.Submission.CuspGeom

/-!
# Depressed↔full reconciliation brick (WORK IN PROGRESS)

PLAN step (a): the cusp discriminant complement `DC ⊂ ℂ²` (depressed monic cubics `X³+pX+q`
with `4p³+27q² ≠ 0`) embeds into the full discriminant complement `Submission.Vieta.DiscCompl`
as the `e₁ = 0` slice, and this embedding is a homotopy equivalence (centroid/depression
retraction). The key gating fact is that a depressed cubic with nonzero discriminant has three
distinct complex roots.

Staged: not imported by `Submission.lean` until `sorry`-free.
-/

namespace Submission.Depressed

open Polynomial Complex

/-- The depressed monic cubic `X³ + p·X + q` over `ℂ`. -/
noncomputable def cubic (p q : ℂ) : ℂ[X] := X ^ 3 + C p * X + C q

lemma cubic_monic (p q : ℂ) : (cubic p q).Monic := by
  unfold cubic;
  rw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases hp : p = 0 <;> simp +decide [ hp, Polynomial.natDegree_add_eq_left_of_natDegree_lt ]

lemma cubic_natDegree (p q : ℂ) : (cubic p q).natDegree = 3 := by
  unfold cubic;
  rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases h : p = 0 <;> simp +decide [ h ]

/-
The derivative of the depressed cubic is `3X² + p`.
-/
lemma derivative_cubic (p q : ℂ) : derivative (cubic p q) = C 3 * X ^ 2 + C p := by
  unfold cubic;
  norm_num [ Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X_pow ]

/-- The depressed cubic packaged as a Mathlib `Cubic` with `a = 1, b = 0, c = p, d = q`. -/
def Pcubic (p q : ℂ) : Cubic ℂ := ⟨1, 0, p, q⟩

lemma Pcubic_discr (p q : ℂ) : (Pcubic p q).discr = -4 * p ^ 3 - 27 * q ^ 2 := by
  unfold Pcubic; ring;
  unfold Cubic.discr; ring;

lemma Pcubic_splits (p q : ℂ) :
    (Polynomial.map (RingHom.id ℂ) (Pcubic p q).toPoly).Splits := by
  convert IsAlgClosed.splits ( Polynomial.map ( RingHom.id ℂ ) ( Pcubic p q |> Cubic.toPoly ) ) using 1

/-
**Three distinct roots.** If `4p³ + 27q² ≠ 0`, there is an injective triple of roots of the
depressed cubic, i.e. its Vieta coefficients `(0, p, -q)` lie in `Submission.Vieta.DiscCompl`.
-/
theorem exists_injective_roots {p q : ℂ} (h : 4 * p ^ 3 + 27 * q ^ 2 ≠ 0) :
    ((0 : ℂ), p, -q) ∈ Submission.Vieta.DiscCompl := by
  obtain ⟨x, y, z, h_roots⟩ : ∃ x y z : ℂ, (Cubic.map (RingHom.id ℂ) (Pcubic p q)).roots = {x, y, z} ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    obtain ⟨x, y, z, h_roots⟩ : ∃ x y z : ℂ, (Cubic.map (RingHom.id ℂ) (Pcubic p q)).roots = {x, y, z} := by
      have h_splits : (Polynomial.map (RingHom.id ℂ) (Pcubic p q).toPoly).Splits :=
        Pcubic_splits p q
      convert Cubic.splits_iff_roots_eq_three ( show ( Pcubic p q ).a ≠ 0 from by simp +decide [ Pcubic ] ) |>.1 h_splits using 1;
    have h_distinct : Multiset.Nodup (Cubic.roots (Cubic.map (RingHom.id ℂ) (Pcubic p q))) := by
      apply Cubic.discr_ne_zero_iff_roots_nodup (by
      exact one_ne_zero) (by
      convert Pcubic_splits p q using 1) |>.1;
      rw [ Pcubic_discr ] ; contrapose! h; linear_combination' -h;
    aesop;
  use ⟨![x, y, z], by
    simp +decide [ Function.Injective, Fin.forall_fin_succ, h_roots ];
    grind⟩
  generalize_proofs at *;
  have h_vieta : (Pcubic p q).b = (Pcubic p q).a * -(x + y + z) ∧ (Pcubic p q).c = (Pcubic p q).a * (x * y + x * z + y * z) ∧ (Pcubic p q).d = (Pcubic p q).a * -(x * y * z) := by
    have := Cubic.b_eq_three_roots ( show ( Pcubic p q ).a ≠ 0 from by simp +decide [ Pcubic ] ) ( show ( Cubic.map ( RingHom.id ℂ ) ( Pcubic p q ) ).roots = { x, y, z } from h_roots.1 ) ; ( have := Cubic.c_eq_three_roots ( show ( Pcubic p q ).a ≠ 0 from by simp +decide [ Pcubic ] ) ( show ( Cubic.map ( RingHom.id ℂ ) ( Pcubic p q ) ).roots = { x, y, z } from h_roots.1 ) ; ( have := Cubic.d_eq_three_roots ( show ( Pcubic p q ).a ≠ 0 from by simp +decide [ Pcubic ] ) ( show ( Cubic.map ( RingHom.id ℂ ) ( Pcubic p q ) ).roots = { x, y, z } from h_roots.1 ) ; aesop; ) );
  unfold Vieta.coeffConf Vieta.Coeff; simp_all +decide [ Pcubic ] ;
  grind

end Submission.Depressed