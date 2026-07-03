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


namespace LeanEval
namespace KnotTheory

/-!
# Smooth knots, links, ambient isotopy, and chirality

Minimal definitions to support the three knot-theory benchmark problems
(`Linking`, `NonIsotopicKnots`, `Chiral`). Mathlib has essentially no knot
theory, so we set up just enough infrastructure to state the questions
faithfully in terms of smooth maps `S¹ → ℝ³` and ambient isotopies of `ℝ³`.

A *knot* is a smooth, 2π-periodic, injective immersion `ℝ → ℝ³`. A
*two-component link* is a pair of knots with disjoint images. An *ambient
isotopy* is a smooth one-parameter family of diffeomorphisms of `ℝ³`
starting at the identity, presented here as a forward map and an inverse
map jointly smooth in `(t, x)`.

The parametrization is part of the data, so each knot or link component
comes with an orientation induced from the standard orientation on `S¹`.
Accordingly, isotopy is understood in the oriented sense: an ambient isotopy
must carry the parametrized components of the source to those of the target,
up to orientation-preserving reparametrization of the source circle. A knot
is *chiral* here in this same orientation-sensitive sense: it is not isotopic
to its mirror image (under reflection through the `xy`-plane).

These definitions trade some Mathlib idiomaticity for being self-contained
and easy to read; in particular, we do not go through `Diffeomorph` or
`ContMDiff` on a manifold structure for `ℝ³`, since `ContDiff ℝ ⊤` over the
ambient normed space says exactly what we need.
-/

/-- The ambient space `ℝ³`, as a Euclidean inner-product space. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- An oriented smooth knot in `ℝ³`: a 2π-periodic, smooth, injective immersion.
The orientation is the one induced by the parametrization. -/
structure Knot where
  /-- The parametrizing map. -/
  curve : ℝ → R3
  /-- The map is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) curve
  /-- The map has period `2π`. -/
  periodic : ∀ t, curve (t + 2 * Real.pi) = curve t
  /-- The map is injective on a fundamental period. -/
  injOn : Set.InjOn curve (Set.Ico 0 (2 * Real.pi))
  /-- The map is an immersion (its derivative is everywhere nonzero). -/
  immersion : ∀ t, deriv curve t ≠ 0

/-- An oriented two-component smooth link in `ℝ³`: a pair of oriented knots
with disjoint images. -/
structure TwoLink where
  /-- The first component. -/
  K : Knot
  /-- The second component. -/
  L : Knot
  /-- The two components have disjoint images in `ℝ³`. -/
  disjoint : Disjoint (Set.range K.curve) (Set.range L.curve)

/-- A smooth ambient isotopy of `ℝ³`: a one-parameter family `H t : ℝ³ → ℝ³`
of diffeomorphisms, jointly smooth in `(t, x)`, starting at the identity.
The inverse family `Hinv` is also jointly smooth. -/
structure AmbientIsotopy where
  /-- The forward family. -/
  H : ℝ → R3 → R3
  /-- The inverse family. -/
  Hinv : ℝ → R3 → R3
  /-- The forward family is jointly smooth in `(t, x)`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H)
  /-- The inverse family is jointly smooth in `(t, x)`. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Hinv)
  /-- `Hinv t` is a left inverse of `H t`. -/
  inv_left : ∀ t x, Hinv t (H t x) = x
  /-- `Hinv t` is a right inverse of `H t`. -/
  inv_right : ∀ t x, H t (Hinv t x) = x
  /-- The isotopy starts at the identity. -/
  start : H 0 = id

structure CircleReparam where
  /-- A lift `ℝ → ℝ` of a circle self-map. -/
  f : ℝ → ℝ
  /-- A lifted inverse. -/
  finv : ℝ → ℝ
  /-- The lift is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  /-- The inverse lift is smooth. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) finv
  /-- `finv` is a left inverse to `f`. -/
  left_inv : ∀ t, finv (f t) = t
  /-- `finv` is a right inverse to `f`. -/
  right_inv : ∀ t, f (finv t) = t
  /-- The lift descends to a map of `S¹ = ℝ / 2πℤ`. -/
  periodic : ∀ t, f (t + 2 * Real.pi) = f t + 2 * Real.pi
  /-- The inverse lift also descends to `S¹`. -/
  periodic_inv : ∀ t, finv (t + 2 * Real.pi) = finv t + 2 * Real.pi
  /-- The induced circle map preserves orientation. -/
  mono : StrictMono f

/-- Two oriented knots are ambient-isotopic if some ambient isotopy of `ℝ³`
carries the parametrized knot `K₁` to the parametrized knot `K₂`, up to an
orientation-preserving smooth reparametrization of the source circle. -/
def Knot.Isotopic (K₁ K₂ : Knot) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam, ∀ t, Φ.H 1 (K₁.curve t) = K₂.curve (σ.f t)

/-- Two oriented two-component links are ambient-isotopic if a single ambient
isotopy carries each oriented component of the first link to the
corresponding oriented component of the second. -/
def TwoLink.Isotopic (L₁ L₂ : TwoLink) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ τ : CircleReparam,
    (∀ t, Φ.H 1 (L₁.K.curve t) = L₂.K.curve (σ.f t)) ∧
    (∀ t, Φ.H 1 (L₁.L.curve t) = L₂.L.curve (τ.f t))

/-- Reflection through the `xy`-plane in `ℝ³`: `(x, y, z) ↦ (x, y, -z)`. -/
def reflectZ (p : R3) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => if i = 2 then -p.ofLp i else p.ofLp i)

/-- A knot is *chiral* if it is not ambient-isotopic, in the
orientation-sensitive sense used in this benchmark, to its mirror image (the
reflection of the image through the `xy`-plane). -/
def Knot.Chiral (K : Knot) : Prop :=
  ¬ ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
    ∀ t, Φ.H 1 (K.curve t) = reflectZ (K.curve (σ.f t))

end KnotTheory
end LeanEval
