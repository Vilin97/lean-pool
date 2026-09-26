/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Coordinate
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Intrinsic integer points and the polytope centerpoint statement

This file records the convex-geometric definitions from the introduction and
the corrected formal statement of Theorem 1.12.  The paper writes
`P ⊆ ℚ^d` while simultaneously taking real convex combinations.  We use the
real realization and explicitly require the finite support of the weight to
be rational.  Without that requirement a finite set such as
`{0, 1, sqrt 2}` need not lie in any discrete affine lattice, so the phrase
"the lattice spanned by the support" would be undefined.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

/-- The affine integer span of a set: finite integer affine combinations. -/
def affineIntSpan {n : ℕ} (S : Set (RealCoord n)) : Set (RealCoord n) :=
  {q | ∃ (k : ℕ) (points : Fin k → RealCoord n) (coeff : Fin k → ℤ),
    (∀ i, points i ∈ S) ∧ (∑ i, coeff i) = 1 ∧
      q = ∑ i, (coeff i : ℝ) • points i}

namespace RationalPolytope

/-- `F` is the minimal face of `P` containing `q`, expressed by the
standard equivalent characterization that `q` lies in the relative interior
of `F`.  The order-theoretic characterization (every containing face also
contains `F`) belongs in the finite-face API. -/
def IsMinimalFaceAt {n : ℕ} (P : RationalPolytope n) (q : RealCoord n)
    (F : P.Face) : Prop :=
  q ∈ F.relInterior

/-- Definition 1.7 (`intpt`): integrality is measured in the affine integer
span of the vertices of the minimal face, not in an ambient fixed lattice. -/
def IsIntrinsicInteger {n : ℕ} (P : RationalPolytope n) (q : RealCoord n) : Prop :=
  ∃ F : P.Face, P.IsMinimalFaceAt q F ∧
    q ∈ affineIntSpan (P.vertexSet ∩ F.carrier)

/-- A hollow polytope has no intrinsic integer points other than vertices. -/
def IsHollow {n : ℕ} (P : RationalPolytope n) : Prop :=
  ∀ q ∈ P.carrier, P.IsIntrinsicInteger q → q ∈ P.vertexSet

end RationalPolytope

/-- There is a hollow rational `d`-polytope with exactly `n` vertices. -/
def AdmitsHollowPolytopeVertexCount (d n : ℕ) : Prop :=
  ∃ P : RationalPolytope d, P.IsHollow ∧ P.vertexSet.ncard = n

/-- The paper's convex-geometric constant `L(d)`, defined as a supremum.
Finiteness/attainment will be supplied by the hollow-polytope theory. -/
noncomputable def hollowPolytopeNumber (d : ℕ) : ℕ :=
  sSup {n : ℕ | AdmitsHollowPolytopeVertexCount d n}

/-- Total mass of a finitely supported nonnegative weight. -/
noncomputable def totalWeight {n : ℕ} (w : RealCoord n → NNReal) : NNReal :=
  ∑ᶠ q, w q

/-- Weight on the closed affine halfspace through `q` selected by `xi`. -/
noncomputable def upperHalfspaceWeight {n : ℕ} (w : RealCoord n → NNReal)
    (q : RealCoord n) (xi : RealCoord n →ᵃ[ℝ] ℝ) : NNReal :=
  ∑ᶠ x, if xi q ≤ xi x then w x else 0

/-- A point is `theta`-central if every closed halfspace containing it has at
least a `theta` fraction of the total weight.  It suffices to test supporting
halfspaces whose boundary passes through the point. -/
def IsCentral {n : ℕ} (w : RealCoord n → NNReal) (theta : NNReal)
    (q : RealCoord n) : Prop :=
  ∀ xi : RealCoord n →ᵃ[ℝ] ℝ,
    theta * totalWeight w ≤ upperHalfspaceWeight w q xi

/-- The exact conclusion of Theorem 1.12. -/
def PolytopeCenterpointConclusion {d : ℕ} (P : RationalPolytope d)
    (w : RealCoord d → NNReal) : Prop :=
  ∃ (F : P.Face) (q : RealCoord d),
    q ∈ F.relInterior ∧
      IsCentral w (hollowPolytopeNumber d : NNReal)⁻¹ q ∧
      q ∈ affineIntSpan ({x | w x ≠ 0} ∩ F.carrier)

end EGZ
