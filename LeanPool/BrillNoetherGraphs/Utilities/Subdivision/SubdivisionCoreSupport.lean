/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexReachability
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import Mathlib.Tactic

/-!
# Core-supported rank-one divisors on subdivisions

The embedded core vertices of a positive subdivision are a strong separator.
Thus a particularly small uniform rank-one witness is available whenever one
can put a positive number of chips at every core vertex.  This module records
that observation without referring to a genus, a trivalence hypothesis, or a
certificate search.

The first theorem is deliberately graph-theoretic: an effective divisor with
at least one chip at every member of a certified strong separator has rank at
least one.  The subdivision theorems specialize it to the transparent divisor
which is zero on every edge-interior vertex.
-/

namespace Utilities.Subdivision.SubdivisionCoreSupport
open Utilities.Certificate

open Utilities

open Finset

variable {G : CFGraph}

/-- A positive effective representative already reaches each vertex at which
it carries a chip.  Consequently positivity on a strong separator proves
rank at least one. -/
theorem rank_ge_one_of_effective_positive_on_strongSeparator
    (hConnected : graphConnected G) {S : Finset G.V}
    (hSNonempty : S.Nonempty)
    (hSeparator : StrongSeparator.StrongSeparatorCertificate G S)
    {D : CFDiv G} (hEffective : effective D)
    (hPositive : ∀ s ∈ S, 1 ≤ D s) :
    rank G D ≥ 1 := by
  apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
    hConnected hSNonempty hSeparator
  intro s hs
  exact StrongSeparator.reaches_of_effective_representative
    (linearEquiv.refl G D) hEffective (hPositive s hs)

variable {n p : ℕ}

/-- The divisor which places `weight vertex` chips at each embedded core
vertex and no chips at subdivision-interior vertices. -/
def coreDivisor (spec : SubdivisionGraph.Spec n p) (weight : Fin n → ℤ) :
    CFDiv spec.graph
  | Sum.inl vertex => weight vertex
  | Sum.inr _interior => 0

@[simp] theorem coreDivisor_coreVertex
    (spec : SubdivisionGraph.Spec n p) (weight : Fin n → ℤ) (vertex : Fin n) :
    coreDivisor spec weight (spec.coreVertex vertex) = weight vertex := rfl

@[simp] theorem coreDivisor_interiorVertex
    (spec : SubdivisionGraph.Spec n p) (weight : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    coreDivisor spec weight (spec.interiorVertex edge offset) = 0 := rfl

/-- Nonnegative core weights make the core-supported divisor effective. -/
theorem coreDivisor_effective (spec : SubdivisionGraph.Spec n p)
    (weight : Fin n → ℤ) (hNonnegative : ∀ vertex, 0 ≤ weight vertex) :
    effective (coreDivisor spec weight) := by
  intro vertex
  rcases vertex with vertex | interior
  · exact hNonnegative vertex
  · rfl

/-- The degree of the core-supported divisor is exactly the sum of its core
weights; subdivision-interior vertices contribute zero. -/
@[simp] theorem deg_coreDivisor (spec : SubdivisionGraph.Spec n p)
    (weight : Fin n → ℤ) :
    deg (coreDivisor spec weight) = ∑ vertex : Fin n, weight vertex := by
  simp [deg, coreDivisor, Fintype.sum_sum_type]

/-- Positive core weights on a connected positive subdivision give a
rank-one divisor, uniformly over all edge lengths. -/
theorem rank_ge_one_coreDivisor (spec : SubdivisionGraph.Spec n p)
    (weight : Fin n → ℤ) (hConnected : graphConnected spec.graph)
    (hPositive : ∀ vertex, 1 ≤ weight vertex) :
    rank spec.graph (coreDivisor spec weight) ≥ 1 := by
  apply rank_ge_one_of_effective_positive_on_strongSeparator hConnected
    (ExplicitPotential.Certificate.coreVertices_nonempty spec)
    spec.coreVertices_strongSeparatorCertificate
    (coreDivisor_effective spec weight (fun vertex => by
      have := hPositive vertex
      omega))
  intro vertex hVertex
  obtain ⟨anchor, _hAnchor, rfl⟩ := Finset.mem_image.mp hVertex
  exact hPositive anchor

/-- Advertise the core-supported rank-one witness at its exact total degree.
This is useful for uniform families: only connectedness and positivity of the
core weights remain as hypotheses. -/
theorem bnExists_coreDivisor (spec : SubdivisionGraph.Spec n p)
    (weight : Fin n → ℤ) (degree : ℤ)
    (hDegree : (∑ vertex : Fin n, weight vertex) = degree)
    (hConnected : graphConnected spec.graph)
    (hPositive : ∀ vertex, 1 ≤ weight vertex) :
    BNExists spec.graph 1 degree := by
  refine ⟨coreDivisor spec weight, ?_,
    rank_ge_one_coreDivisor spec weight hConnected hPositive⟩
  rw [deg_coreDivisor]
  exact hDegree

/-- Put one chip at every core vertex and place all remaining degree at the
first core vertex.  The core is nonempty by definition of a subdivision
specification. -/
def degreeWeight (spec : SubdivisionGraph.Spec n p) (degree : ℤ) : Fin n → ℤ :=
  fun vertex =>
    1 + if vertex = ⟨0, spec.core_nonempty⟩ then degree - (n : ℤ) else 0

@[simp] theorem sum_degreeWeight (spec : SubdivisionGraph.Spec n p)
    (degree : ℤ) :
    ∑ vertex : Fin n, degreeWeight spec degree vertex = degree := by
  classical
  simp [degreeWeight, Finset.sum_add_distrib]

theorem degreeWeight_positive (spec : SubdivisionGraph.Spec n p)
    (degree : ℤ) (hDegree : (n : ℤ) ≤ degree) (vertex : Fin n) :
    1 ≤ degreeWeight spec degree vertex := by
  classical
  unfold degreeWeight
  split <;> omega

/-- **Core-cardinality criterion.**  A connected subdivision with at most
`degree` embedded core vertices has a rank-one divisor of that degree.  This
is the certificate-free form of the all-supported sparse-potential pattern. -/
theorem bnExists_of_coreVertexCount_le_degree
    (spec : SubdivisionGraph.Spec n p) (degree : ℤ)
    (hConnected : graphConnected spec.graph)
    (hDegree : (n : ℤ) ≤ degree) :
    BNExists spec.graph 1 degree := by
  exact bnExists_coreDivisor spec (degreeWeight spec degree) degree
    (sum_degreeWeight spec degree) hConnected
    (degreeWeight_positive spec degree hDegree)

/-- Finite-core-facing form of the core-cardinality criterion. -/
theorem bnExists_of_coreVertexCount_le_degree_of_coreConnected
    (spec : SubdivisionGraph.Spec n p) (degree : ℤ)
    (hCoreConnected : spec.core.Connected)
    (hDegree : (n : ℤ) ≤ degree) :
    BNExists spec.graph 1 degree :=
  bnExists_of_coreVertexCount_le_degree spec degree
    (spec.graph_connected_of_coreConnected hCoreConnected) hDegree

end Utilities.Subdivision.SubdivisionCoreSupport
