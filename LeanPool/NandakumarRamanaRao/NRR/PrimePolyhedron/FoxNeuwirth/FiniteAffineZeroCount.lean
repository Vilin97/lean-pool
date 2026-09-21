/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexChain
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceZero
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FiniteCells

/-!
# Finite affine zero counts on Fox--Neuwirth incidence cycles

This module implements the algebraic finite-zero-count layer.  The correct
modulo-prime invariant counts symmetry orbits of transverse zeros, rather than all zeros in the
covering order complex.  Accordingly the main object is a finite incidence cycle: a finite set of
top cells, a finite set of facets, an incidence matrix, and a coefficient vector whose boundary
vanishes.

The zero count is the pairing of the cycle coefficients with a local-index function.  An admissible
affine homotopy supplies a facet transgression whose incidence coboundary is the difference of the
endpoint local indices.  Finite Stokes algebra then proves invariance of the zero count.  No general
PL topology is used in this layer.

For the order complex itself, the file defines the explicit alternating incidence matrix and shows
that an ordinary simplicial cycle produces a finite incidence cycle.  The later orbit reduction can
instantiate the same interface with orbit representatives and quotient incidences.
-/

namespace NRR

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- A finite chain-level incidence cycle.  This is the exact algebraic structure required by the
zero-count argument, and it applies equally to an ordinary finite simplicial cycle or to its finite
symmetry-orbit quotient. -/
structure FiniteIncidenceCycle (R : Type*) [CommRing R] where
  TopCell : Type*
  Facet : Type*
  [topCellFintype : Fintype TopCell]
  [topCellDecidableEq : DecidableEq TopCell]
  [facetFintype : Fintype Facet]
  [facetDecidableEq : DecidableEq Facet]
  incidence : Facet → TopCell → R
  coefficient : TopCell → R
  boundary_zero : ∀ f : Facet, ∑ c : TopCell, incidence f c * coefficient c = 0

attribute [instance] FiniteIncidenceCycle.topCellFintype
attribute [instance] FiniteIncidenceCycle.topCellDecidableEq
attribute [instance] FiniteIncidenceCycle.facetFintype
attribute [instance] FiniteIncidenceCycle.facetDecidableEq

namespace FiniteIncidenceCycle

variable (C : FiniteIncidenceCycle R)

/-- Incidence coboundary of a facet function. -/
def coboundary (h : C.Facet → R) : C.TopCell → R :=
  fun c => ∑ f : C.Facet, C.incidence f c * h f

/-- Pairing of the cycle coefficient vector with a local-index function. -/
def zeroCount (index : C.TopCell → R) : R :=
  ∑ c : C.TopCell, C.coefficient c * index c

@[simp] theorem zeroCount_zero : C.zeroCount 0 = 0 := by
  simp [zeroCount]

@[simp] theorem zeroCount_add (a b : C.TopCell → R) :
    C.zeroCount (a + b) = C.zeroCount a + C.zeroCount b := by
  simp [zeroCount, mul_add, Finset.sum_add_distrib]

@[simp] theorem zeroCount_sub (a b : C.TopCell → R) :
    C.zeroCount (a - b) = C.zeroCount a - C.zeroCount b := by
  simp [zeroCount, mul_sub, Finset.sum_sub_distrib]

/-- Finite Stokes theorem: the pairing of a cycle with an incidence coboundary vanishes. -/
theorem zeroCount_coboundary_eq_zero (h : C.Facet → R) :
    C.zeroCount (C.coboundary h) = 0 := by
  classical
  unfold zeroCount coboundary
  calc
    (∑ c : C.TopCell,
        C.coefficient c * ∑ f : C.Facet, C.incidence f c * h f) =
        ∑ c : C.TopCell, ∑ f : C.Facet,
          C.coefficient c * (C.incidence f c * h f) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.mul_sum]
    _ = ∑ f : C.Facet, ∑ c : C.TopCell,
          C.incidence f c * C.coefficient c * h f := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro f hf
            apply Finset.sum_congr rfl
            intro c hc
            ring
    _ = ∑ f : C.Facet,
          (∑ c : C.TopCell, C.incidence f c * C.coefficient c) * h f := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.sum_mul]
    _ = 0 := by
      simp [C.boundary_zero]

/-- A chain-level admissible homotopy.  The transgression is the finite signed zero set in the
prism facets, and `index_difference` is the local finite Stokes relation. -/
structure IndexHomotopy (index₀ index₁ : C.TopCell → R) where
  transgression : C.Facet → R
  index_difference : index₁ - index₀ = C.coboundary transgression

namespace IndexHomotopy

variable {C : FiniteIncidenceCycle R}
variable {index₀ index₁ : C.TopCell → R}

/-- Zero-count invariance under an admissible finite homotopy. -/
theorem zeroCount_eq (H : C.IndexHomotopy index₀ index₁) :
    C.zeroCount index₀ = C.zeroCount index₁ := by
  apply sub_eq_zero.mp
  calc
    C.zeroCount index₀ - C.zeroCount index₁ =
        -C.zeroCount (index₁ - index₀) := by
          rw [C.zeroCount_sub]
          ring
    _ = -C.zeroCount (C.coboundary H.transgression) := by
          rw [H.index_difference]
    _ = 0 := by
          rw [C.zeroCount_coboundary_eq_zero]
          simp

/-- Nonvanishing transports across an admissible finite homotopy. -/
theorem zeroCount_ne_zero
    (H : C.IndexHomotopy index₀ index₁)
    (h₀ : C.zeroCount index₀ ≠ 0) :
    C.zeroCount index₁ ≠ 0 := by
  rw [← H.zeroCount_eq]
  exact h₀

end IndexHomotopy

end FiniteIncidenceCycle

namespace FoxNeuwirthOrderComplex

variable {p d : Nat}

namespace SimplicialIncidence

/-- Alternating incidence coefficient between a simplex and one of its codimension-one faces. -/
noncomputable def incidence
    (target : Simplex p d) (source : Simplex p (d + 1)) : R :=
  ∑ k : Fin (d + 2),
    if source.restrict (FaceMap.delete k) = target then
      SimplicialChain.faceSign k
    else 0

/-- The ordinary simplicial boundary coefficient is matrix multiplication by the alternating
incidence matrix. -/
theorem boundary_apply_eq_incidence
    (chain : SimplicialChain R p (d + 1))
    (target : Simplex p d) :
    SimplicialChain.boundary chain target =
      ∑ source : Simplex p (d + 1), incidence target source * chain source := by
  classical
  simp only [SimplicialChain.boundary_apply, incidence]
  apply Finset.sum_congr rfl
  intro source hsource
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hface : source.restrict (FaceMap.delete k) = target
  · simp [SimplicialChain.faceContribution, hface]
  · simp [SimplicialChain.faceContribution, hface]

/-- An ordinary simplicial cycle as a finite incidence cycle. -/
noncomputable def ofCycle
    (chain : SimplicialChain R p (d + 1))
    (hcycle : SimplicialChain.boundary chain = 0) :
    FiniteIncidenceCycle R where
  TopCell := Simplex p (d + 1)
  Facet := Simplex p d
  incidence := incidence
  coefficient := chain
  boundary_zero := by
    intro target
    rw [← boundary_apply_eq_incidence]
    rw [hcycle]
    rfl

end SimplicialIncidence

/-- Vertex data for a map that is affine on every simplex of the order complex.  The target is an
explicit `d`-dimensional real coordinate space. -/
structure AffineVertexMap (p d : Nat) where
  vertexValue : BarredPermutation p → Fin d → ℝ

namespace AffineVertexMap

/-- Affine extension of vertex values over one order-complex simplex. -/
noncomputable def value
    (f : AffineVertexMap p d)
    (s : Simplex p d)
    (w : StandardSimplex d) : Fin d → ℝ :=
  fun r => ∑ i : Fin (d + 1), w i * f.vertexValue (s i) r

/-- Augmented affine matrix.  Its columns are the target values of the simplex vertices and its
last row consists of ones. -/
def augmentedMatrix
    (f : AffineVertexMap p d) (s : Simplex p d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun r i => Fin.lastCases (1 : ℝ) (fun q => f.vertexValue (s i) q) r

/-- Determinant controlling regularity and the local orientation of the affine map. -/
noncomputable def determinant
    (f : AffineVertexMap p d) (s : Simplex p d) : ℝ :=
  Matrix.det (f.augmentedMatrix s)

/-- The affine restriction has a zero in the relative interior of the simplex. -/
def HasInteriorZero
    (f : AffineVertexMap p d) (s : Simplex p d) : Prop :=
  ∃ w : StandardSimplex d,
    StandardSimplex.IsInterior w ∧ ∀ r, f.value s w r = 0

/-- The restriction is regular when its augmented affine matrix is nonsingular. -/
def IsRegularOn
    (f : AffineVertexMap p d) (s : Simplex p d) : Prop :=
  f.determinant s ≠ 0

/-- Global finite regularity on all top-dimensional simplices. -/
def IsRegular (f : AffineVertexMap p d) : Prop :=
  ∀ s : Simplex p d, f.IsRegularOn s

/-- Sign of a real determinant, reduced to the coefficient field `ZMod p`. -/
noncomputable def determinantIndex (x : ℝ) : ZMod p :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- Local signed zero index of one affine simplex. -/
noncomputable def localZeroIndex
    (f : AffineVertexMap p d) (s : Simplex p d) : ZMod p := by
  classical
  exact if f.HasInteriorZero s then determinantIndex (p := p) (f.determinant s) else 0

/-- Local-index function used in the finite cycle pairing. -/
noncomputable def localIndexCochain
    (f : AffineVertexMap p d) : Simplex p d → ZMod p :=
  fun s => f.localZeroIndex s

end AffineVertexMap

/-- Concrete finite affine zero count on an ordinary simplicial chain.  The orbit-count version
uses the same `FiniteIncidenceCycle.zeroCount` operation after replacing top simplices by their
prime-symmetry orbit cells. -/
noncomputable def simplicialAffineZeroCount
    (chain : SimplicialChain (ZMod p) p d)
    (f : AffineVertexMap p d) : ZMod p :=
  ∑ s : Simplex p d, chain s * f.localZeroIndex s

end FoxNeuwirthOrderComplex

/-- Proof-carrying finite orbit model for the finite zero count.  The top and facet types are
intended to be prime-symmetry orbits of transverse simplices and prism facets. -/
structure FiniteOrbitZeroCountModel {p : Nat} (hp : Nat.Prime p) where
  cycle : FiniteIncidenceCycle (ZMod p)
  topSimplex : cycle.TopCell → FoxNeuwirthOrderComplex.Simplex p (p - 1)
  referenceMap : FoxNeuwirthOrderComplex.AffineVertexMap p (p - 1)
  referenceRegular : referenceMap.IsRegular
  referenceIndex : cycle.TopCell → ZMod p
  referenceIndex_eq :
    ∀ c, referenceIndex c = referenceMap.localZeroIndex (topSimplex c)
  referenceCount_eq :
    cycle.zeroCount referenceIndex = FoxNeuwirth.referenceSignedOrbitCount hp

namespace FiniteOrbitZeroCountModel

variable {p : Nat} {hp : Nat.Prime p}

/-- The reference orbit count of the finite affine model is nonzero modulo the prime. -/
theorem referenceCount_ne_zero (M : FiniteOrbitZeroCountModel hp) :
    M.cycle.zeroCount M.referenceIndex ≠ 0 := by
  rw [M.referenceCount_eq]
  exact FoxNeuwirth.referenceSignedOrbitCount_ne_zero hp

/-- Endpoint data for an affine family: its local-index function is related to the reference
function by a finite incidence transgression. -/
structure EndpointData (M : FiniteOrbitZeroCountModel hp) where
  map : FoxNeuwirthOrderComplex.AffineVertexMap p (p - 1)
  regular : map.IsRegular
  homotopy : M.cycle.IndexHomotopy M.referenceIndex
    (fun c => map.localZeroIndex (M.topSimplex c))

namespace EndpointData

/-- Local-index function of an affine endpoint on the orbit representatives. -/
noncomputable def index
    {M : FiniteOrbitZeroCountModel hp} (D : M.EndpointData) :
    M.cycle.TopCell → ZMod p :=
  fun c => D.map.localZeroIndex (M.topSimplex c)

/-- Every regular affine endpoint connected to the reference index by an admissible finite
homotopy has nonzero orbit zero count. -/
theorem zeroCount_ne_zero
    {M : FiniteOrbitZeroCountModel hp} (D : M.EndpointData) :
    M.cycle.zeroCount D.index ≠ 0 := by
  change M.cycle.zeroCount
    (fun c => D.map.localZeroIndex (M.topSimplex c)) ≠ 0
  exact D.homotopy.zeroCount_ne_zero M.referenceCount_ne_zero

end EndpointData

end FiniteOrbitZeroCountModel

end NRR

namespace NRR

namespace FiniteIncidenceCycle

variable {R : Type*} [CommRing R]

/-- A nonzero cycle pairing has at least one top cell with nonzero local index. -/
theorem exists_index_ne_zero_of_zeroCount_ne_zero
    {C : FiniteIncidenceCycle R}
    {index : C.TopCell → R}
    (hcount : C.zeroCount index ≠ 0) :
    ∃ c : C.TopCell, index c ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hcount
  simp [FiniteIncidenceCycle.zeroCount, h]

end FiniteIncidenceCycle

namespace FoxNeuwirthOrderComplex
namespace AffineVertexMap

variable {p d : Nat}

/-- A nonzero local affine index certifies a relative-interior zero. -/
theorem hasInteriorZero_of_localZeroIndex_ne_zero
    (f : AffineVertexMap p d) (s : Simplex p d)
    (hindex : f.localZeroIndex s ≠ 0) :
    f.HasInteriorZero s := by
  classical
  by_contra hzero
  apply hindex
  simp [localZeroIndex, hzero]

end AffineVertexMap
end FoxNeuwirthOrderComplex

namespace FiniteOrbitZeroCountModel

variable {p : Nat} {hp : Nat.Prime p}

namespace EndpointData

/-- A nonzero finite orbit count produces an orbit representative simplex containing a
relative-interior zero of the affine endpoint map. -/
theorem exists_topCell_hasInteriorZero
    {M : FiniteOrbitZeroCountModel hp} (D : M.EndpointData) :
    ∃ c : M.cycle.TopCell,
      D.map.HasInteriorZero (M.topSimplex c) := by
  obtain ⟨c, hc⟩ :=
    FiniteIncidenceCycle.exists_index_ne_zero_of_zeroCount_ne_zero D.zeroCount_ne_zero
  refine ⟨c, ?_⟩
  exact FoxNeuwirthOrderComplex.AffineVertexMap.hasInteriorZero_of_localZeroIndex_ne_zero
    D.map (M.topSimplex c) (by simpa [index] using hc)

end EndpointData
end FiniteOrbitZeroCountModel

end NRR
