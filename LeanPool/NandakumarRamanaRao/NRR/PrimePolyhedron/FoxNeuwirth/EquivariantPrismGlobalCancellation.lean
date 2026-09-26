/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismSubdivisionMargin
/-!
# Global signed cancellation for the refined equivariant prism

The compatible perturbation assigns one vector to every global sampled prism vertex.  Hence the
positive-ray index of a codimension-one face depends only on its ordered list of global vertices,
not on the refined prism simplex in which that face is encountered.

This file turns the local affine boundary theorem into a single global finite cancellation identity.
A facet occurrence is a pair consisting of a refined prism simplex and an omitted vertex.  Its
ordered global-vertex signature records the induced parametrized facet.  Occurrences with the same
signature have the same unsigned positive-ray index.  After multiplying by the orbit-cycle,
spatial-subdivision, staircase, prism-subdivision, and alternating face signs, the sum over all
facet occurrences is zero.

The final section separates signatures in the lower horizontal layer, the upper horizontal layer,
and the nonhorizontal part. The endpoint module proves vanishing of the nonhorizontal contribution
and identifies the horizontal sums with the endpoint refined counts.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open SphereOddDegree
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismGlobalCancellation

attribute [local simp] Matrix.fromBlocks_apply₁₁ Matrix.fromBlocks_apply₁₂
  Matrix.fromBlocks_apply₂₁ Matrix.fromBlocks_apply₂₂
attribute [local simp] Matrix.fromBlocks

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGenericPerturbation
open SubdivisionPrismCharts
open RefinedAffineMap

variable {p : Nat}

/-- Positive-ray index of an oriented facet before multiplication by its alternating boundary
sign. -/
noncomputable def unsignedFacetIndex
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) : ZMod p :=
  if FacetHasPositiveRayIntersection hp V k then
    FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex
      (facetDeterminant hp V k)
  else 0

/-- Transport an omitted facet vertex to the face-index type used by the simplicial boundary. -/
def facetFaceIndex
    (hp : Nat.Prime p) (k : Fin (p + 1)) : Fin ((p - 1) + 2) :=
  Fin.cast (by have := hp.two_le; omega) k

@[simp] theorem facetFaceIndex_val
    (hp : Nat.Prime p) (k : Fin (p + 1)) :
    (facetFaceIndex hp k).1 = k.1 := rfl

/-- The local signed facet index is the alternating face sign times the unsigned face index. -/
theorem facetIndex_eq_faceSign_mul_unsignedFacetIndex
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    facetIndex hp V k =
      SimplicialChain.faceSign (R := ZMod p) (d := p - 1) (facetFaceIndex hp k) *
        unsignedFacetIndex hp V k := by
  classical
  by_cases h : FacetHasPositiveRayIntersection hp V k
  · simp [facetIndex, unsignedFacetIndex, h, facetFaceIndex, SimplicialChain.faceSign]
  · simp [facetIndex, unsignedFacetIndex, h, facetFaceIndex, SimplicialChain.faceSign]

/-- If two oriented facets have the same ordered vertex values, their unsigned positive-ray
indices agree. -/
theorem unsignedFacetIndex_eq_of_facetValue_eq
    (hp : Nat.Prime p)
    (V W : VertexMap p) (k l : Fin (p + 1))
    (hvalue : ∀ i : Fin p, facetValue V k i = facetValue W l i) :
    unsignedFacetIndex hp V k = unsignedFacetIndex hp W l := by
  classical
  have hmatrix : facetMatrix hp V k = facetMatrix hp W l := by
    ext r i
    simp [facetMatrix, hvalue]
  have hdet : facetDeterminant hp V k = facetDeterminant hp W l := by
    simp [facetDeterminant, hmatrix]
  have haffine :
      ∀ w : StandardSimplex (p - 1),
        facetAffineValue V k w = facetAffineValue W l w := by
    intro w
    funext r
    unfold facetAffineValue
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvalue i]
  have hinter :
      FacetHasPositiveRayIntersection hp V k ↔
        FacetHasPositiveRayIntersection hp W l := by
    constructor
    · rintro ⟨w, hwint, hwdev, hwmean⟩
      refine ⟨w, hwint, ?_, ?_⟩
      · intro r
        rw [← haffine w]
        exact hwdev r
      · rw [← haffine w]
        exact hwmean
    · rintro ⟨w, hwint, hwdev, hwmean⟩
      refine ⟨w, hwint, ?_, ?_⟩
      · intro r
        rw [haffine w]
        exact hwdev r
      · rw [haffine w]
        exact hwmean
  unfold unsignedFacetIndex
  by_cases hV : FacetHasPositiveRayIntersection hp V k
  · have hW : FacetHasPositiveRayIntersection hp W l := hinter.mp hV
    rw [ite_eq_left hV, ite_eq_left hW, hdet]
  · have hW : ¬ FacetHasPositiveRayIntersection hp W l :=
      fun h => hV (hinter.mpr h)
    rw [ite_eq_right hV, ite_eq_right hW]

/-- Relabel every output coordinate vector of a local affine simplex by a prime symmetry. -/
noncomputable def primeSmulVertexMap
    (p : Nat) (g : PrimeSymmetry p) (V : VertexMap p) : VertexMap p where
  value i := g • V.value i

@[simp] theorem primeSmulVertexMap_value
    (p : Nat) (g : PrimeSymmetry p) (V : VertexMap p) (i : Fin (p + 1)) :
    (primeSmulVertexMap p g V).value i = g • V.value i := rfl

/-- The square coordinate matrix of a facet before passing to fixed differences. -/
private noncomputable def facetCoordinateMatrix
    (V : VertexMap p) (k : Fin (p + 1)) : Matrix (Fin p) (Fin p) Real :=
  fun r i => facetValue V k i r

/-- Border the coordinate matrix by a column and row of ones.  This matrix makes coordinate
relabeling an honest row permutation. -/
private noncomputable def facetBorderedMatrix
    (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) Real :=
  Matrix.fromBlocks
    (facetCoordinateMatrix V k)
    (fun _ _ => 1)
    (fun _ _ => 1)
    (fun _ _ => 0)

/-- Multiples of the distinguished coordinate row used to form fixed differences. -/
private def facetRowCoefficient
    (hp : Nat.Prime p) : Fin p ⊕ Unit → Real
  | Sum.inl r => if r = ReferenceAffineOrbitCount.lastLabel hp then 0 else -1
  | Sum.inr _ => 0

/-- Subtract the distinguished coordinate row from every other coordinate row. -/
private noncomputable def facetRowReducedMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) Real :=
  fun r c =>
    facetBorderedMatrix V k r c +
      facetRowCoefficient hp r *
        facetBorderedMatrix V k (Sum.inl (ReferenceAffineOrbitCount.lastLabel hp)) c

/-- Swap the distinguished coordinate row with the border row. -/
private def facetBorderSwap
    (hp : Nat.Prime p) : Equiv.Perm (Fin p ⊕ Unit) :=
  Equiv.swap (Sum.inl (ReferenceAffineOrbitCount.lastLabel hp)) (Sum.inr ())

/-- The block form obtained after row subtraction and the final row swap. -/
private noncomputable def facetBlockMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) Real :=
  Matrix.fromBlocks
    (facetMatrix hp V k)
    0
    (fun _ i => facetValue V k i (ReferenceAffineOrbitCount.lastLabel hp))
    1

private theorem augmentedRowEquiv_lastLabel
    (hp : Nat.Prime p) :
    augmentedRowEquiv hp (ReferenceAffineOrbitCount.lastLabel hp) =
      Fin.last (p - 1) := by
  apply Fin.ext
  rfl

private theorem augmentedRowEquiv_coordinateLabel
    (hp : Nat.Prime p) (q : Fin (p - 1)) :
    augmentedRowEquiv hp (ReferenceAffineOrbitCount.coordinateLabel hp q) = q.castSucc := by
  apply Fin.ext
  rfl

private theorem facetBlockMatrix_eq_swappedRowReduced
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    facetBlockMatrix hp V k =
      (facetRowReducedMatrix hp V k).submatrix (facetBorderSwap hp) id := by
  classical
  ext r c
  rcases r with r | u
  · rcases c with c | v
    · by_cases hr : r = ReferenceAffineOrbitCount.lastLabel hp
      · subst r
        simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
          facetRowCoefficient, facetBorderedMatrix, facetCoordinateMatrix,
          facetMatrix, augmentedRowEquiv_lastLabel, Matrix.fromBlocks]
      · have hrmem : r ∈ {x : Fin p |
            x ≠ ReferenceAffineOrbitCount.lastLabel hp} := hr
        rw [← ReferenceAffineOrbitCount.coordinateLabel_range hp] at hrmem
        obtain ⟨q, rfl⟩ := hrmem
        have hq : ReferenceAffineOrbitCount.coordinateLabel hp q ≠
            ReferenceAffineOrbitCount.lastLabel hp := by
          intro h
          have hv := congrArg Fin.val h
          simp [ReferenceAffineOrbitCount.coordinateLabel,
            ReferenceAffineOrbitCount.lastLabel] at hv
          omega
        simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
          facetRowCoefficient, facetBorderedMatrix, facetCoordinateMatrix,
          facetMatrix, augmentedRowEquiv_coordinateLabel, VertexMap.deviation, hq,
          Equiv.swap_apply_of_ne_of_ne, sub_eq_add_neg]
    · rcases v with ⟨⟩
      by_cases hr : r = ReferenceAffineOrbitCount.lastLabel hp
      · subst r
        simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
          facetRowCoefficient, facetBorderedMatrix]
      · have hrmem : r ∈ {x : Fin p |
            x ≠ ReferenceAffineOrbitCount.lastLabel hp} := hr
        rw [← ReferenceAffineOrbitCount.coordinateLabel_range hp] at hrmem
        obtain ⟨q, rfl⟩ := hrmem
        have hq : ReferenceAffineOrbitCount.coordinateLabel hp q ≠
            ReferenceAffineOrbitCount.lastLabel hp := by
          intro h
          have hv := congrArg Fin.val h
          simp [ReferenceAffineOrbitCount.coordinateLabel,
            ReferenceAffineOrbitCount.lastLabel] at hv
          omega
        simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
          facetRowCoefficient, facetBorderedMatrix,  hq,
          Equiv.swap_apply_of_ne_of_ne]
  · rcases u with ⟨⟩
    rcases c with c | v
    · simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
        facetRowCoefficient, facetBorderedMatrix, facetCoordinateMatrix]
    · rcases v with ⟨⟩
      simp [facetBlockMatrix, facetRowReducedMatrix, facetBorderSwap,
        facetRowCoefficient, facetBorderedMatrix]

private theorem det_facetRowReducedMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix.det (facetRowReducedMatrix hp V k) = Matrix.det (facetBorderedMatrix V k) := by
  classical
  exact Matrix.det_eq_of_forall_row_eq_smul_add_const
    (A := facetRowReducedMatrix hp V k)
    (B := facetBorderedMatrix V k)
    (facetRowCoefficient hp)
    (Sum.inl (ReferenceAffineOrbitCount.lastLabel hp))
    (by simp [facetRowCoefficient])
    (by intro i j; rfl)

private theorem det_facetBlockMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix.det (facetBlockMatrix hp V k) = facetDeterminant hp V k := by
  classical
  let C : Matrix Unit (Fin p) Real :=
    fun _ i => facetValue V k i (ReferenceAffineOrbitCount.lastLabel hp)
  have h := Matrix.det_fromBlocks_zero₁₂
    (facetMatrix hp V k) C (1 : Matrix Unit Unit Real)
  change (Matrix.fromBlocks (facetMatrix hp V k) 0 C 1).det = (facetMatrix hp V k).det
  simpa using h

/-- The bordered coordinate determinant is the negative of the fixed-difference facet
 determinant. -/
private theorem det_facetBorderedMatrix
    (hp : Nat.Prime p) (V : VertexMap p) (k : Fin (p + 1)) :
    Matrix.det (facetBorderedMatrix V k) = -facetDeterminant hp V k := by
  classical
  have hswap : Matrix.det (facetBlockMatrix hp V k) =
      -Matrix.det (facetRowReducedMatrix hp V k) := by
    rw [facetBlockMatrix_eq_swappedRowReduced]
    rw [Matrix.det_permute]
    simp [facetBorderSwap]
  rw [det_facetBlockMatrix, det_facetRowReducedMatrix] at hswap
  linarith

/-- Extend a prime coordinate permutation by fixing the border row. -/
private def primeBorderRowPerm
    (p : Nat) (g : PrimeSymmetry p) : Equiv.Perm (Fin p ⊕ Unit) :=
  Equiv.sumCongr (PrimeSymmetry.toPerm p g).symm (Equiv.refl Unit)

private theorem sign_primeBorderRowPerm
    (p : Nat) (g : PrimeSymmetry p) :
    Equiv.Perm.sign (primeBorderRowPerm p g) =
      Equiv.Perm.sign (PrimeSymmetry.toPerm p g) := by
  simp [primeBorderRowPerm, Equiv.Perm.sign_sumCongr]

private theorem facetBorderedMatrix_primeSmul
    (p : Nat) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) :
    facetBorderedMatrix (primeSmulVertexMap p g V) k =
      (facetBorderedMatrix V k).submatrix (primeBorderRowPerm p g) id := by
  classical
  ext r c
  rcases r with r | u
  · rcases c with c | v
    · simp [facetBorderedMatrix, facetCoordinateMatrix, primeBorderRowPerm,
        primeSmulVertexMap, facetValue, PrimeSymmetry.smul_coordinate_apply]
    · rcases v with ⟨⟩
      simp [facetBorderedMatrix,  primeBorderRowPerm]
  · rcases u with ⟨⟩
    rcases c with c | v
    · simp [facetBorderedMatrix,  primeBorderRowPerm]
    · rcases v with ⟨⟩
      simp [facetBorderedMatrix,  primeBorderRowPerm]

/-- Exact determinant transformation under prime coordinate relabeling. -/
private theorem facetDeterminant_primeSmul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) :
    facetDeterminant hp (primeSmulVertexMap p g V) k =
      ((((Equiv.Perm.sign (PrimeSymmetry.toPerm p g) : ℤˣ) : ℤ) : Real)) *
        facetDeterminant hp V k := by
  classical
  have hnew := det_facetBorderedMatrix hp (primeSmulVertexMap p g V) k
  have hold := det_facetBorderedMatrix hp V k
  have hperm :
      Matrix.det (facetBorderedMatrix (primeSmulVertexMap p g V) k) =
        ((((Equiv.Perm.sign (PrimeSymmetry.toPerm p g) : ℤˣ) : ℤ) : Real)) *
          Matrix.det (facetBorderedMatrix V k) := by
    rw [facetBorderedMatrix_primeSmul p, Matrix.det_permute,
      sign_primeBorderRowPerm p]
  rw [hperm, hold] at hnew
  linarith

/-- Prime relabelling preserves nonvanishing of every oriented facet determinant. -/
theorem facetDeterminant_primeSmul_ne_zero_iff
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) :
    facetDeterminant hp (primeSmulVertexMap p g V) k ≠ 0 ↔
      facetDeterminant hp V k ≠ 0 := by
  rw [facetDeterminant_primeSmul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (PrimeSymmetry.toPerm p g)) with h | h
  · simp []
  · simp []

private theorem deviations_eq_zero_of_coordinateDeviation_eq_zero
    (hp : Nat.Prime p) (y : Fin p → Real)
    (h : coordinateDeviation hp.pos y = 0) :
    ∀ q : Fin (p - 1), deviation hp y q = 0 := by
  intro q
  have hq := congrArg
    (fun z : ZeroSum p => z (ReferenceAffineOrbitCount.coordinateLabel hp q)) h
  have hlast := congrArg
    (fun z : ZeroSum p => z (ReferenceAffineOrbitCount.lastLabel hp)) h
  simp only [coordinateDeviation_apply, ZeroSum.zero_apply] at hq hlast
  unfold deviation
  linarith

private theorem facetAffineValue_primeSmul
    (p : Nat) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) (w : StandardSimplex (p - 1)) :
    facetAffineValue (primeSmulVertexMap p g V) k w =
      g • facetAffineValue V k w := by
  funext r
  simp [facetAffineValue, facetValue, primeSmulVertexMap,
    PrimeSymmetry.smul_coordinate_apply]

private theorem facetHasPositiveRayIntersection_primeSmul_iff
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) :
    FacetHasPositiveRayIntersection hp (primeSmulVertexMap p g V) k ↔
      FacetHasPositiveRayIntersection hp V k := by
  classical
  constructor
  · rintro ⟨w, hwint, hwdev, hwmean⟩
    refine ⟨w, hwint, ?_, ?_⟩
    · apply deviations_eq_zero_of_coordinateDeviation_eq_zero hp
        (facetAffineValue V k w)
      have hsmul : g • coordinateDeviation hp.pos (facetAffineValue V k w) = 0 := by
        rw [← coordinateDeviation_prime_smul hp]
        rw [← facetAffineValue_primeSmul p g V k w]
        exact coordinateDeviation_eq_zero_of_deviation_eq_zero hp _ hwdev
      have hinv := congrArg (fun z : ZeroSum p => g⁻¹ • z) hsmul
      simpa [smul_smul] using hinv
    · have hmeanEq :
          mean p (facetAffineValue (primeSmulVertexMap p g V) k w) =
            mean p (facetAffineValue V k w) := by
        rw [facetAffineValue_primeSmul p]
        simpa [mean] using
          coordinateMean_prime_smul p (facetAffineValue V k w) g
      rw [← hmeanEq]
      exact hwmean
  · rintro ⟨w, hwint, hwdev, hwmean⟩
    refine ⟨w, hwint, ?_, ?_⟩
    · apply deviations_eq_zero_of_coordinateDeviation_eq_zero hp
        (facetAffineValue (primeSmulVertexMap p g V) k w)
      rw [facetAffineValue_primeSmul p, coordinateDeviation_prime_smul hp,
        coordinateDeviation_eq_zero_of_deviation_eq_zero hp _ hwdev]
      simp
    · have hmeanEq :
          mean p (facetAffineValue (primeSmulVertexMap p g V) k w) =
            mean p (facetAffineValue V k w) := by
        rw [facetAffineValue_primeSmul p]
        simpa [mean] using
          coordinateMean_prime_smul p (facetAffineValue V k w) g
      rw [hmeanEq]
      exact hwmean

private theorem determinantIndex_neg
    (x : Real) :
    FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex (p := p) (-x) =
      -FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex (p := p) x := by
  unfold FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex
  by_cases hpos : 0 < x
  · have hnneg : -x < 0 := neg_neg_of_pos hpos
    have hnpos : ¬ 0 < -x := not_lt.mpr (le_of_lt hnneg)
    have hxneg : ¬ x < 0 := not_lt.mpr (le_of_lt hpos)
    simp [hpos,  hnpos, hnneg]
  · by_cases hneg : x < 0
    · have hnpos : 0 < -x := neg_pos.mpr hneg
      have hnneg : ¬ -x < 0 := not_lt.mpr (le_of_lt hnpos)
      simp [hpos, hneg, hnpos]
    · have hx : x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      subst x
      simp

private theorem determinantIndex_sign_mul
    (ε : ℤˣ) (x : Real) :
    FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex (p := p)
        ((((ε : ℤ) : Real)) * x) =
      (((ε : ℤ) : ZMod p)) *
        FoxNeuwirthOrderComplex.AffineVertexMap.determinantIndex (p := p) x := by
  rcases Int.units_eq_one_or ε with h | h
  · rw [h]
    simp
  · rw [h]
    simpa using (determinantIndex_neg (p := p) x)

/-- Prime relabelling preserves the unsigned positive-ray index.  The open diagonal ray and the
coordinate mean are invariant under coordinate permutation; the determinant changes by the sign
of the selected prime permutation, whose image in `ZMod p` is one. -/
theorem unsignedFacetIndex_primeSmul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) :
    unsignedFacetIndex hp (primeSmulVertexMap p g V) k =
      unsignedFacetIndex hp V k := by
  classical
  have hinter := facetHasPositiveRayIntersection_primeSmul_iff hp g V k
  unfold unsignedFacetIndex
  by_cases h : FacetHasPositiveRayIntersection hp V k
  · have h' : FacetHasPositiveRayIntersection hp (primeSmulVertexMap p g V) k :=
      hinter.mpr h
    rw [ite_eq_left h', ite_eq_left h, facetDeterminant_primeSmul,
      determinantIndex_sign_mul,
      PrimeOrbitCycle.primeSymmetry_sign_cast_eq_one]
    simp
  · have h' : ¬ FacetHasPositiveRayIntersection hp (primeSmulVertexMap p g V) k :=
      fun hg => h (hinter.mp hg)
    rw [ite_eq_right h', ite_eq_right h]


/-- If the ordered values of one facet are a simultaneous prime relabelling of another, their
unsigned positive-ray indices agree. -/
theorem unsignedFacetIndex_eq_of_facetValue_eq_primeSmul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (V W : VertexMap p) (k l : Fin (p + 1))
    (hvalue : ∀ i : Fin p, facetValue W l i = g • facetValue V k i) :
    unsignedFacetIndex hp W l = unsignedFacetIndex hp V k := by
  calc
    unsignedFacetIndex hp W l =
        unsignedFacetIndex hp (primeSmulVertexMap p g V) k := by
      apply unsignedFacetIndex_eq_of_facetValue_eq hp
      intro i
      simpa [primeSmulVertexMap, facetValue] using hvalue i
    _ = unsignedFacetIndex hp V k :=
      unsignedFacetIndex_primeSmul hp g V k

/-- One codimension-one occurrence in the fully refined prism triangulation. -/
abbrev FacetOccurrence (hp : Nat.Prime p) (N L : Nat) :=
  PrismCell hp N L × Fin (p + 1)

noncomputable instance (hp : Nat.Prime p) (N L : Nat) :
    Fintype (FacetOccurrence hp N L) := inferInstance
noncomputable instance (hp : Nat.Prime p) (N L : Nat) :
    DecidableEq (FacetOccurrence hp N L) := inferInstance

/-- Ordered global vertices of one induced prism facet.  Equality of signatures means equality as
an ordered sampled facet, which is the correct relation for oriented boundary cancellation. -/
noncomputable def facetSignature
    (hp : Nat.Prime p) (N L : Nat)
    (o : FacetOccurrence hp N L) : Fin p → GlobalVertex hp N L :=
  fun i => sampleVertex hp N L (o.1, o.2.succAbove i)

/-- Finite type of possible ordered global-vertex signatures. -/
abbrev FacetSignature (hp : Nat.Prime p) (N L : Nat) :=
  Fin p → GlobalVertex hp N L

noncomputable instance facetSignatureFintype
    (hp : Nat.Prime p) (N L : Nat) :
    Fintype (FacetSignature hp N L) := Fintype.ofFinite _

noncomputable instance facetSignatureDecidableEq
    (hp : Nat.Prime p) (N L : Nat) :
    DecidableEq (FacetSignature hp N L) := Classical.decEq _

/-- Equal ordered facet signatures give equal ordered local vertex values. -/
theorem facetValue_eq_of_signature_eq
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    {o o' : FacetOccurrence hp N L}
    (h : facetSignature hp N L o = facetSignature hp N L o')
    (i : Fin p) :
    facetValue (localVertexMap hp N L a o.1) o.2 i =
      facetValue (localVertexMap hp N L a o'.1) o'.2 i := by
  change vectorValue hp N L a (facetSignature hp N L o i) =
    vectorValue hp N L a (facetSignature hp N L o' i)
  rw [congrFun h i]

/-- The unsigned index of a local occurrence depends only on its ordered global-vertex signature. -/
theorem unsignedFacetIndex_eq_of_signature_eq
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    {o o' : FacetOccurrence hp N L}
    (h : facetSignature hp N L o = facetSignature hp N L o') :
    unsignedFacetIndex hp (localVertexMap hp N L a o.1) o.2 =
      unsignedFacetIndex hp (localVertexMap hp N L a o'.1) o'.2 := by
  apply unsignedFacetIndex_eq_of_facetValue_eq hp
  intro i
  exact facetValue_eq_of_signature_eq hp N L a h i

/-- A chosen unsigned index for an ordered global facet signature.  If the signature is not
realized by the triangulation, its value is zero. -/
noncomputable def signatureWeight
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (s : FacetSignature hp N L) : ZMod p := by
  classical
  by_cases h : ∃ o : FacetOccurrence hp N L, facetSignature hp N L o = s
  · exact unsignedFacetIndex hp
      (localVertexMap hp N L a (Classical.choose h).1)
      (Classical.choose h).2
  · exact 0

/-- On a realized signature, the chosen global weight is the unsigned index of every occurrence
with that signature. -/
theorem signatureWeight_facetSignature
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (o : FacetOccurrence hp N L) :
    signatureWeight hp N L a (facetSignature hp N L o) =
      unsignedFacetIndex hp (localVertexMap hp N L a o.1) o.2 := by
  classical
  unfold signatureWeight
  split_ifs with h
  · exact unsignedFacetIndex_eq_of_signature_eq hp N L a
      (Classical.choose_spec h)
  · exact (h ⟨o, rfl⟩).elim

/-- Coefficient of one fully refined prism simplex.  It combines the original orbit-cycle
coefficient, the spatial barycentric-subdivision sign, the staircase sign, and the further prism
subdivision sign. -/
noncomputable def prismCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) : ZMod p :=
  (PrimeOrbitCycle.orbitCycle hp).coefficient q.1.1.1 *
    subdivisionSign N q.1.1.2 *
      (prismSign q : ZMod p)

/-- Signed incidence coefficient of one facet occurrence in the global refined prism chain. -/
noncomputable def occurrenceCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (o : FacetOccurrence hp N L) : ZMod p :=
  prismCoefficient hp N L o.1 *
    SimplicialChain.faceSign (R := ZMod p) (d := p - 1) (facetFaceIndex hp o.2)

/-- Total signed boundary coefficient of one ordered global facet signature. -/
noncomputable def signatureBoundaryCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) : ZMod p :=
  ∑ o : FacetOccurrence hp N L,
    if facetSignature hp N L o = s then occurrenceCoefficient hp N L o else 0

/-- Expanded global signed positive-ray boundary sum over all local facet occurrences. -/
noncomputable def globalSignedFacetSum
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ o : FacetOccurrence hp N L,
    occurrenceCoefficient hp N L o *
      signatureWeight hp N L a (facetSignature hp N L o)

/-- The expanded occurrence sum is the sum over geometric ordered facet signatures of boundary
coefficient times the common unsigned positive-ray index. -/
theorem globalSignedFacetSum_eq_signature_sum
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) :
    globalSignedFacetSum hp N L a =
      ∑ s : FacetSignature hp N L,
        signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s := by
  classical
  unfold globalSignedFacetSum signatureBoundaryCoefficient
  calc
    (∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          signatureWeight hp N L a (facetSignature hp N L o)) =
      ∑ o : FacetOccurrence hp N L,
        ∑ s : FacetSignature hp N L,
          if facetSignature hp N L o = s then
            occurrenceCoefficient hp N L o * signatureWeight hp N L a s
          else 0 := by
      apply Finset.sum_congr rfl
      intro o ho
      simp [eq_comm]
    _ = ∑ s : FacetSignature hp N L,
        ∑ o : FacetOccurrence hp N L,
          if facetSignature hp N L o = s then
            occurrenceCoefficient hp N L o * signatureWeight hp N L a s
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ s : FacetSignature hp N L,
        (∑ o : FacetOccurrence hp N L,
          if facetSignature hp N L o = s then occurrenceCoefficient hp N L o else 0) *
            signatureWeight hp N L a s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro o ho
      split_ifs <;> simp

/-- The global occurrence sum can equally be grouped by refined prism simplices and written using
the local signed facet indices. -/
theorem globalSignedFacetSum_eq_local_boundary_sum
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) :
    globalSignedFacetSum hp N L a =
      ∑ q : PrismCell hp N L,
        prismCoefficient hp N L q *
          (∑ k : Fin (p + 1),
            facetIndex hp (localVertexMap hp N L a q) k) := by
  classical
  unfold globalSignedFacetSum occurrenceCoefficient
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [signatureWeight_facetSignature]
  rw [facetIndex_eq_faceSign_mul_unsignedFacetIndex]
  ring

/-- Global signed prism-facet cancellation.  Under local general position, every local affine
boundary sum is zero, so the globally glued signed sum over all refined prism facets vanishes. -/
theorem globalSignedFacetSum_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      GeneralPosition hp (localVertexMap hp N L a q)) :
    globalSignedFacetSum hp N L a = 0 := by
  rw [globalSignedFacetSum_eq_local_boundary_sum]
  apply Finset.sum_eq_zero
  intro q hq
  have hzero :=
    NRR.AffinePositiveRayBoundary.VertexMap.alternating_facetIndex_sum_eq_zero_of_generalPosition
      hp (localVertexMap hp N L a q) (hgp q)
  exact mul_eq_zero_of_right _ hzero

/-- Public global signed prism-facet cancellation theorem.  The sum ranges over every fully
refined prism simplex and every oriented facet occurrence. -/
theorem global_signed_prism_facet_cancellation
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      GeneralPosition hp (localVertexMap hp N L a q)) :
    globalSignedFacetSum hp N L a = 0 :=
  globalSignedFacetSum_eq_zero hp N L a hgp

/-- Signature-level form of global signed cancellation. -/
theorem signature_weighted_boundary_sum_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      GeneralPosition hp (localVertexMap hp N L a q)) :
    (∑ s : FacetSignature hp N L,
      signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s) = 0 := by
  rw [← globalSignedFacetSum_eq_signature_sum]
  exact globalSignedFacetSum_eq_zero hp N L a hgp

/-- Global occurrence-level cancellation specialized to the compatible generic perturbation. -/
theorem Result.global_signed_prism_facet_cancellation
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : Result hp N L H m) :
    globalSignedFacetSum hp N L R.assignment = 0 :=
  EquivariantPrismGlobalCancellation.global_signed_prism_facet_cancellation
    hp N L R.assignment R.generalPosition

/-- Cancellation specialized to the assignment produced by the generic perturbation theorem. -/
theorem Result.signature_weighted_boundary_sum_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : Result hp N L H m) :
    (∑ s : FacetSignature hp N L,
      signatureBoundaryCoefficient hp N L s *
        signatureWeight hp N L R.assignment s) = 0 :=
  EquivariantPrismGlobalCancellation.signature_weighted_boundary_sum_eq_zero
    hp N L R.assignment R.generalPosition

/-! ## Horizontal and nonhorizontal decomposition -/

/-- Time coordinate of one vertex in an ordered global facet signature. -/
noncomputable def signatureTime
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) (i : Fin p) : Real :=
  (globalPoint hp N L (s i)).time.1

/-- A facet signature lies in the lower horizontal layer. -/
def IsLowerHorizontal
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) : Prop :=
  ∀ i : Fin p, signatureTime hp N L s i = 0

/-- A facet signature lies in the upper horizontal layer. -/
def IsUpperHorizontal
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) : Prop :=
  ∀ i : Fin p, signatureTime hp N L s i = 1

noncomputable instance isLowerHorizontalDecidable
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) : Decidable (IsLowerHorizontal hp N L s) :=
  Classical.propDecidable _

noncomputable instance isUpperHorizontalDecidable
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) : Decidable (IsUpperHorizontal hp N L s) :=
  Classical.propDecidable _

/-- Lower horizontal contribution to the global signed facet sum. -/
noncomputable def lowerHorizontalContribution
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ s : FacetSignature hp N L,
    if IsLowerHorizontal hp N L s then
      signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s
    else 0

/-- Upper horizontal contribution to the global signed facet sum. -/
noncomputable def upperHorizontalContribution
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ s : FacetSignature hp N L,
    if IsUpperHorizontal hp N L s then
      signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s
    else 0

/-- Contribution of every signature not wholly contained in either horizontal layer. -/
noncomputable def nonhorizontalContribution
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ s : FacetSignature hp N L,
    if ¬ IsLowerHorizontal hp N L s ∧ ¬ IsUpperHorizontal hp N L s then
      signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s
    else 0

/-- A signature cannot lie in both horizontal layers when the facet has a vertex. -/
theorem not_lower_and_upper
    (hp : Nat.Prime p) (N L : Nat)
    (s : FacetSignature hp N L) :
    ¬ (IsLowerHorizontal hp N L s ∧ IsUpperHorizontal hp N L s) := by
  rintro ⟨hlow, hupp⟩
  let i : Fin p := ⟨0, hp.pos⟩
  have h0 := hlow i
  have h1 := hupp i
  linarith

/-- The signature sum splits into lower-horizontal, upper-horizontal, and nonhorizontal pieces. -/
theorem signature_sum_eq_horizontal_add_nonhorizontal
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) :
    (∑ s : FacetSignature hp N L,
      signatureBoundaryCoefficient hp N L s * signatureWeight hp N L a s) =
      lowerHorizontalContribution hp N L a +
        upperHorizontalContribution hp N L a +
          nonhorizontalContribution hp N L a := by
  classical
  unfold lowerHorizontalContribution upperHorizontalContribution nonhorizontalContribution
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hl : IsLowerHorizontal hp N L s
  · have hu : ¬ IsUpperHorizontal hp N L s := by
      intro hu
      exact not_lower_and_upper hp N L s ⟨hl, hu⟩
    simp [hl, hu]
  · by_cases hu : IsUpperHorizontal hp N L s
    · simp [hl, hu]
    · simp [hl, hu]

/-- The global local-boundary identity in horizontal/nonhorizontal form. -/
theorem horizontal_add_nonhorizontal_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      GeneralPosition hp (localVertexMap hp N L a q)) :
    lowerHorizontalContribution hp N L a +
      upperHorizontalContribution hp N L a +
        nonhorizontalContribution hp N L a = 0 := by
  rw [← signature_sum_eq_horizontal_add_nonhorizontal]
  exact signature_weighted_boundary_sum_eq_zero hp N L a hgp


/-- Horizontal/nonhorizontal decomposition specialized to a generic perturbation result. -/
theorem Result.horizontal_add_nonhorizontal_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : Result hp N L H m) :
    lowerHorizontalContribution hp N L R.assignment +
      upperHorizontalContribution hp N L R.assignment +
        nonhorizontalContribution hp N L R.assignment = 0 :=
  EquivariantPrismGlobalCancellation.horizontal_add_nonhorizontal_eq_zero
    hp N L R.assignment R.generalPosition

/-- Once internal and spatial-side signatures have been shown to cancel, the two horizontal
contributions are opposite.  This is the exact algebraic endpoint consumed by the refined
homotopy-invariance theorem. -/
theorem lowerHorizontalContribution_eq_neg_upper_of_nonhorizontal_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      GeneralPosition hp (localVertexMap hp N L a q))
    (hside : nonhorizontalContribution hp N L a = 0) :
    lowerHorizontalContribution hp N L a =
      -upperHorizontalContribution hp N L a := by
  have h := horizontal_add_nonhorizontal_eq_zero hp N L a hgp
  rw [hside, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Horizontal balance specialized to a generic perturbation result. -/
theorem Result.lowerHorizontalContribution_eq_neg_upper_of_nonhorizontal_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : Result hp N L H m)
    (hside : nonhorizontalContribution hp N L R.assignment = 0) :
    lowerHorizontalContribution hp N L R.assignment =
      -upperHorizontalContribution hp N L R.assignment := by
  have h := EquivariantPrismGlobalCancellation.horizontal_add_nonhorizontal_eq_zero
    hp N L R.assignment R.generalPosition
  rw [hside, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end EquivariantPrismGlobalCancellation
end FoxNeuwirthOrderComplex
end NRR
