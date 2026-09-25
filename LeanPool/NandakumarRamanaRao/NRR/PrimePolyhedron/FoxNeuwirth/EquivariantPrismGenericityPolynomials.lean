/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismVertexParameters
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffinePositiveRayBoundary
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Genericity polynomials for the equivariant refined prism

The global parameter type from `EquivariantPrismVertexParameters` already enforces shared-vertex
compatibility and prime equivariance.  This file records the two algebraic degeneracy families used
by the refined prism perturbation.

* For every refined prism simplex and every one of its facets, the facet polynomial is the
  determinant of the augmented deviation matrix.  Its nonvanishing is exactly facet regularity.
* For every refined prism simplex and every ordered codimension-two face, the minor polynomial is
  the determinant of the deviation vectors at the remaining vertices.  Its nonvanishing rules out
  a deviation zero on that codimension-two face.

Both constructions are literal multivariate polynomials over the finite orbit parameter type.
Evaluation lemmas identify them with the corresponding real matrices reconstructed from an
assignment.  A final sum type packages the two finite families for direct use with
`FiniteMultivariateGenericPerturbation.exists_small_positive_generic`.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open MvPolynomial

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismGenericityPolynomials

open EquivariantPrismVertexParameters
open SubdivisionPrismCharts
open AffinePositiveRayBoundary

variable {p : Nat}

/-- The multivariate-polynomial ring attached to the finite equivariant prism parameter space. -/
abbrev PolynomialRing (hp : Nat.Prime p) (N L : Nat) :=
  MvPolynomial (Parameter hp N L) Real

/-- The coordinate variable attached to a sampled global vertex and a coordinate label. -/
noncomputable def scalarPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (x : GlobalVertex hp N L) (j : Fin p) : PolynomialRing hp N L :=
  X (Quotient.mk _ (x, j))

/-- The polynomial coordinate vector at a sampled global vertex. -/
noncomputable def vectorPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (x : GlobalVertex hp N L) : Fin p → PolynomialRing hp N L :=
  fun j => scalarPolynomial hp N L x j

/-- The polynomial coordinate vector at one local refined-prism vertex occurrence. -/
noncomputable def localVertexPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (i : Fin (p + 1)) :
    Fin p → PolynomialRing hp N L :=
  vectorPolynomial hp N L (sampleVertex hp N L (q, i))

/-- Fixed difference coordinate in the polynomial ring. -/
noncomputable def deviationPolynomial
    (hp : Nat.Prime p) {N L : Nat}
    (y : Fin p → PolynomialRing hp N L) (r : Fin (p - 1)) :
    PolynomialRing hp N L :=
  y (ReferenceAffineOrbitCount.coordinateLabel hp r) -
    y (ReferenceAffineOrbitCount.lastLabel hp)

/-- The real vertex map reconstructed on one refined prism simplex. -/
noncomputable def localVertexMap
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) :
    AffinePositiveRayBoundary.VertexMap p where
  value i := localVertexValue hp N L a q i

/-- Evaluation at a parameter assignment, bundled as a ring homomorphism. -/
noncomputable def assignmentEvalHom
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    PolynomialRing hp N L →+* Real :=
  MvPolynomial.eval₂Hom (RingHom.id Real) a

@[simp] theorem assignmentEvalHom_apply
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (P : PolynomialRing hp N L) :
    assignmentEvalHom hp N L a P = MvPolynomial.eval a P := rfl

@[simp] theorem eval_scalarPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (x : GlobalVertex hp N L) (j : Fin p) :
    MvPolynomial.eval a (scalarPolynomial hp N L x j) =
      scalarValue hp N L a x j := by
  simp [scalarPolynomial, scalarValue]

@[simp] theorem eval_vectorPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (x : GlobalVertex hp N L) (j : Fin p) :
    MvPolynomial.eval a (vectorPolynomial hp N L x j) =
      vectorValue hp N L a x j := by
  simp [vectorPolynomial, vectorValue]

@[simp] theorem eval_localVertexPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L)
    (i : Fin (p + 1)) (j : Fin p) :
    MvPolynomial.eval a (localVertexPolynomial hp N L q i j) =
      localVertexValue hp N L a q i j := by
  simp [localVertexPolynomial, localVertexValue]

@[simp] theorem eval_deviationPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (y : Fin p → PolynomialRing hp N L) (r : Fin (p - 1)) :
    MvPolynomial.eval a (deviationPolynomial hp y r) =
      AffinePositiveRayBoundary.VertexMap.deviation hp
        (fun j => MvPolynomial.eval a (y j)) r := by
  simp [deviationPolynomial, AffinePositiveRayBoundary.VertexMap.deviation]

/-- The polynomial augmented deviation matrix on the facet omitting vertex `k`. -/
noncomputable def facetMatrixPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (k : Fin (p + 1)) :
    Matrix (Fin p) (Fin p) (PolynomialRing hp N L) :=
  fun r i => Fin.lastCases (C (1 : Real))
    (fun s => deviationPolynomial hp
      (localVertexPolynomial hp N L q (k.succAbove i)) s)
    (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r)

/-- The facet determinant polynomial for one local refined-prism simplex. -/
noncomputable def facetDeterminantPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (k : Fin (p + 1)) :
    PolynomialRing hp N L :=
  Matrix.det (facetMatrixPolynomial hp N L q k)

/-- Evaluation of the polynomial facet matrix is the real facet matrix of the reconstructed local
vertex map. -/
theorem map_facetMatrixPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (k : Fin (p + 1)) :
    (assignmentEvalHom hp N L a).mapMatrix
        (facetMatrixPolynomial hp N L q k) =
      AffinePositiveRayBoundary.VertexMap.facetMatrix hp
        (localVertexMap hp N L a q) k := by
  ext r i
  change MvPolynomial.eval a
      (Fin.lastCases (C (1 : Real))
        (fun s => deviationPolynomial hp
          (localVertexPolynomial hp N L q (k.succAbove i)) s)
        (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r)) =
    Fin.lastCases 1
      (fun s => AffinePositiveRayBoundary.VertexMap.deviation hp
        (localVertexValue hp N L a q (k.succAbove i)) s)
      (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r)
  generalize AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r = r'
  refine Fin.lastCases ?_ (fun s => ?_) r'
  · simp
  · simp

/-- The facet determinant polynomial evaluates to the actual local facet determinant. -/
theorem eval_facetDeterminantPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (k : Fin (p + 1)) :
    MvPolynomial.eval a (facetDeterminantPolynomial hp N L q k) =
      AffinePositiveRayBoundary.VertexMap.facetDeterminant hp
        (localVertexMap hp N L a q) k := by
  change assignmentEvalHom hp N L a
      (Matrix.det (facetMatrixPolynomial hp N L q k)) = _
  rw [RingHom.map_det]
  rw [map_facetMatrixPolynomial]
  rfl

/-- An ordered codimension-two face is encoded by first omitting one vertex and then omitting one
vertex of the resulting facet.  This representation is finite and avoids choosing an ordering on
unordered pairs. -/
abbrev CodimTwoFace (p : Nat) := Fin (p + 1) × Fin p

instance codimTwoFaceFintype (p : Nat) : Fintype (CodimTwoFace p) := inferInstance
instance codimTwoFaceDecidableEq (p : Nat) : DecidableEq (CodimTwoFace p) := inferInstance

/-- The second omission index, cast to the syntactic successor form needed by `Fin.succAbove`. -/
def secondOmissionIndex
    (hp : Nat.Prime p) (f : CodimTwoFace p) : Fin ((p - 1) + 1) :=
  Fin.cast (by have := hp.pos; omega) f.2

/-- The vertex retained in an ordered codimension-two face after the two omissions. -/
def codimTwoVertex
    (hp : Nat.Prime p) (f : CodimTwoFace p) (i : Fin (p - 1)) : Fin (p + 1) :=
  f.1.succAbove
    (Fin.cast (by have := hp.pos; omega) ((secondOmissionIndex hp f).succAbove i))

@[simp] theorem codimTwoVertex_ne_first
    (hp : Nat.Prime p) (f : CodimTwoFace p) (i : Fin (p - 1)) :
    codimTwoVertex hp f i ≠ f.1 := by
  simp [codimTwoVertex]

/-- The polynomial deviation matrix on the vertices of an ordered codimension-two face.  Rows are
fixed deviation coordinates and columns are the `p-1` retained vertices. -/
noncomputable def codimTwoDeviationMatrixPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (f : CodimTwoFace p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) (PolynomialRing hp N L) :=
  fun r i => deviationPolynomial hp
    (localVertexPolynomial hp N L q (codimTwoVertex hp f i)) r

/-- The codimension-two deviation-minor polynomial. -/
noncomputable def codimTwoMinorPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (f : CodimTwoFace p) :
    PolynomialRing hp N L :=
  Matrix.det (codimTwoDeviationMatrixPolynomial hp N L q f)

/-- The corresponding real deviation matrix reconstructed from an assignment. -/
noncomputable def codimTwoDeviationMatrix
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (f : CodimTwoFace p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) Real :=
  fun r i => AffinePositiveRayBoundary.VertexMap.deviation hp
    (localVertexValue hp N L a q (codimTwoVertex hp f i)) r

/-- Evaluation of the polynomial codimension-two matrix gives the corresponding real matrix. -/
theorem map_codimTwoDeviationMatrixPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (f : CodimTwoFace p) :
    (assignmentEvalHom hp N L a).mapMatrix
        (codimTwoDeviationMatrixPolynomial hp N L q f) =
      codimTwoDeviationMatrix hp N L a q f := by
  ext r i
  simp [codimTwoDeviationMatrixPolynomial, codimTwoDeviationMatrix]

/-- The codimension-two minor polynomial evaluates to the corresponding real determinant. -/
theorem eval_codimTwoMinorPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (f : CodimTwoFace p) :
    MvPolynomial.eval a (codimTwoMinorPolynomial hp N L q f) =
      Matrix.det (codimTwoDeviationMatrix hp N L a q f) := by
  change assignmentEvalHom hp N L a
      (Matrix.det (codimTwoDeviationMatrixPolynomial hp N L q f)) = _
  rw [RingHom.map_det]
  rw [map_codimTwoDeviationMatrixPolynomial]

/-- Finite indices for all facet-determinant and codimension-two-minor degeneracies. -/
abbrev GenericityIndex (hp : Nat.Prime p) (N L : Nat) :=
  (PrismCell hp N L × Fin (p + 1)) ⊕
    (PrismCell hp N L × CodimTwoFace p)

noncomputable instance genericityIndexFintype
    (hp : Nat.Prime p) (N L : Nat) : Fintype (GenericityIndex hp N L) := inferInstance

noncomputable instance genericityIndexDecidableEq
    (hp : Nat.Prime p) (N L : Nat) : DecidableEq (GenericityIndex hp N L) := inferInstance

/-- The combined finite polynomial family used by the generic perturbation theorem. -/
noncomputable def genericityPolynomial
    (hp : Nat.Prime p) (N L : Nat) :
    GenericityIndex hp N L → PolynomialRing hp N L
  | Sum.inl qk => facetDeterminantPolynomial hp N L qk.1 qk.2
  | Sum.inr qf => codimTwoMinorPolynomial hp N L qf.1 qf.2

/-- Evaluation of the combined family, split into its two geometric meanings. -/
theorem eval_genericityPolynomial
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (i : GenericityIndex hp N L) :
    MvPolynomial.eval a (genericityPolynomial hp N L i) =
      match i with
      | Sum.inl qk =>
          AffinePositiveRayBoundary.VertexMap.facetDeterminant hp
            (localVertexMap hp N L a qk.1) qk.2
      | Sum.inr qf => Matrix.det (codimTwoDeviationMatrix hp N L a qf.1 qf.2) := by
  cases i with
  | inl qk => exact eval_facetDeterminantPolynomial hp N L a qk.1 qk.2
  | inr qf => exact eval_codimTwoMinorPolynomial hp N L a qf.1 qf.2

end EquivariantPrismGenericityPolynomials
end FoxNeuwirthOrderComplex
end NRR
