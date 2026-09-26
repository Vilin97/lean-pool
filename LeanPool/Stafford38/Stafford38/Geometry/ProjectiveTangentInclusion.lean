/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.FormalDivisorLaurentConormal


/-!
# Projective tangent inclusion is enough for affine conormality

The projective dehomogenization bridge does not need equality between the
Zariski tangent space and the span of the supplied dehomogenized columns.
It is enough that the Zariski tangent space is contained in that span: a
covector annihilating the larger space then annihilates the smaller one.

This file propagates that weaker hypothesis through the existing formal
divisor and Laurent-direction consumers.  It constructs no projective chart,
normalization, tangent comparison, or conormal-closure theorem.
-/

@[expose] public section

namespace Stafford38.Geometry.ProjectiveTangentInclusion

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryRetractionSpecialization

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- A projective annihilating row gives an affine conormal covector whenever
the Zariski tangent space is contained in the dehomogenized column span.
Equality of the two tangent spaces is not required. -/
theorem coordinateCovector_mem_affineConormalSpace_of_zariski_le_span
    {κ : Type*}
    (I : Ideal (MvPolynomial (Fin n) K))
    (q ell : Fin (n + 1) → K) (B : Matrix (Fin (n + 1)) κ K)
    (hq0 : q 0 ≠ 0)
    (hq : ∑ i, ell i * q i = 0)
    (hB : rowMul ell B = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint q) I ≤
        dehomogenizedTangentSpan q B) :
    coordinateCovector (fun i ↦ ell i.succ) ∈
      affineConormalSpace (dehomogenizedPoint q) I := by
  rw [affineConormalSpace, Submodule.mem_dualAnnihilator]
  intro v hv
  have hann :=
    coordinateCovector_mem_dehomogenizedTangentSpan_dualAnnihilator
      q ell B hq0 hq hB
  rw [Submodule.mem_dualAnnihilator] at hann
  exact hann v (htangent hv)

/-- The weakened projective bridge reaches the equation-defined affine
conormal locus directly. -/
theorem phasePoint_mem_equationConormalLocus_of_zariski_le_span
    {κ : Type*}
    (I : Ideal (MvPolynomial (Fin n) K))
    (q ell : Fin (n + 1) → K) (B : Matrix (Fin (n + 1)) κ K)
    (hq0 : q 0 ≠ 0)
    (hq : ∑ i, ell i * q i = 0)
    (hB : rowMul ell B = 0)
    (hbase : ∀ f ∈ I, MvPolynomial.eval (dehomogenizedPoint q) f = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint q) I ≤
        dehomogenizedTangentSpan q B) :
    Sum.elim (dehomogenizedPoint q) (fun i ↦ ell i.succ) ∈
      equationConormalLocus I := by
  refine ⟨?_, ?_⟩
  · simpa using hbase
  · simpa using coordinateCovector_mem_affineConormalSpace_of_zariski_le_span
      I q ell B hq0 hq hB htangent

variable {k : Type*} [Field k]

/-- Formal row annihilation reaches the Laurent-valued equation-conormal
locus under tangent inclusion rather than tangent equality. -/
theorem laurentPhasePoint_mem_equationConormalLocus_of_zariski_le_span
    {κ : Type*} [Finite κ]
    (I : Ideal (MvPolynomial (Fin n) (LaurentSeries k)))
    (q ell : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (hq0 : q 0 ≠ 0)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0)
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q)) I ≤
        dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau)) :
    Sum.elim (dehomogenizedPoint (laurentColumn q))
        (fun i ↦ laurentColumn ell i.succ) ∈
      equationConormalLocus I := by
  classical
  let := Fintype.ofFinite κ
  exact phasePoint_mem_equationConormalLocus_of_zariski_le_span
    I (laurentColumn q) (laurentColumn ell)
      (laurentNonpositionTangentMatrix Z tau)
      (laurentColumn_ne_zero_of_ne_zero q hq0)
      (laurentColumn_dot_eq_zero_of_formalTangent_rowMul q ell Z tau hrow)
      (laurentNonposition_rowMul_eq_zero_of_formalTangent_rowMul
        q ell Z tau hrow)
      hbase htangent

/-- The weakened Laurent bridge retains the exact fibre-residue identity. -/
theorem laurentPhasePoint_mem_equationConormalLocus_and_residue_of_zariski_le_span
    {κ : Type*} [Finite κ]
    (I : Ideal (MvPolynomial (Fin n) (LaurentSeries k)))
    (q ell : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (hq0 : q 0 ≠ 0)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0)
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q)) I ≤
        dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau)) :
    Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ laurentColumn ell i.succ) ∈ equationConormalLocus I ∧
      residueColumn (fun i : Fin n ↦ ell i.succ) =
        fun i ↦ residueColumn ell i.succ := by
  classical
  let := Fintype.ofFinite κ
  exact ⟨laurentPhasePoint_mem_equationConormalLocus_of_zariski_le_span
    I q ell Z tau hq0 hrow hbase htangent, residueColumn_tail ell⟩

/-- The same inclusion hypothesis reaches the projected Laurent
equation-conormal direction closure required by the asymptotic consumer. -/
theorem residue_tail_mem_laurentEquationConormalDirectionClosure_of_zariski_le_span
    {κ : Type*} [Finite κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q ell : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (hq0 : q 0 ≠ 0)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0)
    (hbase : ∀ f ∈
        I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))) ≤
        dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau)) :
    residueColumn (fun i : Fin n ↦ ell i.succ) ∈
      laurentEquationConormalDirectionClosure I := by
  classical
  let := Fintype.ofFinite κ
  apply residue_mem_laurentEquationConormalDirectionClosure
    I (dehomogenizedPoint (laurentColumn q)) (fun i : Fin n ↦ ell i.succ)
  exact laurentPhasePoint_mem_equationConormalLocus_of_zariski_le_span
    (I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)))
    q ell Z tau hq0 hrow hbase htangent


end

end Stafford38.Geometry.ProjectiveTangentInclusion
