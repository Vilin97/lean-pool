/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.FormalDivisorAxisLift
public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveConormalDehomogenization
public import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection


/-!
# From a formal divisor tangent to a Laurent conormal point

This file is the local algebraic bridge between the formal-divisor tangent
construction and Laurent conormal specialization.  Projective coordinates,
an annihilating row, and the divisor and normalized-transverse tangent columns
are embedded from power series into Laurent series.  The position column of
the formal tangent matrix supplies the projective Euler relation; its other
columns supply the projective tangent annihilation relation.  The existing
dehomogenization theorem then gives an equation-conormal point once the base
equations and the exact affine tangent-space equality are supplied.

No normalization or divisor chart is constructed here.  In particular this
file makes no global closure, coisotropy, or Gabber claim.
-/

@[expose] public section

namespace Stafford38.Geometry.FormalDivisorLaurentConormal

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryRetractionSpecialization

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Coefficientwise embedding of a power-series projective column into
Laurent series. -/
def laurentColumn (v : Fin (n + 1) → PowerSeries k) :
    Fin (n + 1) → LaurentSeries k :=
  fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (v i)

/-- The divisor and normalized-transverse columns of the formal tangent
matrix, embedded in Laurent series.  The position column is deliberately
omitted: it is used separately as the projective-point Euler relation. -/
def laurentNonpositionTangentMatrix {κ : Type*}
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k) :
    Matrix (Fin (n + 1)) (κ ⊕ Unit) (LaurentSeries k)
  | i, Sum.inl j =>
      algebraMap (PowerSeries k) (LaurentSeries k) (Z i j)
  | i, Sum.inr _ =>
      algebraMap (PowerSeries k) (LaurentSeries k) (tau i)

/-- The position component of an exact formal tangent annihilation becomes
the projective point-annihilation relation over Laurent series. -/
theorem laurentColumn_dot_eq_zero_of_formalTangent_rowMul
    {κ : Type*}
    (q ell : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0) :
    ∑ i, laurentColumn ell i * laurentColumn q i = 0 := by
  have hposition := congrFun hrow (Sum.inl ())
  simp only [Pi.zero_apply, rowMul, formalTangentMatrix] at hposition
  simpa [laurentColumn, map_sum] using
    congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hposition

/-- The non-position components of an exact formal tangent annihilation
become annihilation of all embedded divisor and normalized-transverse
columns. -/
theorem laurentNonposition_rowMul_eq_zero_of_formalTangent_rowMul
    {κ : Type*}
    (q ell : Fin (n + 1) → PowerSeries k)
    (Z : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (tau : Fin (n + 1) → PowerSeries k)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0) :
    rowMul (laurentColumn ell) (laurentNonpositionTangentMatrix Z tau) = 0 := by
  funext column
  rcases column with j | _
  · have hj := congrFun hrow (Sum.inr (Sum.inl j))
    simp only [Pi.zero_apply, rowMul, formalTangentMatrix] at hj
    simpa [rowMul, laurentColumn, laurentNonpositionTangentMatrix, map_sum] using
      congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hj
  · have htau := congrFun hrow (Sum.inr (Sum.inr ()))
    simp only [Pi.zero_apply, rowMul, formalTangentMatrix] at htau
    simpa [rowMul, laurentColumn, laurentNonpositionTangentMatrix, map_sum] using
      congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) htau

/-- The power-series embedding in Laurent series is nonzero on every nonzero
power series. -/
theorem laurentColumn_ne_zero_of_ne_zero
    (q : Fin (n + 1) → PowerSeries k) (hq0 : q 0 ≠ 0) :
    laurentColumn q 0 ≠ 0 := by
  intro hzero
  apply hq0
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  simpa [laurentColumn] using hzero

/-- The complete conditional local bridge.  Exact formal row annihilation
supplies both projective relations.  Given the base equations and the exact
dehomogenized tangent-space equality, the resulting Laurent phase point lies
in the equation-defined conormal locus. -/
theorem laurentPhasePoint_mem_equationConormalLocus
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
      dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau) =
        zariskiTangentSpace (dehomogenizedPoint (laurentColumn q)) I) :
    Sum.elim (dehomogenizedPoint (laurentColumn q))
        (fun i ↦ laurentColumn ell i.succ) ∈
      equationConormalLocus I := by
  classical
  let := Fintype.ofFinite κ
  exact phasePoint_mem_equationConormalLocus_of_projective_row
    I (laurentColumn q) (laurentColumn ell)
      (laurentNonpositionTangentMatrix Z tau)
      (laurentColumn_ne_zero_of_ne_zero q hq0)
      (laurentColumn_dot_eq_zero_of_formalTangent_rowMul q ell Z tau hrow)
      (laurentNonposition_rowMul_eq_zero_of_formalTangent_rowMul
        q ell Z tau hrow)
      hbase htangent

/-- The residue of the affine covector is exactly the tail of the residue of
the formal projective annihilating row.  This is the fibre-residue equality
consumed by `LaurentConormalDirection`. -/
theorem residueColumn_tail
    (ell : Fin (n + 1) → PowerSeries k) :
    residueColumn (fun i : Fin n ↦ ell i.succ) =
      fun i ↦ residueColumn ell i.succ := by
  rfl

/-- Package the conormal membership together with the exact residue relation
for its regular fibre coordinates. -/
theorem laurentPhasePoint_mem_equationConormalLocus_and_residue
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
      dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau) =
        zariskiTangentSpace (dehomogenizedPoint (laurentColumn q)) I) :
    Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ)) ∈
        equationConormalLocus I ∧
      residueColumn (fun i : Fin n ↦ ell i.succ) =
        fun i ↦ residueColumn ell i.succ := by
  classical
  let := Fintype.ofFinite κ
  exact ⟨laurentPhasePoint_mem_equationConormalLocus
    I q ell Z tau hq0 hrow hbase htangent, residueColumn_tail ell⟩

/-- Direct handoff to `LaurentConormalDirection` for a scalar-extended base
ideal.  The possibly singular dehomogenized position is retained over Laurent
series, while the regular fibre is the power-series tail of `ell`. -/
theorem residue_tail_mem_laurentEquationConormalDirectionClosure
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
      dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau) =
        zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n)))) :
    residueColumn (fun i : Fin n ↦ ell i.succ) ∈
      laurentEquationConormalDirectionClosure I := by
  classical
  let := Fintype.ofFinite κ
  apply residue_mem_laurentEquationConormalDirectionClosure
    I (dehomogenizedPoint (laurentColumn q)) (fun i : Fin n ↦ ell i.succ)
  exact laurentPhasePoint_mem_equationConormalLocus
    (I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)))
    q ell Z tau hq0 hrow hbase htangent


end

end Stafford38.Geometry.FormalDivisorLaurentConormal
