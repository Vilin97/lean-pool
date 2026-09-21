/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveConormalDehomogenization
import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection
import LeanPool.Stafford38.Stafford38.Geometry.SmoothAffineConormal
import LeanPool.Stafford38.Stafford38.Geometry.ConormalScalarExtensionVanishing
import LeanPool.Stafford38.Stafford38.Geometry.SmoothConormalFibreVanishing
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveConormalDirections
import LeanPool.Stafford38.Stafford38.Geometry.FormalDivisorLaurentConormal
import LeanPool.Stafford38.Stafford38.Geometry.GeneralTangentLatticePresentation
import LeanPool.Stafford38.Stafford38.Geometry.LocalizedProjectiveChartTransition

/-!
# The split-lattice tangent-limit calculation

This file records the tangent-limit criterion after the affine-chart and
tangent-lattice dictionaries have been made explicit.  It uses no
normalization theorem.  A
power-series matrix is the lattice of projective tangent columns.  A left
inverse is the direct-summand certificate.  The axis condition is imposed on
the reduced lattice, and the annihilator is constructed by the retraction
correction; it is not an input.

The Laurent-valued smooth equation-conormal direction hull is transported to
the ground-field projective closure by the existing scalar-extension and
smooth-fibre vanishing theorems.  `Input` is the internal split-matrix kernel.
The paper-facing `DirectSummandInput` instead takes the formal arc and the
actual complemented tangent lattice.  The theorem below constructs the
matrix presentation and proves the projective-closure and tangent-chart
dictionaries before applying that kernel.
-/

namespace Stafford38.Geometry.GeneralTangentLimitCriterion

open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.GeneralTangentLatticePresentation
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization

noncomputable section

variable {k : Type*} [Field k]

/-- The scalar-extended smooth equation-conormal phase locus used by the
Laurent specialization theorem.  The smoothness predicate is the genuine
`SmoothAffinePoint` predicate; it is not a dimension label or a placeholder.
-/
def smoothEquationConormalLocus {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (PhaseVar n → LaurentSeries k) :=
  {q | q ∈ equationConormalLocus
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n))) ∧
    SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (fun i ↦ q (Sum.inl i))}

/-! ## Coordinate-free statement of the paper hypotheses -/

/-- Coordinatewise extension of scalars on a finite coordinate module. -/
def extendColumn {R K : Type*} [CommSemiring R] [CommSemiring K]
    [Algebra R K] {ι : Type*} :
    (ι → R) →ₛₗ[algebraMap R K] (ι → K) where
  toFun v i := algebraMap R K (v i)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

/-- The ordinary scalar extension of a lattice, presented as the span of its
coordinatewise images.  This definition avoids choosing a basis. -/
def genericFibre {R K : Type*} [CommSemiring R] [CommSemiring K]
    [Algebra R K] {ι : Type*} (L : Submodule R (ι → R)) :
    Submodule K (ι → K) :=
  Submodule.span K (extendColumn (R := R) (K := K) '' (L : Set (ι → R)))

/-- The derivative of the zeroth affine chart at a homogeneous point. -/
def dehomogenizedTangentLinearMap {K : Type*} [Field K] {n : ℕ}
    (q : Fin (n + 1) → K) :
    (Fin (n + 1) → K) →ₗ[K] (Fin n → K) where
  toFun w := dehomogenizedTangentColumn q w
  map_add' x y := by
    ext i
    simp [dehomogenizedTangentColumn]
    ring
  map_smul' a x := by
    ext i
    simp [dehomogenizedTangentColumn]
    ring

/-- The affine cone over the embedded projective tangent plane in the chart
`q 0 ≠ 0`: it is the inverse image of the affine tangent space under the
chart derivative.  Its radial kernel contains `q`. -/
def projectiveTangentCone {K : Type*} [Field K] {n : ℕ}
    (q : Fin (n + 1) → K) (T : Submodule K (Fin n → K)) :
    Submodule K (Fin (n + 1) → K) :=
  T.comap (dehomogenizedTangentLinearMap q)

/-- Equation-level membership in the projective closure in the zeroth chart.
The equations are the standard homogenizations of every affine equation, so
this is the ordinary homogeneous-equation presentation of the closure. -/
def projectiveClosureAtZero {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (q : Fin (n + 1) → K) : Prop :=
  ∀ f ∈ I, MvPolynomial.eval q (homogenizeAtZero f) = 0

/-- In the nonzero zeroth chart, the homogeneous-equation presentation of the
projective closure is equivalent to membership in the original affine zero
locus. -/
theorem projectiveClosureAtZero_iff {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0) :
    projectiveClosureAtZero I q ↔
      dehomogenizedPoint q ∈ MvPolynomial.zeroLocus K I := by
  constructor
  · intro h f hf
    have heval := eval_projectiveDehomogenize_eq_zero_of_homogeneous
      (homogenizeAtZero f) f.totalDegree
      (homogenizeAtZero_isHomogeneous f) q hq0 (h f hf)
    simpa only [projectiveDehomogenize_homogenizeAtZero,
      MvPolynomial.aeval_eq_eval] using heval
  · intro h f hf
    have hnormalized :
        MvPolynomial.eval (normalizedProjectivePoint q (q 0))
          (homogenizeAtZero f) = 0 := by
      rw [normalizedProjectivePoint_eq_chartPoint q hq0,
        ← eval_projectiveDehomogenize,
        projectiveDehomogenize_homogenizeAtZero]
      exact h f hf
    rw [eval_eq_pow_mul_eval_normalizedProjectivePoint
      (homogenizeAtZero f) f.totalDegree
      (homogenizeAtZero_isHomogeneous f) q (q 0) hq0,
      hnormalized, mul_zero]

/-- A formal projective arc represented by power-series coordinates.  The
unit-coordinate condition makes the tuple a morphism to projective space;
the second field is membership in the homogeneous-equation closure after
passing to the generic Laurent point. -/
def FormalProjectiveArcInClosure {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k) : Prop :=
  (∃ i, IsUnit (q i)) ∧
    projectiveClosureAtZero
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (laurentColumn q)

/-- Exact chart dictionary for `FormalProjectiveArcInClosure`: its
homogeneous projective equations are equivalent to the affine equations at
the Laurent generic point, while the unit-coordinate condition records that
the tuple is a genuine formal projective arc. -/
theorem formalProjectiveArcInClosure_iff {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (hq0 : q 0 ≠ 0) :
    FormalProjectiveArcInClosure I q ↔
      (∃ i, IsUnit (q i)) ∧
        dehomogenizedPoint (laurentColumn q) ∈
          MvPolynomial.zeroLocus (LaurentSeries k)
            (I.map (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n))) := by
  rw [FormalProjectiveArcInClosure,
    projectiveClosureAtZero_iff]
  exact laurentColumn_ne_zero_of_ne_zero q hq0

/-- The columns of a matrix presentation span the generic fibre of the
original lattice after scalar extension. -/
private theorem genericFibre_eq_span_matrixColumns
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {ι κ : Type*} [Fintype κ]
    (L : Submodule R (ι → R)) (B : Matrix ι κ R)
    (hspan : Submodule.span R (Set.range fun j => fun i => B i j) = L) :
    genericFibre (K := K) L =
      Submodule.span K (Set.range fun j => fun i =>
        algebraMap R K (B i j)) := by
  let f := extendColumn (R := R) (K := K) (ι := ι)
  let columns : κ → (ι → R) := fun j i => B i j
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    have hxspan : x ∈ Submodule.span R (Set.range columns) := by
      rw [hspan]
      exact hx
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun R).mp hxspan
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun j => algebraMap R K (c j), ?_⟩
    apply funext
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hi : (∑ j, c j * B i j) = x i := by
      simpa only [columns, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] using congrFun hc i
    change _ = algebraMap R K (x i)
    simpa only [map_sum, map_mul] using congrArg (algebraMap R K) hi
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Submodule.subset_span
    refine ⟨columns j, ?_, rfl⟩
    rw [← hspan]
    exact Submodule.subset_span ⟨j, rfl⟩

/-- The chart derivative is onto whenever the chart denominator is nonzero. -/
private theorem dehomogenizedTangentLinearMap_surjective
    {K : Type*} [Field K] {n : ℕ}
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0) :
    Function.Surjective (dehomogenizedTangentLinearMap q) := by
  intro v
  refine ⟨Fin.cases 0 (fun i => v i * q 0), ?_⟩
  ext i
  change (v i * q 0 * q 0 - q i.succ * 0) / q 0 ^ 2 = v i
  field_simp
  ring

/-- If the scalar-extended lattice is the projective tangent cone, any matrix
whose columns span that lattice contains the projective point and its chart
derivatives span exactly the affine tangent space.  This is the dictionary
formerly exposed as the separate `hposition` and `htangent` inputs. -/
private theorem matrix_tangent_dictionary
    {K : Type*} [Field K] {n : ℕ} {κ : Type*} [Fintype κ]
    (q : Fin (n + 1) → K) (hq0 : q 0 ≠ 0)
    (T : Submodule K (Fin n → K))
    (B : Matrix (Fin (n + 1)) κ K)
    (hspan : Submodule.span K
      (Set.range fun j => fun i => B i j) = projectiveTangentCone q T) :
    (∃ c : κ → K, ∀ i, q i = ∑ j, B i j * c j) ∧
      dehomogenizedTangentSpan q B = T := by
  have hqcone : q ∈ projectiveTangentCone q T := by
    change dehomogenizedTangentColumn q q ∈ T
    convert T.zero_mem using 1
    ext i
    simp [dehomogenizedTangentColumn]
  have hqspan : q ∈ Submodule.span K
      (Set.range fun j => fun i => B i j) := by
    rw [hspan]
    exact hqcone
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hqspan
  refine ⟨⟨c, fun i => ?_⟩, ?_⟩
  · have hi := congrFun hc.symm i
    simpa [Finset.sum_apply, smul_eq_mul, mul_comm] using hi
  let d := dehomogenizedTangentLinearMap q
  calc
    dehomogenizedTangentSpan q B =
        (Submodule.span K (Set.range fun j => fun i => B i j)).map d := by
          rw [dehomogenizedTangentSpan, Submodule.map_span]
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_range]
          constructor
          · rintro ⟨j, rfl⟩
            exact ⟨fun i => B i j, ⟨j, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
            exact ⟨j, rfl⟩
    _ = (projectiveTangentCone q T).map d := by rw [hspan]
    _ = T := by
      exact Submodule.map_comap_eq_of_surjective
        (dehomogenizedTangentLinearMap_surjective q hq0) T

/-- The data appearing in the paper's tangent-limit hypothesis, expressed in
the affine chart of the projective arc.  `hposition` says that the generic
projective point belongs to the cone spanned by the generic tangent lattice;
the tangent-space equality is the exact smooth affine tangent dictionary.
The cardinality equation records the advertised rank `dimY + 1`.
-/
structure Input {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k)) where
  axis : Fin n
  C : Matrix κ (Fin (n + 1)) (PowerSeries k)
  hprime : I.IsPrime
  hsplit : C * B = 1
  hrank : Fintype.card κ = dimY + 1
  hq0 : q 0 ≠ 0
  hbase : ∀ f ∈ I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q))
  hposition : ∃ c : κ → LaurentSeries k, ∀ i,
      laurentColumn q i = ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (B i j) * c j
  htangent : dehomogenizedTangentSpan (laurentColumn q)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) =
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)))
  haxis : ∀ j, PowerSeries.constantCoeff (B axis.succ j) = 0

/-- The hypotheses of the paper's tangent-limit lemma, with the tangent
lattice supplied as an actual direct summand rather than chosen matrices.
`hgenericTangentCone` is literally the assertion that its Laurent generic
fibre is the affine cone over the embedded projective tangent plane, using
`projectiveTangentCone` above. -/
structure DirectSummandInput {n dimY : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k)) where
  axis : Fin n
  isComplemented : IsComplemented L
  rank_eq : Module.finrank (PowerSeries k) L = dimY + 1
  hprime : I.IsPrime
  chart_nonzero : q 0 ≠ 0
  arc_mem_closure : FormalProjectiveArcInClosure I q
  generic_smooth : SmoothAffinePoint
    (I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)))
    (dehomogenizedPoint (laurentColumn q))
  hgenericTangentCone :
    genericFibre (K := LaurentSeries k) L =
      projectiveTangentCone (laurentColumn q)
        (zariskiTangentSpace
          (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))))
  residue_le_coordinateHyperplane : ∀ v : L,
    PowerSeries.constantCoeff ((v : Fin (n + 1) → PowerSeries k) axis.succ) = 0

private theorem rowMul_zero_of_leftInverse_axis
    {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (C : Matrix κ (Fin (n + 1)) (PowerSeries k))
    (axis : Fin (n + 1))
    (hCB : C * B = 1)
    (haxis : ∀ j, PowerSeries.constantCoeff (B axis j) = 0) :
    ∃ ell : Fin (n + 1) → PowerSeries k,
      rowMul ell B = 0 ∧
        residueColumn ell = axisRow (k := k) axis := by
  let a₀ : Fin (n + 1) → k := axisRow (k := k) axis
  let a : Fin (n + 1) → PowerSeries k := constantColumn a₀
  have hres : residueColumn a = a₀ := by
    exact residueColumn_constantColumn a₀
  have hred : rowMul a₀
      (fun i j ↦ PowerSeries.constantCoeff (B i j)) = 0 := by
    funext j
    simp [a₀, axisRow, rowMul, haxis j]
  let ell : Fin (n + 1) → PowerSeries k := annihilatorLift a B C
  have hell := powerSeries_annihilatorLift_spec a a₀ B C hCB hres hred
  refine ⟨ell, ?_, ?_⟩
  · exact hell.1
  · simpa [ell, a₀] using hell.2

private theorem rowMul_laurent_of_rowMul
    {n : ℕ} {κ : Type*} [Fintype κ]
    (ell : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (h : rowMul ell B = 0) :
    rowMul (laurentColumn ell)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) = 0 := by
  funext j
  have hj := congrFun h j
  simpa [rowMul, laurentColumn, map_sum] using
    congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hj

theorem exists_axis_laurent_smooth_conormal_direction
    {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k))
    (D : Input (dimY := dimY) I q B) :
    ∃ ell : Fin (n + 1) → PowerSeries k,
      rowMul ell B = 0 ∧
      residueColumn ell = axisRow (k := k) D.axis.succ ∧
      (let phase : PhaseVar n → LaurentSeries k :=
        Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ));
       phase ∈ smoothEquationConormalLocus I ∧
       residueColumn (fun i : Fin n ↦ ell i.succ) ∈
         extensionFibreClosure (k := k) (K := LaurentSeries k)
           (smoothEquationConormalLocus I) ∧
       Projectivization.mk k
           (fun i : Fin n => if i = D.axis then (1 : k) else 0)
           (by intro h; have hh := congrFun h D.axis; simpa using hh) ∈
         projectiveHomogeneousClosure
           (projectivizedDirectionSet (smoothConormalDirectionSet I))) := by
  obtain ⟨ell, hrow, hres⟩ := rowMul_zero_of_leftInverse_axis
    B D.C D.axis.succ D.hsplit D.haxis
  have hrowL := rowMul_laurent_of_rowMul ell B hrow
  have hqL : ∑ i, laurentColumn ell i * laurentColumn q i = 0 := by
    obtain ⟨c, hc⟩ := D.hposition
    have hprod : ∑ i, laurentColumn ell i * laurentColumn q i =
        ∑ j, (∑ i, laurentColumn ell i *
          algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) * c j := by
      calc
        ∑ i, laurentColumn ell i * laurentColumn q i =
            ∑ i, laurentColumn ell i *
              (∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
                (B i j) * c j) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hc i]
        _ = ∑ i, ∑ j, laurentColumn ell i *
              (algebraMap (PowerSeries k) (LaurentSeries k) (B i j) * c j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, laurentColumn ell i *
              (algebraMap (PowerSeries k) (LaurentSeries k) (B i j) * c j) :=
                Finset.sum_comm
        _ = ∑ j, (∑ i, laurentColumn ell i *
              algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) * c j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                ring
    rw [hprod]
    have hzero : ∀ j, (∑ i, laurentColumn ell i *
          algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) = 0 := by
      intro j
      exact congrFun hrowL j
    change (∑ j, rowMul (laurentColumn ell)
      (fun i l ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i l)) j * c j) = 0
    rw [hrowL]
    simp
  have hphase :
      Sum.elim (dehomogenizedPoint (laurentColumn q))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin n))) := by
    exact phasePoint_mem_equationConormalLocus_of_projective_row
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (laurentColumn q) (laurentColumn ell)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j))
      (laurentColumn_ne_zero_of_ne_zero q D.hq0)
      hqL hrowL D.hbase D.htangent
  let phase : PhaseVar n → LaurentSeries k :=
    Sum.elim (dehomogenizedPoint (laurentColumn q))
      (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (ell i.succ))
  have hphaseSmooth : phase ∈ smoothEquationConormalLocus I := by
    exact ⟨hphase, D.hsmooth⟩
  have hclosure := residue_mem_extensionFibreClosure_of_laurent_generic
    (S := smoothEquationConormalLocus I)
    (dehomogenizedPoint (laurentColumn q))
    (fun i : Fin n ↦ ell i.succ) hphaseSmooth
  let axisVec : Fin n → k := fun i => if i = D.axis then 1 else 0
  have hresTail : residueColumn (fun i : Fin n ↦ ell i.succ) = axisVec := by
    funext i
    have hi := congrFun hres i.succ
    simpa [residueColumn, axisRow, axisVec] using hi
  have hvanAxis : axisVec ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I)) := by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro P hP
    have hf : fibreLift P ∈
        MvPolynomial.vanishingIdeal k (equationConormalLocus I) :=
      fibreLift_mem_vanishingIdeal_equationConormal I D.hprime P hP
    have hPext : P ∈ extensionValuedVanishingIdeal
        (k := k) (K := LaurentSeries k)
        (fibreImage (smoothEquationConormalLocus I)) := by
      rw [mem_extensionValuedVanishingIdeal_iff]
      intro v hv
      rcases hv with ⟨z, hz, rfl⟩
      have hs := scalarExtension_vanishing I (fibreLift P) (by
        simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using hf)
        z hz.1
      have hsplit :
          Sum.elim (fun i ↦ z (Sum.inl i)) (fun i ↦ z (Sum.inr i)) = z := by
        funext i
        rcases i with i | i <;> rfl
      rw [← hsplit] at hs
      simpa [eval₂_fibreLift] using hs
    have hz := hclosure P hPext
    rw [hresTail] at hz
    simpa [MvPolynomial.aeval_eq_eval] using hz
  have hproj := mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus
    I axisVec (by
      intro h
      have hh := congrFun h D.axis
      simpa [axisVec] using hh) hvanAxis
  exact ⟨ell, hrow, hres, ⟨hphaseSmooth, hclosure, by simpa [axisVec] using hproj⟩⟩

/-- Paper-level tangent-limit criterion.  Starting from an actual rank
`dimY + 1` direct-summand lattice whose generic fibre is the projective
tangent cone, this theorem constructs split matrix coordinates internally and
applies `exists_axis_laurent_smooth_conormal_direction`.  No annihilator,
matrix retraction, position coefficients, or chart tangent dictionary occurs
in the input. -/
theorem tangent_limit_criterion_of_directSummand
    {n dimY : ℕ} [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (L : Submodule (PowerSeries k)
      (Fin (n + 1) → PowerSeries k))
    (D : DirectSummandInput (dimY := dimY) I q L) :
    Projectivization.mk k
        (fun i : Fin n => if i = D.axis then (1 : k) else 0)
        (by intro h; have hh := congrFun h D.axis; simpa using hh) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I)) := by
  obtain ⟨P⟩ := exists_splitMatrixPresentation_of_isComplemented
    L D.isComplemented (dimY + 1) D.rank_eq
  let B : Matrix (Fin (n + 1)) (Fin (dimY + 1))
      (PowerSeries k) := P.B
  let BL : Matrix (Fin (n + 1)) (Fin (dimY + 1))
      (LaurentSeries k) :=
    fun i j => algebraMap (PowerSeries k) (LaurentSeries k) (B i j)
  have hgenericSpan :
      Submodule.span (LaurentSeries k)
          (Set.range fun j => fun i => BL i j) =
        projectiveTangentCone (laurentColumn q)
          (zariskiTangentSpace
            (dehomogenizedPoint (laurentColumn q))
            (I.map (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n)))) := by
    rw [← D.hgenericTangentCone,
      genericFibre_eq_span_matrixColumns L B P.columnsSpan]
  have hq0L : laurentColumn q 0 ≠ 0 :=
    laurentColumn_ne_zero_of_ne_zero q D.chart_nonzero
  obtain ⟨hposition, htangent⟩ := matrix_tangent_dictionary
    (laurentColumn q) hq0L
    (zariskiTangentSpace
      (dehomogenizedPoint (laurentColumn q))
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n))))
    BL hgenericSpan
  have hbase : ∀ f ∈ I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0 := by
    have hz := (projectiveClosureAtZero_iff
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (laurentColumn q) hq0L).mp D.arc_mem_closure.2
    exact hz
  have haxis : ∀ j,
      PowerSeries.constantCoeff (B D.axis.succ j) = 0 := by
    intro j
    have hmem : (fun i => B i j) ∈ L := by
      rw [← P.columnsSpan]
      exact Submodule.subset_span ⟨j, rfl⟩
    let v : L := ⟨fun i => B i j, hmem⟩
    simpa [v] using D.residue_le_coordinateHyperplane v
  let low : Input (dimY := dimY) I q B := {
    axis := D.axis
    C := P.C
    hprime := D.hprime
    hsplit := P.leftInverse
    hrank := by simp
    hq0 := D.chart_nonzero
    hbase := hbase
    hsmooth := D.generic_smooth
    hposition := hposition
    htangent := htangent
    haxis := haxis }
  obtain ⟨ell, hrow, hres, hconormal⟩ :=
    exists_axis_laurent_smooth_conormal_direction I q B low
  exact hconormal.2.2


end
end Stafford38.Geometry.GeneralTangentLimitCriterion
