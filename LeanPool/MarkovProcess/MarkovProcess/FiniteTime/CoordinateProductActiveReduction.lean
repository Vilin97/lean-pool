/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinateProductNormalization


/-!
# Restricting normalized coordinate products to active coordinates

This file enumerates the active coordinates of a normalized `CoordinateProductTerm`, extracts
their genuine `C₀` factors, and proves that evaluation factors through the corresponding
coordinate restriction.  The restricting function is definitionally the same path operation as
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding factors)` when that finite-time API is in
scope.

If there are no active coordinates, the reduced index type is `Fin 0` and the empty scalar
product is one.  No constant-one element of `C₀` is constructed.  This is purely algebraic
finite-product infrastructure: it involves no measure and no kernel.
-/

@[expose] public section

open scoped CompactlySupported ZeroAtInfty BigOperators

namespace MarkovProcess.PiContinuousMap

variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

/-- The increasing enumeration of the coordinates carrying normalized factors. -/
def activeOrderEmbedding (factors : List (Fin n × C₀(alpha, ℝ))) :
    Fin (activeCoordinates factors).card ↪o Fin n :=
  (activeCoordinates factors).orderEmbOfFin rfl

/-- The genuine `C₀` factor at an active coordinate, indexed in increasing order. -/
def activeNormalizedFactor (factors : List (Fin n × C₀(alpha, ℝ)))
    (j : Fin (activeCoordinates factors).card) : C₀(alpha, ℝ) :=
  (normalizedCoordinateFactors factors (activeOrderEmbedding factors j)).get (by
    apply (mem_activeCoordinates_iff factors _).mp
    exact Finset.orderEmbOfFin_mem (activeCoordinates factors) rfl j)

private theorem eval_activeNormalizedFactor
    (factors : List (Fin n × C₀(alpha, ℝ)))
    (j : Fin (activeCoordinates factors).card) (x : alpha) :
    evalOptionalFactor x
        (normalizedCoordinateFactors factors (activeOrderEmbedding factors j)) =
      activeNormalizedFactor factors j x := by
  have hj : (normalizedCoordinateFactors factors
      (activeOrderEmbedding factors j)).isSome := by
    apply (mem_activeCoordinates_iff factors _).mp
    exact Finset.orderEmbOfFin_mem (activeCoordinates factors) rfl j
  generalize hq : normalizedCoordinateFactors factors
      (activeOrderEmbedding factors j) = q at hj ⊢
  cases q with
  | none => exact Bool.noConfusion hj
  | some f =>
      simp only [evalOptionalFactor, activeNormalizedFactor, hq, Option.get_some]

/-- The product of all optional normalized factors equals the product over active coordinates.
In particular, this holds uniformly when the active set, or the ambient `Fin n`, is empty. -/
theorem normalizedCoordinateFactors_evaluation_active
    (factors : List (Fin n × C₀(alpha, ℝ))) (x : Fin n → alpha) :
    ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) =
      ∏ j, activeNormalizedFactor factors j (x (activeOrderEmbedding factors j)) := by
  let A := activeCoordinates factors
  let v : Fin n → ℝ := fun i ↦
    evalOptionalFactor (x i) (normalizedCoordinateFactors factors i)
  calc
    ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) =
        ∏ i ∈ A, v i := by
      symm
      apply Finset.prod_subset (fun i _ ↦ Finset.mem_univ i)
      intro i _ hi
      have hnone := normalizedCoordinateFactors_eq_none_of_notMem_activeCoordinates
        factors (show i ∉ activeCoordinates factors from hi)
      simp only [v, hnone, evalOptionalFactor]
    _ = ∏ i : A, v i := (Finset.prod_finset_coe v A).symm
    _ = ∏ j, v ((A.orderIsoOfFin rfl) j) := by
      symm
      exact (A.orderIsoOfFin rfl).toEquiv.prod_comp (fun i : A ↦ v i)
    _ = ∏ j, activeNormalizedFactor factors j
          (x (activeOrderEmbedding factors j)) := by
      apply Finset.prod_congr rfl
      intro j _
      simpa only [v, A, activeOrderEmbedding,
        Finset.coe_orderIsoOfFin_apply] using
        (eval_activeNormalizedFactor factors j
          (x (activeOrderEmbedding factors j)))

/-- Scalar evaluation of a normalized term on only its active coordinates.  For an empty active
set this is the coefficient times the empty scalar product, hence just the coefficient. -/
def CoordinateProductTerm.activeEvaluation
    (t : CoordinateProductTerm (Fin n) alpha)
    (y : Fin (activeCoordinates t.factors).card → alpha) : ℝ :=
  t.coefficient * ∏ j, activeNormalizedFactor t.factors j (y j)

/-- Evaluation of a coordinate-product term factors through its increasing active-coordinate
restriction.  The restricting lambda is definitionally
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding t.factors)`. -/
theorem CoordinateProductTerm.toContinuousMap_apply_active
    (t : CoordinateProductTerm (Fin n) alpha) (x : Fin n → alpha) :
    t.toContinuousMap x =
      t.activeEvaluation (fun k ↦ x (activeOrderEmbedding t.factors k)) := by
  rw [CoordinateProductTerm.toContinuousMap_apply_normalized,
    normalizedCoordinateFactors_evaluation_active]
  rfl

end MarkovProcess.PiContinuousMap
