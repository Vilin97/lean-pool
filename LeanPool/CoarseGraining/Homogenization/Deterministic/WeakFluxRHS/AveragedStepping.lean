/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.AveragedLocal.DescendantsAverage
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FullStepping

/-! # Averaged Stepping -/

@[expose] public section

namespace Homogenization

noncomputable section

/-- Averaged-scale form of the weak-flux local recurrence.  This is the
Section 3.2.3 Step 4 bookkeeping bridge specialized to the flux field
`a u`. -/
theorem descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_flux_le_discount_next_add_error_of_localBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (j : ℕ) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          E R) :
    descendantsAverage Q j
      (fun R =>
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2) ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q (j + 1)
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      descendantsAverage Q j E := by
  exact
    descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_error_of_localBound
      Q s (fun x => matVecMul (a x) (u x)) j E hlocal

end

end Homogenization
