/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalNoteTerms

/-! # Descendants Average -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem descendantsAverage_sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_error_of_localBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (j : ℕ) (E : TriadicCube d → ℝ)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2) +
          E R) :
    descendantsAverage Q j
      (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q (j + 1)
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) +
      descendantsAverage Q j E := by
  have havg :
      descendantsAverage Q j
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) ≤
        descendantsAverage Q j
          (fun R =>
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage R 1
                (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2) +
            E R) := by
    exact descendantsAverage_le_descendantsAverage Q j (fun R hR => hlocal R hR)
  calc
    descendantsAverage Q j
        (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2)
        ≤
          descendantsAverage Q j
            (fun R =>
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage R 1
                  (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2) +
              E R) := havg
    _ =
          descendantsAverage Q j
            (fun R =>
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage R 1
                  (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2)) +
            descendantsAverage Q j E := by
              rw [descendantsAverage_add Q j
                (fun R =>
                  Real.rpow (3 : ℝ) (-2 * s) *
                    descendantsAverage R 1
                      (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2))
                E]
    _ =
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q (j + 1)
              (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) +
            descendantsAverage Q j E := by
              rw [descendantsAverage_smul Q j (Real.rpow (3 : ℝ) (-2 * s))
                (fun R =>
                  descendantsAverage R 1
                    (fun S => (cubeBesovNegativeVectorSeminormTwo S s u) ^ 2))]
              rw [← descendantsAverage_add_eq_descendantsAverage_descendantsAverage
                (Q := Q) (j := j) (n := 1)
                (F := fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2)]


end

end Homogenization
