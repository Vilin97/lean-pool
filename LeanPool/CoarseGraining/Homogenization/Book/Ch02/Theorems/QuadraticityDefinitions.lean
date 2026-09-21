/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions

/-! # Quadraticity Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for the statement that `(p,q) ↦ J(U,p,q;a)` is
quadratic.

The two fields are the homogeneity and parallelogram identities. The canonical
public theorem proving this package is `responseQuadraticTheory` in
`Quadraticity.lean`. -/
structure ResponseQuadraticTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop where
  responseJ_smul :
    ∀ c : ℝ, ∀ p q : Vec d,
      responseJ U a (c • p) (c • q) = c ^ 2 * responseJ U a p q
  responseJ_parallelogram :
    ∀ p1 q1 p2 q2 : Vec d,
      responseJ U a (p1 + p2) (q1 + q2) +
          responseJ U a (p1 - p2) (q1 - q2) =
        2 * responseJ U a p1 q1 + 2 * responseJ U a p2 q2

namespace ResponseQuadraticTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hQuad : ResponseQuadraticTheory U a) :
    ResponseQuadraticTheory U b where
  responseJ_smul := by
    intro c p q
    calc
      responseJ U b (c • p) (c • q)
          = responseJ U a (c • p) (c • q) := by
              rw [responseJ_eq_ofAEEq h (c • p) (c • q)]
      _ = c ^ 2 * responseJ U a p q := hQuad.responseJ_smul c p q
      _ = c ^ 2 * responseJ U b p q := by
              rw [responseJ_eq_ofAEEq h p q]
  responseJ_parallelogram := by
    intro p1 q1 p2 q2
    calc
      responseJ U b (p1 + p2) (q1 + q2) +
          responseJ U b (p1 - p2) (q1 - q2)
          = responseJ U a (p1 + p2) (q1 + q2) +
              responseJ U a (p1 - p2) (q1 - q2) := by
              rw [responseJ_eq_ofAEEq h (p1 + p2) (q1 + q2)]
              rw [responseJ_eq_ofAEEq h (p1 - p2) (q1 - q2)]
      _ = 2 * responseJ U a p1 q1 + 2 * responseJ U a p2 q2 :=
              hQuad.responseJ_parallelogram p1 q1 p2 q2
      _ = 2 * responseJ U b p1 q1 + 2 * responseJ U b p2 q2 := by
              rw [responseJ_eq_ofAEEq h p1 q1]
              rw [responseJ_eq_ofAEEq h p2 q2]

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseQuadraticTheory U a ↔ ResponseQuadraticTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseQuadraticTheory

theorem responseJ_smul_of_responseQuadraticTheory {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hQuad : ResponseQuadraticTheory U a) (c : ℝ) (p q : Vec d) :
    responseJ U a (c • p) (c • q) = c ^ 2 * responseJ U a p q :=
  hQuad.responseJ_smul c p q

theorem responseJ_parallelogram_of_responseQuadraticTheory {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hQuad : ResponseQuadraticTheory U a) (p1 q1 p2 q2 : Vec d) :
    responseJ U a (p1 + p2) (q1 + q2) +
        responseJ U a (p1 - p2) (q1 - q2) =
      2 * responseJ U a p1 q1 + 2 * responseJ U a p2 q2 :=
  hQuad.responseJ_parallelogram p1 q1 p2 q2

end

end Ch02
end Book
end Homogenization
