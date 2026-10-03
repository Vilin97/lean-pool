/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Quadraticity

/-! # Quadraticity -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 quadraticity theorem for the response functional. -/
theorem responseQuadraticTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseQuadraticTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseQuadraticTheory U a

/-- Public homogeneity identity for the response functional. -/
theorem responseJ_smul {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (c : ℝ) (p q : Vec d) :
    responseJ U a (c • p) (c • q) = c ^ 2 * responseJ U a p q :=
  (responseQuadraticTheory U a).responseJ_smul c p q

/-- Public parallelogram identity for the response functional. -/
theorem responseJ_parallelogram {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (p1 q1 p2 q2 : Vec d) :
    responseJ U a (p1 + p2) (q1 + q2) +
        responseJ U a (p1 - p2) (q1 - q2) =
      2 * responseJ U a p1 q1 + 2 * responseJ U a p2 q2 :=
  (responseQuadraticTheory U a).responseJ_parallelogram p1 q1 p2 q2

end

end Ch02
end Book
end Homogenization
