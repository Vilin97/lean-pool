/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction

/-! # Matrix Extraction Proofs -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- The canonical coarse matrices extracted from the response functional satisfy
the note-facing matrix identities. -/
theorem canonicalResponseMatrixIdentities {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    CanonicalResponseMatrixIdentities U a :=
  Homogenization.Internal.Ch02.BookCh02.canonicalResponseMatrixIdentities U a

/-- Existence form of matrix extraction, obtained from the canonical matrices. -/
theorem responseMatrixExists {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseMatrixExists U a :=
  responseMatrixExists_of_canonicalResponseMatrixIdentities
    (canonicalResponseMatrixIdentities U a)

/-- Public pure-flux quadratic formula defining `sigmaStarInv(U; a)`. -/
theorem responseJ_zero_q_eq_sigmaStarInvCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (q : Vec d) :
    responseJ U a 0 q =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) :=
  (canonicalResponseMatrixIdentities U a).sigmaStarInv_response q

/-- Public mixed-response formula defining `kappa(U; a)`. -/
theorem mixedResponse_eq_sigmaStarInv_kappa {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    mixedResponse U a p q =
      vecDot q
        (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) := by
  simpa [coarseMatrices] using
    (canonicalResponseMatrixIdentities U a).kappa_response p q

/-- Public corrected pure-gradient formula defining `sigma(U; a)`. -/
theorem canonicalSigmaCorrectedResponse_eq_sigmaCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p : Vec d) :
    canonicalSigmaCorrectedResponse U a p =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) := by
  simpa [sigmaCorrectedResponse_coarseMatrices] using
    (canonicalResponseMatrixIdentities U a).sigma_response p

/-- Public direct coarse-matrix formula for the response functional. -/
theorem responseJ_eq_coarseMatrices_formula_canonical {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q + matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q + matVecMul (kappaCoarse U a) p)) -
        vecDot p q :=
  responseJ_eq_canonical_coarseMatrices_formula
    (canonicalResponseMatrixIdentities U a) p q

end

end Ch02
end Book
end Homogenization
