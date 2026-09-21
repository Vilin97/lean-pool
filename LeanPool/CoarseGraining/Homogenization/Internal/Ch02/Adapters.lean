/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.HarmonicMean
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.UpperLeftAverage

/-! # Adapters -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

/-- The public Chapter 2 average is definitionally the old volume average. -/
theorem book_average_eq_volumeAverage {d : ℕ} (U : Book.Ch02.Domain d)
    (f : Vec d → ℝ) :
    Book.Ch02.average U f = volumeAverage (U : Set (Vec d)) f :=
  rfl

/-- The public Chapter 2 response integrand is definitionally the old scalar
response integrand. -/
theorem book_responseIntegrand_eq_scalarResponseIntegrand {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U a) :
    Book.Ch02.responseIntegrand U a p q v =
      scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField p q v :=
  rfl

/-- Adapter from the new public response value to the old proof-engine value. -/
theorem book_responseValue_eq_volumeAverage_scalarResponseIntegrand {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U a) :
    Book.Ch02.responseValue U a p q v =
      volumeAverage (U : Set (Vec d))
        (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField p q v) :=
  rfl

/-- The public value set is the old value set, behind the internal boundary. -/
theorem book_responseValueSet_eq_responseJValueSet {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Book.Ch02.responseValueSet U a p q =
      responseJValueSet (U : Set (Vec d)) p q a.toCoeffField := by
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

/-- The public response functional is the old response functional, internally. -/
theorem book_responseJ_eq_ResponseJ {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Book.Ch02.responseJ U a p q =
      ResponseJ (U : Set (Vec d)) p q a.toCoeffField := by
  simp [Book.Ch02.responseJ, ResponseJ, book_responseValueSet_eq_responseJValueSet]

/-- The public `sigmaStarInv` matrix is the old canonical matrix, internally. -/
theorem book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.sigmaStarInvCoarse U a =
      Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Book.Ch02.sigmaStarInvCoarse, Book.Ch02.sigmaStarInvEntry,
      book_responseJ_eq_ResponseJ]
  · simp [Book.Ch02.sigmaStarInvCoarse, Book.Ch02.sigmaStarInvEntry,
      hij, book_responseJ_eq_ResponseJ]

/-- The public mixed-response matrix is the old canonical mixed matrix,
internally. -/
theorem book_sigmaStarInvKappaCoarse_eq_sigmaStarInvKappaCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.sigmaStarInvKappaCoarse U a =
      Homogenization.sigmaStarInvKappaCoarse (U : Set (Vec d)) a.toCoeffField := by
  ext i j
  simp [Book.Ch02.sigmaStarInvKappaCoarse, Book.Ch02.mixedResponse,
    Homogenization.sigmaStarInvKappaCoarse, book_responseJ_eq_ResponseJ]

/-- The public `sigmaStar` matrix is the old canonical matrix, internally. -/
theorem book_sigmaStarCoarse_eq_sigmaStarCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.sigmaStarCoarse U a =
      Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField := by
  simp [Book.Ch02.sigmaStarCoarse, Homogenization.sigmaStarCoarse,
    book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse]

/-- The public `kappa` matrix is the old canonical matrix, internally. -/
theorem book_kappaCoarse_eq_kappaCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.kappaCoarse U a =
      Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField := by
  simp [Book.Ch02.kappaCoarse, Homogenization.kappaCoarse,
    book_sigmaStarCoarse_eq_sigmaStarCoarse,
    book_sigmaStarInvKappaCoarse_eq_sigmaStarInvKappaCoarse]

/-- The public corrected `sigma` response is the old corrected response,
internally. -/
theorem book_canonicalSigmaCorrectedResponse_eq_sigmaCorrectedResponse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (p : Vec d) :
    Book.Ch02.canonicalSigmaCorrectedResponse U a p =
      Homogenization.sigmaCorrectedResponse (U : Set (Vec d)) a.toCoeffField p := by
  simp [Book.Ch02.canonicalSigmaCorrectedResponse,
    Homogenization.sigmaCorrectedResponse, book_responseJ_eq_ResponseJ,
    book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse, book_kappaCoarse_eq_kappaCoarse]

/-- The public `sigma` matrix is the old canonical matrix, internally. -/
theorem book_sigmaCoarse_eq_sigmaCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.sigmaCoarse U a =
      Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Book.Ch02.sigmaCoarse, Book.Ch02.sigmaEntry,
      book_canonicalSigmaCorrectedResponse_eq_sigmaCorrectedResponse]
  · simp [Book.Ch02.sigmaCoarse, Book.Ch02.sigmaEntry,
      hij, book_canonicalSigmaCorrectedResponse_eq_sigmaCorrectedResponse]

/-- The public harmonic-mean average is the old averaged inverse symmetric
part, internally. -/
theorem book_averagedSymmPartInv_eq_averagedSymmPartInv {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.averagedSymmPartInv U a =
      Homogenization.averagedSymmPartInv (U : Set (Vec d)) a.toCoeffField :=
  rfl

/-- The public upper coefficient average is the old averaged upper-left
coefficient, internally. -/
theorem book_averagedSymmPartPlusCorrection_eq_averagedSymmPartPlusCorrection
    {d : ℕ} (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.averagedSymmPartPlusCorrection U a =
      Homogenization.averagedSymmPartPlusCorrection (U : Set (Vec d)) a.toCoeffField :=
  rfl

/-- The public derived `b` matrix is the old canonical `bCoarse`, once the old
`sigmaStar` witness identifies its inverse with `sigmaStarInvCoarse`. -/
theorem book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (hS :
      IsSigmaStarCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)) :
    (Book.Ch02.coarseMatrices U a).b =
      Homogenization.bCoarse
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
  change
    Book.Ch02.sigmaCoarse U a +
        matTranspose (Book.Ch02.kappaCoarse U a) *
          Book.Ch02.sigmaStarInvCoarse U a * Book.Ch02.kappaCoarse U a =
      Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField +
        matTranspose (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) *
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹ *
            Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField
  rw [book_sigmaCoarse_eq_sigmaCoarse U a, book_kappaCoarse_eq_kappaCoarse U a,
    book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]

end

end Ch02
end Internal
end Homogenization
