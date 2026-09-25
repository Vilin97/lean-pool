/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions

/-! # Matrix Extraction -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Note-facing identities characterizing the coarse-grained matrices. -/
structure ResponseMatrixIdentities {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (M : CoarseMatrices d) : Prop where
  sigma_symm : M.sigma.IsSymm
  sigmaStarInv_symm : M.sigmaStarInv.IsSymm
  sigmaStarInv_response :
    ∀ q : Vec d,
      responseJ U a 0 q =
        (1 / 2 : ℝ) * vecDot q (matVecMul M.sigmaStarInv q)
  kappa_response :
    ∀ p q : Vec d,
      mixedResponse U a p q =
        vecDot q (matVecMul M.sigmaStarInv (matVecMul M.kappa p))
  sigma_response :
    ∀ p : Vec d,
      sigmaCorrectedResponse U a M p =
        (1 / 2 : ℝ) * vecDot p (matVecMul M.sigma p)
  full_response :
    ∀ p q : Vec d,
      responseJ U a p q =
        (1 / 2 : ℝ) * vecDot p (matVecMul M.sigma p) +
          (1 / 2 : ℝ) *
            vecDot (q + matVecMul M.kappa p)
              (matVecMul M.sigmaStarInv (q + matVecMul M.kappa p)) -
          vecDot p q

namespace ResponseMatrixIdentities

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {M : CoarseMatrices d}
    (hM : ResponseMatrixIdentities U a M) :
    ResponseMatrixIdentities U b M where
  sigma_symm := hM.sigma_symm
  sigmaStarInv_symm := hM.sigmaStarInv_symm
  sigmaStarInv_response := by
    intro q
    simpa [responseJ_eq_ofAEEq h (0 : Vec d) q] using hM.sigmaStarInv_response q
  kappa_response := by
    intro p q
    simpa [mixedResponse, responseJ_eq_ofAEEq h p q,
      responseJ_eq_ofAEEq h p (0 : Vec d), responseJ_eq_ofAEEq h (0 : Vec d) q]
      using hM.kappa_response p q
  sigma_response := by
    intro p
    simpa [sigmaCorrectedResponse, responseJ_eq_ofAEEq h p (0 : Vec d)]
      using hM.sigma_response p
  full_response := by
    intro p q
    simpa [responseJ_eq_ofAEEq h p q] using hM.full_response p q

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {M : CoarseMatrices d} :
    ResponseMatrixIdentities U a M ↔ ResponseMatrixIdentities U b M :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseMatrixIdentities

/-- The canonical note-facing matrix-extraction target: the matrices obtained
directly from `J` satisfy the response identities. -/
def CanonicalResponseMatrixIdentities {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Prop :=
  ResponseMatrixIdentities U a (coarseMatrices U a)

namespace CanonicalResponseMatrixIdentities

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hM : CanonicalResponseMatrixIdentities U a) :
    CanonicalResponseMatrixIdentities U b := by
  simpa [CanonicalResponseMatrixIdentities, coarseMatrices_eq_ofAEEq h] using
    ResponseMatrixIdentities.ofAEEq h hM

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    CanonicalResponseMatrixIdentities U a ↔
      CanonicalResponseMatrixIdentities U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end CanonicalResponseMatrixIdentities

/-- Existence of public coarse-grained matrices satisfying the note-facing
identities. -/
def ResponseMatrixExists {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop :=
  ∃ M : CoarseMatrices d, ResponseMatrixIdentities U a M

namespace ResponseMatrixExists

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hM : ResponseMatrixExists U a) : ResponseMatrixExists U b := by
  rcases hM with ⟨M, hIdent⟩
  exact ⟨M, hIdent.ofAEEq h⟩

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseMatrixExists U a ↔ ResponseMatrixExists U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseMatrixExists

/-- Canonical matrix identities imply the existential matrix-extraction
statement. -/
theorem responseMatrixExists_of_canonicalResponseMatrixIdentities {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hM : CanonicalResponseMatrixIdentities U a) :
    ResponseMatrixExists U a :=
  ⟨coarseMatrices U a, hM⟩

/-- Chosen public coarse-grained matrices, once the extraction theorem has been
supplied. -/
noncomputable def responseMatrices {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) : CoarseMatrices d :=
  Classical.choose hM

theorem responseMatrices_identities {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) :
    ResponseMatrixIdentities U a (responseMatrices hM) :=
  Classical.choose_spec hM

noncomputable def sigmaMatrix {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) : Mat d :=
  (responseMatrices hM).sigma

noncomputable def sigmaStarInvMatrix {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) : Mat d :=
  (responseMatrices hM).sigmaStarInv

noncomputable def kappaMatrix {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) : Mat d :=
  (responseMatrices hM).kappa

theorem responseJ_eq_coarseMatrices_formula {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {M : CoarseMatrices d}
    (hM : ResponseMatrixIdentities U a M) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul M.sigma p) +
        (1 / 2 : ℝ) *
          vecDot (q + matVecMul M.kappa p)
            (matVecMul M.sigmaStarInv (q + matVecMul M.kappa p)) -
        vecDot p q :=
  hM.full_response p q

theorem responseJ_eq_canonical_coarseMatrices_formula {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hM : CanonicalResponseMatrixIdentities U a) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q + matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q + matVecMul (kappaCoarse U a) p)) -
        vecDot p q := by
  simpa [CanonicalResponseMatrixIdentities, coarseMatrices] using
    responseJ_eq_coarseMatrices_formula hM p q

theorem responseJ_eq_responseMatrices_formula {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hM : ResponseMatrixExists U a) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaMatrix hM) p) +
        (1 / 2 : ℝ) *
          vecDot (q + matVecMul (kappaMatrix hM) p)
            (matVecMul (sigmaStarInvMatrix hM)
              (q + matVecMul (kappaMatrix hM) p)) -
        vecDot p q := by
  simpa [sigmaMatrix, sigmaStarInvMatrix, kappaMatrix] using
    responseJ_eq_coarseMatrices_formula (responseMatrices_identities hM) p q

end

end Ch02
end Book
end Homogenization
