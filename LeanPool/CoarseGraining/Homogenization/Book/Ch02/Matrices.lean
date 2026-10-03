/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Response

/-! # Matrices -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public normalized matrix average over a Chapter 2 domain. -/
noncomputable def averageMat {d : ℕ} (U : Domain d) (A : Vec d → Mat d) : Mat d :=
  fun i j => average U (fun x => A x i j)

/-- The note-facing harmonic-mean matrix
`\fint_U symmPart(a)^{-1}`. -/
noncomputable def averagedSymmPartInv {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  averageMat U fun x => (symmPart (a.toCoeffField x))⁻¹

/-- The note-facing upper coefficient average
`\fint_U (symmPart(a) + skewPart(a)^t symmPart(a)^{-1} skewPart(a))`. -/
noncomputable def averagedSymmPartPlusCorrection {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Mat d :=
  averageMat U fun x =>
    symmPart (a.toCoeffField x) +
      matTranspose (skewPart (a.toCoeffField x)) *
        (symmPart (a.toCoeffField x))⁻¹ * skewPart (a.toCoeffField x)

/-- The harmonic-mean matrix depends only on the coefficient field up to a.e.
equality on the domain. -/
theorem averagedSymmPartInv_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    averagedSymmPartInv U a = averagedSymmPartInv U b := by
  ext i j
  unfold averagedSymmPartInv averageMat average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- The upper coefficient average depends only on the coefficient field up to
a.e. equality on the domain. -/
theorem averagedSymmPartPlusCorrection_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) :
    averagedSymmPartPlusCorrection U a = averagedSymmPartPlusCorrection U b := by
  ext i j
  unfold averagedSymmPartPlusCorrection averageMat average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- The coarse-grained response matrices extracted from the quadratic response
functional. We keep `sigmaStarInv` primitive at this stage; constructing
`sigmaStar` itself belongs to the later positivity/invertibility theorem. -/
structure CoarseMatrices (d : ℕ) where
  sigma : Mat d
  sigmaStarInv : Mat d
  kappa : Mat d

namespace CoarseMatrices

/-- The derived coarse matrix `sigmaStar = sigmaStarInv^{-1}`. -/
def sigmaStar {d : ℕ} (M : CoarseMatrices d) : Mat d :=
  M.sigmaStarInv⁻¹

/-- The derived coarse matrix `b = sigma + kappa^t sigmaStarInv kappa`. -/
def b {d : ℕ} (M : CoarseMatrices d) : Mat d :=
  M.sigma + matTranspose M.kappa * M.sigmaStarInv * M.kappa

/-- The derived coarse coefficient matrix `a = sigma - kappa^t`. -/
def coeff {d : ℕ} (M : CoarseMatrices d) : Mat d :=
  M.sigma - matTranspose M.kappa

@[ext] theorem ext {d : ℕ} {M N : CoarseMatrices d}
    (hsigma : M.sigma = N.sigma)
    (hsigmaStarInv : M.sigmaStarInv = N.sigmaStarInv)
    (hkappa : M.kappa = N.kappa) :
    M = N := by
  cases M
  cases N
  simp_all

end CoarseMatrices

/-- The mixed response appearing in the definition of the coarse skew matrix. -/
noncomputable def mixedResponse {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) : ℝ :=
  responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q + vecDot p q

/-- Entry formula for the canonical coarse matrix `sigmaStarInv`.

The diagonal entries are extracted from the pure `q` response, while the
off-diagonal entries use the usual polarization identity. -/
noncomputable def sigmaStarInvEntry {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * responseJ U a (0 : Vec d) (Pi.single i 1)
  else
    responseJ U a (0 : Vec d) (Pi.single i 1 + Pi.single j 1)
      - responseJ U a (0 : Vec d) (Pi.single i 1)
      - responseJ U a (0 : Vec d) (Pi.single j 1)

/-- The entry formula for `sigmaStarInv` is symmetric by construction. -/
theorem sigmaStarInvEntry_comm {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (i j : Fin d) :
    sigmaStarInvEntry U a i j = sigmaStarInvEntry U a j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    have hsum :
        (Pi.single j (1 : ℝ) : Vec d) + Pi.single i (1 : ℝ) =
          Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ) := by
      ext k
      simp [add_comm]
    simp [sigmaStarInvEntry, hij, hji, hsum]
    ring

/-- The entry formula for `sigmaStarInv` depends only on the coefficient field
up to a.e. equality on the domain. -/
theorem sigmaStarInvEntry_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (i j : Fin d) :
    sigmaStarInvEntry U a i j = sigmaStarInvEntry U b i j := by
  by_cases hij : i = j
  · simp [sigmaStarInvEntry, hij, responseJ_eq_ofAEEq h]
  · simp [sigmaStarInvEntry, hij, responseJ_eq_ofAEEq h]

/-- The canonical coarse matrix `sigmaStarInv(U; a)` extracted from `J(U,0,q;a)`. -/
noncomputable def sigmaStarInvCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  fun i j => sigmaStarInvEntry U a i j

/-- The canonical matrix `sigmaStarInv(U; a)` is symmetric by polarization. -/
theorem sigmaStarInvCoarse_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (sigmaStarInvCoarse U a).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  exact sigmaStarInvEntry_comm U a j i

/-- The canonical matrix `sigmaStarInv(U; a)` is invariant under a.e. changes
of coefficient representative. -/
theorem sigmaStarInvCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    sigmaStarInvCoarse U a = sigmaStarInvCoarse U b := by
  ext i j
  exact sigmaStarInvEntry_eq_ofAEEq h i j

/-- The canonical coarse matrix `sigmaStar(U; a)`, represented as the
nonsingular-inverse expression of `sigmaStarInv(U; a)`. The later positivity
theory proves that this is the genuine inverse in the note-facing cases. -/
noncomputable def sigmaStarCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  (sigmaStarInvCoarse U a)⁻¹

/-- The canonical matrix `sigmaStar(U; a)` is invariant under a.e. changes of
coefficient representative. -/
theorem sigmaStarCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    sigmaStarCoarse U a = sigmaStarCoarse U b := by
  simp [sigmaStarCoarse, sigmaStarInvCoarse_eq_ofAEEq h]

/-- The canonical matrix `sigmaStar(U; a)` is symmetric. -/
theorem sigmaStarCoarse_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (sigmaStarCoarse U a).IsSymm := by
  unfold sigmaStarCoarse
  exact isSymm_nonsingInv (sigmaStarInvCoarse_isSymm U a)

/-- The mixed response depends only on the coefficient field up to a.e. equality
on the domain. -/
theorem mixedResponse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) :
    mixedResponse U a p q = mixedResponse U b p q := by
  simp [mixedResponse, responseJ_eq_ofAEEq h]

/-- The canonical mixed matrix `sigmaStarInv(U; a) * kappa(U; a)`, extracted
directly from the mixed response. -/
noncomputable def sigmaStarInvKappaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  fun i j => mixedResponse U a (Pi.single j 1) (Pi.single i 1)

/-- The canonical mixed matrix is invariant under a.e. changes of coefficient
representative. -/
theorem sigmaStarInvKappaCoarse_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) :
    sigmaStarInvKappaCoarse U a = sigmaStarInvKappaCoarse U b := by
  ext i j
  exact mixedResponse_eq_ofAEEq h (Pi.single j 1) (Pi.single i 1)

/-- The canonical coupling matrix `kappa(U; a)`. -/
noncomputable def kappaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  sigmaStarCoarse U a * sigmaStarInvKappaCoarse U a

/-- The canonical coupling matrix is invariant under a.e. changes of
coefficient representative. -/
theorem kappaCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    kappaCoarse U a = kappaCoarse U b := by
  simp [kappaCoarse, sigmaStarCoarse_eq_ofAEEq h,
    sigmaStarInvKappaCoarse_eq_ofAEEq h]

/-- Under nondegeneracy, `sigmaStar(U; a)` is the right inverse of
`sigmaStarInv(U; a)`. -/
theorem sigmaStarInvCoarse_mul_sigmaStarCoarse {d : ℕ} {U : Domain d}
    {a : CoeffOn U} (hdet : IsUnit (sigmaStarInvCoarse U a).det) :
    sigmaStarInvCoarse U a * sigmaStarCoarse U a = 1 := by
  simpa [sigmaStarCoarse] using Matrix.mul_nonsing_inv (sigmaStarInvCoarse U a) hdet

/-- Under nondegeneracy, `sigmaStar(U; a)` is the left inverse of
`sigmaStarInv(U; a)`. -/
theorem sigmaStarCoarse_mul_sigmaStarInvCoarse {d : ℕ} {U : Domain d}
    {a : CoeffOn U} (hdet : IsUnit (sigmaStarInvCoarse U a).det) :
    sigmaStarCoarse U a * sigmaStarInvCoarse U a = 1 := by
  simpa [sigmaStarCoarse] using Matrix.nonsing_inv_mul (sigmaStarInvCoarse U a) hdet

/-- Under nondegeneracy, the canonical `kappa` definition really solves
`sigmaStarInv * kappa = sigmaStarInvKappa`. -/
theorem sigmaStarInvCoarse_mul_kappaCoarse_eq_sigmaStarInvKappaCoarse
    {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hdet : IsUnit (sigmaStarInvCoarse U a).det) :
    sigmaStarInvCoarse U a * kappaCoarse U a =
      sigmaStarInvKappaCoarse U a := by
  unfold kappaCoarse sigmaStarCoarse
  simpa [Matrix.mul_assoc] using
    Matrix.mul_nonsing_inv_cancel_left
      (A := sigmaStarInvCoarse U a) (sigmaStarInvKappaCoarse U a) hdet

/-- Vector form of
`sigmaStarInvCoarse_mul_kappaCoarse_eq_sigmaStarInvKappaCoarse`. -/
theorem matVecMul_sigmaStarInvCoarse_kappaCoarse
    {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hdet : IsUnit (sigmaStarInvCoarse U a).det) (p : Vec d) :
    matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p) =
      matVecMul (sigmaStarInvKappaCoarse U a) p := by
  rw [matVecMul_mul, sigmaStarInvCoarse_mul_kappaCoarse_eq_sigmaStarInvKappaCoarse hdet]

/-- The canonical corrected `p`-response whose quadratic form defines
`sigma(U; a)`. -/
noncomputable def canonicalSigmaCorrectedResponse {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (p : Vec d) : ℝ :=
  responseJ U a p 0 -
    (1 / 2 : ℝ) * vecDot p
      (matVecMul (matTranspose (kappaCoarse U a))
        (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)))

/-- The canonical corrected response is invariant under a.e. changes of
coefficient representative. -/
theorem canonicalSigmaCorrectedResponse_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (p : Vec d) :
    canonicalSigmaCorrectedResponse U a p =
      canonicalSigmaCorrectedResponse U b p := by
  simp [canonicalSigmaCorrectedResponse, responseJ_eq_ofAEEq h,
    sigmaStarInvCoarse_eq_ofAEEq h, kappaCoarse_eq_ofAEEq h]

/-- Entry formula for the canonical coarse matrix `sigma`.

As for `sigmaStarInv`, the diagonal entries come from the quadratic values and
the off-diagonal entries from polarization. -/
noncomputable def sigmaEntry {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * canonicalSigmaCorrectedResponse U a (Pi.single i 1)
  else
    canonicalSigmaCorrectedResponse U a (Pi.single i 1 + Pi.single j 1)
      - canonicalSigmaCorrectedResponse U a (Pi.single i 1)
      - canonicalSigmaCorrectedResponse U a (Pi.single j 1)

/-- The entry formula for `sigma` is symmetric by construction. -/
theorem sigmaEntry_comm {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (i j : Fin d) :
    sigmaEntry U a i j = sigmaEntry U a j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    have hsum :
        (Pi.single j (1 : ℝ) : Vec d) + Pi.single i (1 : ℝ) =
          Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ) := by
      ext k
      simp [add_comm]
    simp [sigmaEntry, hij, hji, hsum]
    ring

/-- The entry formula for `sigma` depends only on the coefficient field up to
a.e. equality on the domain. -/
theorem sigmaEntry_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (i j : Fin d) :
    sigmaEntry U a i j = sigmaEntry U b i j := by
  by_cases hij : i = j
  · simp [sigmaEntry, hij, canonicalSigmaCorrectedResponse_eq_ofAEEq h]
  · simp [sigmaEntry, hij, canonicalSigmaCorrectedResponse_eq_ofAEEq h]

/-- The canonical coarse matrix `sigma(U; a)`. -/
noncomputable def sigmaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Mat d :=
  fun i j => sigmaEntry U a i j

/-- The canonical matrix `sigma(U; a)` is symmetric by polarization. -/
theorem sigmaCoarse_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (sigmaCoarse U a).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  exact sigmaEntry_comm U a j i

/-- The canonical matrix `sigma(U; a)` is invariant under a.e. changes of
coefficient representative. -/
theorem sigmaCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    sigmaCoarse U a = sigmaCoarse U b := by
  ext i j
  exact sigmaEntry_eq_ofAEEq h i j

/-- The canonical package of coarse-grained response matrices. -/
noncomputable def coarseMatrices {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    CoarseMatrices d where
  sigma := sigmaCoarse U a
  sigmaStarInv := sigmaStarInvCoarse U a
  kappa := kappaCoarse U a

/-- The canonical package of coarse-grained response matrices is invariant under
a.e. changes of coefficient representative. -/
theorem coarseMatrices_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    coarseMatrices U a = coarseMatrices U b := by
  ext <;>
    simp [coarseMatrices, sigmaCoarse_eq_ofAEEq h, sigmaStarInvCoarse_eq_ofAEEq h,
      kappaCoarse_eq_ofAEEq h]

/-- The `sigma` component of the canonical matrix package is symmetric. -/
theorem coarseMatrices_sigma_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).sigma.IsSymm :=
  sigmaCoarse_isSymm U a

/-- The `sigmaStarInv` component of the canonical matrix package is symmetric. -/
theorem coarseMatrices_sigmaStarInv_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).sigmaStarInv.IsSymm :=
  sigmaStarInvCoarse_isSymm U a

/-- The corrected `p`-response whose quadratic form defines `sigma`. -/
noncomputable def sigmaCorrectedResponse {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (M : CoarseMatrices d) (p : Vec d) : ℝ :=
  responseJ U a p 0 -
    (1 / 2 : ℝ) * vecDot p
      (matVecMul (matTranspose M.kappa)
        (matVecMul M.sigmaStarInv (matVecMul M.kappa p)))

/-- The corrected response for a fixed matrix package depends only on the
coefficient field up to a.e. equality on the domain. -/
theorem sigmaCorrectedResponse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (M : CoarseMatrices d) (p : Vec d) :
    sigmaCorrectedResponse U a M p = sigmaCorrectedResponse U b M p := by
  simp [sigmaCorrectedResponse, responseJ_eq_ofAEEq h]

@[simp] theorem coarseMatrices_sigma {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).sigma = sigmaCoarse U a :=
  rfl

@[simp] theorem coarseMatrices_sigmaStarInv {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).sigmaStarInv = sigmaStarInvCoarse U a :=
  rfl

@[simp] theorem coarseMatrices_sigmaStar {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).sigmaStar = sigmaStarCoarse U a :=
  rfl

@[simp] theorem coarseMatrices_kappa {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseMatrices U a).kappa = kappaCoarse U a :=
  rfl

theorem sigmaCorrectedResponse_coarseMatrices {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (p : Vec d) :
    sigmaCorrectedResponse U a (coarseMatrices U a) p =
      canonicalSigmaCorrectedResponse U a p :=
  rfl

/-- Canonical derived coarse matrix
`b(U; a) = sigma + kappa^t sigmaStarInv kappa`. -/
noncomputable def bCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d :=
  (coarseMatrices U a).b

/-- Canonical derived coarse coefficient matrix `a(U; a) = sigma - kappa^t`. -/
noncomputable def aCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d :=
  (coarseMatrices U a).coeff

/-- Canonical derived adjoint coarse coefficient matrix. -/
noncomputable def aStarCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d :=
  sigmaStarCoarse U a - matTranspose (kappaCoarse U a)

/-- The canonical derived matrix `b(U; a)` is invariant under a.e. changes of
coefficient representative. -/
theorem bCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    bCoarse U a = bCoarse U b := by
  unfold bCoarse
  rw [coarseMatrices_eq_ofAEEq h]

/-- The canonical derived matrix `a(U; a)` is invariant under a.e. changes of
coefficient representative. -/
theorem aCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    aCoarse U a = aCoarse U b := by
  unfold aCoarse
  rw [coarseMatrices_eq_ofAEEq h]

/-- The canonical derived matrix `aStar(U; a)` is invariant under a.e. changes
of coefficient representative. -/
theorem aStarCoarse_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    aStarCoarse U a = aStarCoarse U b := by
  simp [aStarCoarse, sigmaStarCoarse_eq_ofAEEq h, kappaCoarse_eq_ofAEEq h]

end

end Ch02
end Book
end Homogenization
