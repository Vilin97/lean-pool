/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Block
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law

/-! # Theta Ellipticity -/

@[expose] public section

namespace Homogenization

/-!
# Ellipticity class and shared matrix infrastructure

Formalization of the sharp-constant pointwise ellipticity vocabulary of
Proposition 2.1 of the high-moment paper (Armstrong–Kuusi–Loher, in
preparation), against the coarse-graining surface of this development.  Items
A1–A3, together with a handful of shared `MatLoewnerLE` helpers and the key
nonsymmetric flux inequality `(★)` reused by the sharp block bounds.

All matrix work is on `Vec d = Fin d → ℝ` / `Mat d`; no `EuclideanSpace`.
-/

open Homogenization.Book.Ch02
open Homogenization.Book.Ch04 (RestrictionCoeffLaw)

variable {d : ℕ}

/-! ## Scalar-multiple-of-identity quadratic forms and `MatLoewnerLE` helpers -/

/-- The identity matrix acts as the identity on vectors. -/
theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- A scalar multiple of the identity acts by scaling. -/
theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul, matVecMul_one]

/-- Quadratic form of a scalar multiple of the identity. -/
theorem vecDot_matVecMul_smul_one (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  rw [matVecMul_smul_one, vecDot_smul_right]
  rfl

/-- Quadratic form of the identity matrix. -/
theorem vecDot_matVecMul_one (x : Vec d) :
    vecDot x (matVecMul (1 : Mat d) x) = vecNormSq x := by
  rw [matVecMul_one]; rfl

/-- `MatLoewnerLE` unwound to a plain quadratic-form comparison (the `½`
factors cancel). -/
theorem matLoewnerLE_iff (A B : Mat d) :
    MatLoewnerLE A B ↔
      ∀ x : Vec d, vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  constructor
  · intro h x; have := h x; linarith
  · intro h x; have := h x; linarith

/-- Build `MatLoewnerLE` from a plain quadratic-form comparison. -/
theorem matLoewnerLE_of_forall {A B : Mat d}
    (h : ∀ x : Vec d, vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x)) :
    MatLoewnerLE A B := (matLoewnerLE_iff A B).2 h

/-! ## A1 — the `(1, Θ)` ellipticity class -/

/-- **A1.**  Membership in the uniform ellipticity class with constants `(1, Θ)`:
`ξ · A ξ ≥ |ξ|²` and `ξ · A⁻¹ ξ ≥ Θ⁻¹ |ξ|²`. -/
abbrev IsThetaElliptic (Θ : ℝ) (A : Mat d) : Prop := IsEllipticMatrix 1 Θ A

/-! ## A2 — the law-level ellipticity predicate -/

open MeasureTheory in
/-- **A2.**  A carrier coefficient law is `Θ`-elliptic when almost every
realization lies, almost everywhere in space, in the `(1, Θ)` ellipticity class.
Following the carrier redesign (Packet P3, decision E-2), the entrywise
measurability conjunct of the paper's class `Ω_Θ` is now **free by type**: every
element of the honest-fields carrier `RegCoeffField d` carries a proof that each
of its scalar entries is Borel measurable (`RegCoeffField.entry_measurable`), so
the a.e.-modification bridge (`CoarseBounds/AeBridge.lean`) recovers the
pointwise-elliptic representative from `a.entry_measurable` rather than a bundled
conjunct.  The statement is therefore the paper's clean `Ω_Θ` membership. -/
def ThetaEllipticLaw (Θ : ℝ) (P : RestrictionCoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)

/-! ## The key nonsymmetric flux inequality `(★)`

For an elliptic matrix `B`, `|B η|² ≤ Lam · (η · sᴮ η)` where `sᴮ = symmPart B`.
This is the second ellipticity inequality read backwards, and is the workhorse
behind the sharp flux bounds A5 and the nonsymmetric coercivity A4. -/

/-- The flux inequality `(★)`: `‖B η‖² ≤ Lam · η · (symmPart B) η`. -/
theorem vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix
    {lam Lam : ℝ} {B : Mat d} (hB : IsEllipticMatrix lam Lam B) (η : Vec d) :
    vecNormSq (matVecMul B η) ≤ Lam * vecDot η (matVecMul (symmPart B) η) := by
  have hdet : IsUnit B.det := isUnit_det_of_isEllipticMatrix hB
  set ξ := matVecMul B η with hξ
  have hBinv : matVecMul B⁻¹ ξ = η := by
    rw [hξ, matVecMul_mul, Matrix.nonsing_inv_mul B hdet, matVecMul_one]
  have hident :
      vecDot ξ (matVecMul B⁻¹ ξ) = vecDot η (matVecMul (symmPart B) η) := by
    rw [hBinv, vecDot_comm, vecDot_matVecMul_symmPart, hξ]
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hB.1 hB.2.1
  have hsecond : Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul B⁻¹ ξ) := hB.2.2.2 ξ
  rw [hident] at hsecond
  have := mul_le_mul_of_nonneg_left hsecond hLam_pos.le
  have hcancel : Lam * (Lam⁻¹ * vecNormSq ξ) = vecNormSq ξ := by
    field_simp [hLam_pos.ne']
  rw [hcancel] at this
  exact this

/-! ## A3 — symmetric part Loewner bounds -/

/-- **A3 (upper).**  `s ≤ Θ • 1` in the Loewner order, `s = symmPart A`. -/
theorem symmPart_matLoewnerLE_smul_one_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    MatLoewnerLE (symmPart A) (Θ • (1 : Mat d)) := by
  refine matLoewnerLE_of_forall (fun x => ?_)
  rw [vecDot_matVecMul_smul_one]
  simpa using upperBound_symmPart_of_isEllipticMatrix hA x

/-- **A3 (lower).**  `1 ≤ s` in the Loewner order, `s = symmPart A`. -/
theorem one_matLoewnerLE_symmPart_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    MatLoewnerLE (1 : Mat d) (symmPart A) := by
  refine matLoewnerLE_of_forall (fun x => ?_)
  rw [vecDot_matVecMul_one]
  simpa using lowerBound_symmPart_of_isEllipticMatrix hA x

end Homogenization
