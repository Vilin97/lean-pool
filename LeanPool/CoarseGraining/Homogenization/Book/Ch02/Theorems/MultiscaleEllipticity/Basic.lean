/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticityDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ.ChangeOfQ
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ.ScaleBounds
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Adapters
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Basic -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Basic Helpers for Chapter 2.5 Multiscale Ellipticity

This file contains the matrix-norm, finite-supremum, and scale-weight helper
lemmas used by the public multiscale ellipticity theorem package.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius


theorem matrixNorm_eq_matrixOperatorNorm {d : ℕ} (A : Mat d) :
    matrixNorm A = matrixOperatorNorm A := by
  rfl

theorem matrixFrobeniusNorm_eq_matNorm {d : ℕ} (A : Mat d) :
    matrixFrobeniusNorm A = Homogenization.matNorm A := by
  rfl

theorem matrixNorm_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matrixNorm A := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using matrixOperatorNorm_nonneg A

theorem matrixNorm_le_matNorm {d : ℕ} (A : Mat d) :
    matrixNorm A ≤ Homogenization.matNorm A := by
  simpa [matrixNorm_eq_matrixOperatorNorm, matrixFrobeniusNorm_eq_matNorm] using
    matrixOperatorNorm_le_matrixFrobeniusNorm A

theorem matNorm_le_dim_mul_matrixNorm {d : ℕ} (A : Mat d) :
    Homogenization.matNorm A ≤ (d : ℝ) * matrixNorm A := by
  simpa [matrixNorm_eq_matrixOperatorNorm, matrixFrobeniusNorm_eq_matNorm] using
    matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm A

/-- The legacy Frobenius norm is bounded by the entrywise `l¹` norm. -/
theorem matNorm_le_sum_abs_entries {d : ℕ} (A : Mat d) :
    Homogenization.matNorm A ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
  simpa [matrixFrobeniusNorm_eq_matNorm] using
    matrixFrobeniusNorm_le_sum_abs_entries A

/-- Triangle inequality for the Chapter 2 matrix norm around a center. -/
theorem matrixNorm_le_matrixNorm_add_matrixNorm_sub {d : ℕ} (A B : Mat d) :
    matrixNorm A ≤ matrixNorm B + matrixNorm (A - B) := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub A B

/-- The Chapter 2 matrix norm around a center is controlled by the entrywise
`l¹` size of the centered matrix. -/
theorem matrixNorm_le_matrixNorm_add_sum_abs_sub_entries {d : ℕ} (A B : Mat d) :
    matrixNorm A ≤ matrixNorm B + ∑ i : Fin d, ∑ j : Fin d, |A i j - B i j| := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A B

theorem coarseBMatrixNorm_nonneg {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) :
    0 ≤ coarseBMatrixNorm Q a := by
  simpa [coarseBMatrixNorm, matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_nonneg (bCoarse (cubeDomain Q) (a.coeffOn Q))

theorem coarseSigmaStarInvMatrixNorm_nonneg {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) :
    0 ≤ coarseSigmaStarInvMatrixNorm Q a := by
  simpa [coarseSigmaStarInvMatrixNorm, matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_nonneg (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))

theorem one_le_matrixNorm_one {d : ℕ} [NeZero d] :
    1 ≤ matrixNorm (1 : Mat d) := by
  simp [matrixNorm_eq_matrixOperatorNorm]

theorem matrixNorm_inv_le_of_mul_eq_one {d : ℕ} [NeZero d]
    {A B : Mat d} (hAB : A * B = 1) (hApos : 0 < matrixNorm A) :
    (matrixNorm A)⁻¹ ≤ matrixNorm B := by
  have hApos' : 0 < matrixOperatorNorm A := by
    simpa [matrixNorm_eq_matrixOperatorNorm] using hApos
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_inv_le_of_mul_eq_one hAB hApos'

theorem bCoarse_isSymm {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (bCoarse U a).IsSymm := by
  unfold bCoarse CoarseMatrices.b coarseMatrices
  exact Matrix.IsSymm.add (sigmaCoarse_isSymm U a)
    (transpose_mul_symm_mul_isSymm (kappaCoarse U a)
      (sigmaStarInvCoarse U a) (sigmaStarInvCoarse_isSymm U a))

theorem posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hBsymm : B.IsSymm)
    (hAB : MatLoewnerLE A B) :
    B.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hBsymm
  · intro x
    change 0 ≤ dotProduct x (Matrix.mulVec B x)
    have hAquad : 0 ≤ dotProduct x (Matrix.mulVec A x) :=
      hA.dotProduct_mulVec_nonneg x
    have hABx :
        (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
          (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x) := by
      simpa [vecDot, matVecMul] using! hAB x
    nlinarith

theorem bCoarse_posSemidef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (bCoarse U a).PosSemidef := by
  have hStarB : MatLoewnerLE (sigmaStarCoarse U a) (bCoarse U a) := by
    intro x
    exact le_trans ((sigmaStarCoarse_le_sigmaCoarse U a) x)
      ((sigmaCoarse_le_bCoarse U a) x)
  exact posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
    (sigmaStarCoarse_posDef U a).posSemidef (bCoarse_isSymm U a) hStarB

theorem matrixNorm_le_matNorm_of_matLoewnerLE_of_posSemidef
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matrixNorm A ≤ Homogenization.matNorm B := by
  exact le_trans (matrixNorm_le_matNorm A)
    (Homogenization.matNorm_le_of_matLoewnerLE_of_posSemidef hA hB hAB)

theorem matrixNorm_le_of_matLoewnerLE_of_posSemidef
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matrixNorm A ≤ matrixNorm B := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hA hB hAB

/-- A positive semidefinite matrix below `B` in Löwner order is controlled by
the norm of any deterministic center plus the entrywise centered size of `B`. -/
theorem matrixNorm_le_center_add_sum_abs_sub_entries_of_matLoewnerLE
    {d : ℕ} {A B center : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matrixNorm A ≤ matrixNorm center + ∑ i : Fin d, ∑ j : Fin d, |B i j - center i j| := by
  calc
    matrixNorm A ≤ matrixNorm B :=
      matrixNorm_le_of_matLoewnerLE_of_posSemidef hA hB hAB
    _ ≤ matrixNorm center + ∑ i : Fin d, ∑ j : Fin d, |B i j - center i j| :=
      matrixNorm_le_matrixNorm_add_sum_abs_sub_entries B center

theorem matrixNorm_pos_of_posDef {d : ℕ} [NeZero d] {A : Mat d}
    (hA : A.PosDef) :
    0 < matrixNorm A := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_pos_of_posDef hA

theorem vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    {d : ℕ} {A B : Mat d} (hB : B.PosSemidef)
    (hleftInv : ∀ ξ : Vec d, matVecMul B (matVecMul A ξ) = ξ) (ξ : Vec d) :
    vecNormSq ξ ≤ matrixNorm B * vecDot ξ (matVecMul A ξ) := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := A) (B := B) hB hleftInv ξ

theorem bCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (bCoarse U a).PosDef := by
  have hStarB : MatLoewnerLE (sigmaStarCoarse U a) (bCoarse U a) := by
    intro x
    exact le_trans ((sigmaStarCoarse_le_sigmaCoarse U a) x)
      ((sigmaCoarse_le_bCoarse U a) x)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using bCoarse_isSymm U a
  · intro x hx
    have hStarPos := (sigmaStarCoarse_posDef U a).dotProduct_mulVec_pos hx
    have hleHalf := hStarB x
    have hle :
        vecDot x (matVecMul (sigmaStarCoarse U a) x) ≤
          vecDot x (matVecMul (bCoarse U a) x) := by
      nlinarith
    have hmain : 0 < vecDot x (matVecMul (bCoarse U a) x) :=
      lt_of_lt_of_le
        (by
          simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hStarPos)
        hle
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hmain

theorem matrixNorm_descendantsAverageMat_le_descendantsAverage_matrixNorm
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    matrixNorm (descendantsAverageMat Q j F) ≤
      descendantsAverage Q j (fun R => matrixNorm (F R)) := by
  simpa [matrixNorm_eq_matrixOperatorNorm] using
    matrixOperatorNorm_descendantsAverageMat_le_descendantsAverage Q j F

theorem matrixNorm_descendantsAverageMat_le_finsetSupReal_matrixNorm
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    matrixNorm (descendantsAverageMat Q j F) ≤
      finsetSupReal (descendantsAtDepth Q j) (fun R => matrixNorm (F R)) := by
  calc
    matrixNorm (descendantsAverageMat Q j F) ≤
        descendantsAverage Q j (fun R => matrixNorm (F R)) :=
      matrixNorm_descendantsAverageMat_le_descendantsAverage_matrixNorm Q j F
    _ ≤ finsetSupReal (descendantsAtDepth Q j) (fun R => matrixNorm (F R)) := by
      simpa [finsetSupReal] using!
        descendantsAverage_le_finsetSsup Q j (fun R => matrixNorm (F R))

theorem finsetSupReal_eq_finsetSsup {α : Type*} (s : Finset α)
    (f : α → ℝ) :
    finsetSupReal s f = Homogenization.finsetSsup s f := by
  rfl

theorem finsetSupReal_congr {α : Type*} (s : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ s, f x = g x) :
    finsetSupReal s f = finsetSupReal s g := by
  unfold finsetSupReal
  refine congrArg sSup ?_
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hfg x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hfg x hx⟩

theorem finsetSupReal_image {α β : Type*} [DecidableEq β] (s : Finset α)
    (φ : α → β) (f : β → ℝ) (g : α → ℝ)
    (hfg : ∀ x ∈ s, f (φ x) = g x) :
    finsetSupReal (s.image φ) f = finsetSupReal s g := by
  unfold finsetSupReal
  refine congrArg sSup ?_
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hfg x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hfg x hx⟩

theorem finsetSupReal_nonneg {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ finsetSupReal s f := by
  unfold finsetSupReal
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hf x hx

theorem finsetSupReal_mono {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {f g : α → ℝ} (hfg : ∀ x ∈ s, f x ≤ g x) :
    finsetSupReal s f ≤ finsetSupReal s g := by
  unfold finsetSupReal
  have hne : (f '' (↑s : Set α)).Nonempty := by
    rcases hs with ⟨x, hx⟩
    exact ⟨f x, ⟨x, hx, rfl⟩⟩
  refine csSup_le hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hbdd : BddAbove (g '' (↑s : Set α)) :=
    ((Set.toFinite _).image g).bddAbove
  exact le_trans (hfg x hx) (le_csSup hbdd ⟨x, hx, rfl⟩)

theorem finsetSupReal_const_mul_le {α : Type*} (s : Finset α)
    (hs : s.Nonempty) {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    finsetSupReal s (fun x => c * f x) ≤ c * finsetSupReal s f := by
  unfold finsetSupReal
  have hne : ((fun x => c * f x) '' (↑s : Set α)).Nonempty := by
    rcases hs with ⟨x, hx⟩
    exact ⟨c * f x, ⟨x, hx, rfl⟩⟩
  refine csSup_le hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hbdd : BddAbove (f '' (↑s : Set α)) :=
    ((Set.toFinite _).image f).bddAbove
  exact mul_le_mul_of_nonneg_left (le_csSup hbdd ⟨x, hx, rfl⟩) hc

theorem finsetSupReal_le_of_subset {α : Type*} (s t : Finset α)
    (hs : s.Nonempty) (hst : ↑s ⊆ (↑t : Set α)) (f : α → ℝ) :
    finsetSupReal s f ≤ finsetSupReal t f := by
  unfold finsetSupReal
  have hne : (f '' (↑s : Set α)).Nonempty := by
    rcases hs with ⟨x, hx⟩
    exact ⟨f x, ⟨x, hx, rfl⟩⟩
  refine csSup_le hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hbdd : BddAbove (f '' (↑t : Set α)) :=
    ((Set.toFinite _).image f).bddAbove
  exact le_csSup hbdd ⟨x, hst hx, rfl⟩

theorem finsetSupReal_le {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {f : α → ℝ} {C : ℝ} (hC : ∀ x ∈ s, f x ≤ C) :
    finsetSupReal s f ≤ C := by
  unfold finsetSupReal
  have hne : (f '' (↑s : Set α)).Nonempty := by
    rcases hs with ⟨x, hx⟩
    exact ⟨f x, ⟨x, hx, rfl⟩⟩
  refine csSup_le hne ?_
  rintro y ⟨x, hx, rfl⟩
  exact hC x hx

theorem geometricDiscount_eq_old (s q : ℝ) :
    geometricDiscount s q = Homogenization.geometricDiscount s q := by
  rfl

theorem geometricWeight_eq_old (s q : ℝ) (n : ℕ) :
    geometricWeight s q n = Homogenization.geometricWeight s q n := by
  rfl

theorem old_descendantWeight_eq_multiscaleDescendantWeight {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (s : ℝ) :
    Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) =
      multiscaleDescendantWeight Q k s := by
  have hnatInt : (Int.toNat (Q.scale - k) : ℤ) = Q.scale - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hnatReal :
      (Int.toNat (Q.scale - k) : ℝ) = ((Q.scale - k : ℤ) : ℝ) := by
    exact_mod_cast hnatInt
  unfold multiscaleDescendantWeight
  rw [hnatReal]

theorem infinityWeight_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) :=
  Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem infinityWeight_le_one {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) ≤ 1 := by
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  nlinarith [hs, hn]

theorem infinityWeight_le_of_le {t s : ℝ} (hts : t ≤ s) (n : ℕ) :
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) ≤
      Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  nlinarith [hts, hn]

theorem infinityWeight_shift (s : ℝ) (h n : ℕ) :
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) =
      Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) *
        Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hexp :
      -2 * s * (n : ℝ) =
        2 * s * (h : ℝ) + -2 * s * ((n + h : ℕ) : ℝ) := by
    norm_num
    ring
  calc
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) =
        Real.rpow (3 : ℝ)
          (2 * s * (h : ℝ) + -2 * s * ((n + h : ℕ) : ℝ)) := by
            rw [hexp]
    _ =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) *
          Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) := by
            simpa using
              (Real.rpow_add h3 (2 * s * (h : ℝ))
                (-2 * s * ((n + h : ℕ) : ℝ)))

end

end Ch02
end Book
end Homogenization
