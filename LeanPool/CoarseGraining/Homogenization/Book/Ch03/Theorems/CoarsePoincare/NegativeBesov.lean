/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-! # Negative Besov -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.1.1: Coarse Poincare negative-Besov bridges

This file contains the negative-Besov normalization and pointwise coefficient
bridges used by the public coarse Poincare theorem package.
-/

noncomputable section

open scoped BigOperators

theorem negativeBesovVectorDepthAverage_eq_old {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j =
      Homogenization.cubeBesovNegativeVectorDepthAverage Q F j := by
  rfl

theorem negativeBesovVectorDepthSeminorm_eq_old {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negativeBesovVectorDepthSeminorm Q s F j =
      Homogenization.cubeBesovNegativeVectorDepthSeminorm Q s F j := by
  simp [negativeBesovVectorDepthSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthSeminorm,
    negativeBesovVectorDepthAverage_eq_old]

theorem negativeBesovVectorDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ negativeBesovVectorDepthAverage Q F j := by
  simpa [negativeBesovVectorDepthAverage_eq_old] using
    Homogenization.cubeBesovNegativeVectorDepthAverage_nonneg Q F j

theorem negativeBesovVectorDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ negativeBesovVectorDepthSeminorm Q s F j := by
  unfold negativeBesovVectorDepthSeminorm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem negativeBesovVectorPartialNormFinite_nonneg {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    0 ≤ negativeBesovVectorPartialNormFinite Q s q N F := by
  unfold negativeBesovVectorPartialNormFinite
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (negativeBesovVectorDepthSeminorm_nonneg Q s F j) _)
    _

theorem scaleNormalizedNegativeBesovVectorNorm_finite_le_of_partialBound
    {d : ℕ} (Q : TriadicCube d) (s q : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, negativeBesovVectorPartialNormFinite Q s q N F ≤ B) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤ B := by
  unfold scaleNormalizedNegativeBesovVectorNorm
  refine csSup_le ?_ ?_
  · exact ⟨negativeBesovVectorPartialNormFinite Q s q 0 F, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_depthBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ j : ℕ, negativeBesovVectorDepthSeminorm Q s F j ≤ B) :
    scaleNormalizedNegativeBesovVectorNorm Q s .infinity F ≤ B := by
  unfold scaleNormalizedNegativeBesovVectorNorm
  refine csSup_le ?_ ?_
  · exact ⟨negativeBesovVectorDepthSeminorm Q s F 0, ⟨0, rfl⟩⟩
  · rintro x ⟨j, rfl⟩
    exact hB j

theorem negativeBesovVectorDepthAverage_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j =
      negativeBesovVectorDepthAverage Q G j := by
  simp [negativeBesovVectorDepthAverage_eq_old,
    Homogenization.cubeBesovNegativeVectorDepthAverage_eq_of_ae_eq_on_cubeSet hFG j]

theorem negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s : ℝ) (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) (j : ℕ) :
    negativeBesovVectorDepthSeminorm Q s F j =
      negativeBesovVectorDepthSeminorm Q s G j := by
  unfold negativeBesovVectorDepthSeminorm
  rw [negativeBesovVectorDepthAverage_eq_of_ae_eq_on_cubeSet hFG j]

theorem negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s q : ℝ) (N : ℕ)
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) :
    negativeBesovVectorPartialNormFinite Q s q N F =
      negativeBesovVectorPartialNormFinite Q s q N G := by
  unfold negativeBesovVectorPartialNormFinite
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet s hFG j]

theorem scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s : ℝ) (q : Ch02.MultiscaleExponent)
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) :
    scaleNormalizedNegativeBesovVectorNorm Q s q F =
      scaleNormalizedNegativeBesovVectorNorm Q s q G := by
  cases q with
  | finite q =>
      unfold scaleNormalizedNegativeBesovVectorNorm
      apply congrArg sSup
      ext y
      constructor
      · rintro ⟨N, rfl⟩
        exact ⟨N,
          (negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s q N hFG).symm⟩
      · rintro ⟨N, rfl⟩
        exact ⟨N,
          negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s q N hFG⟩
  | infinity =>
      unfold scaleNormalizedNegativeBesovVectorNorm
      apply congrArg sSup
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j,
          (negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s hFG j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j,
          negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s hFG j⟩

theorem negativeBesovVectorDepthAverage_le_publicSigmaStarInvEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (a : CoeffFamily d)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R F) ≤
          Ch02.coarseSigmaStarInvMatrixNorm R a * cubeAverage R energy)
    (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j ≤
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
        cubeAverage Q energy := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R F) ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hRscale_eq : R.scale = Q.scale - (j : ℤ) :=
      Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hRscale
    have hlR : Q.scale - (j : ℤ) ≤ R.scale := by
      rw [hRscale_eq]
    have hcoarse_le :
        Ch02.coarseSigmaStarInvMatrixNorm R a ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a :=
      (Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
        R hlR a).trans
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale
          a hRscale hlR)
    have havg_nonneg : 0 ≤ cubeAverage R energy := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    exact le_trans (hlocal j R hR) <|
      mul_le_mul_of_nonneg_right hcoarse_le havg_nonneg
  have hdesc :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hconst :
      descendantsAverage Q j (fun R =>
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy) =
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
          descendantsAverage Q j (fun R => cubeAverage R energy) := by
    let D := descendantsAtDepth Q j
    let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) a
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) * Finset.sum D (fun R => M * cubeAverage R energy) =
          Finset.sum D (fun R => (((D.card : ℝ)⁻¹ * M) * cubeAverage R energy)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro R hR
            ring
      _ = (((D.card : ℝ)⁻¹ * M) * Finset.sum D (fun R => cubeAverage R energy)) := by
            simpa [mul_assoc] using
              (Finset.mul_sum (s := D) (f := fun R => cubeAverage R energy)
                (((D.card : ℝ)⁻¹) * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) * Finset.sum D (fun R => cubeAverage R energy)) := by
            ring
  rw [hconst, havg_eq] at hdesc
  simpa [negativeBesovVectorDepthAverage_eq_old,
    Homogenization.cubeBesovNegativeVectorDepthAverage] using hdesc

theorem negativeBesovVectorDepthAverage_le_publicBEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (a : CoeffFamily d)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R F) ≤
          Ch02.coarseBMatrixNorm R a * cubeAverage R energy)
    (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j ≤
      Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
        cubeAverage Q energy := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R F) ≤
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hRscale_eq : R.scale = Q.scale - (j : ℤ) :=
      Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hRscale
    have hlR : Q.scale - (j : ℤ) ≤ R.scale := by
      rw [hRscale_eq]
    have hcoarse_le :
        Ch02.coarseBMatrixNorm R a ≤
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a :=
      (Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale
        R hlR a).trans
        (Ch02.maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale
          a hRscale hlR)
    have havg_nonneg : 0 ≤ cubeAverage R energy := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    exact le_trans (hlocal j R hR) <|
      mul_le_mul_of_nonneg_right hcoarse_le havg_nonneg
  have hdesc :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hconst :
      descendantsAverage Q j (fun R =>
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy) =
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a *
          descendantsAverage Q j (fun R => cubeAverage R energy) := by
    let D := descendantsAtDepth Q j
    let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) a
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) * Finset.sum D (fun R => M * cubeAverage R energy) =
          Finset.sum D (fun R => (((D.card : ℝ)⁻¹ * M) * cubeAverage R energy)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro R hR
            ring
      _ = (((D.card : ℝ)⁻¹ * M) * Finset.sum D (fun R => cubeAverage R energy)) := by
            simpa [mul_assoc] using
              (Finset.mul_sum (s := D) (f := fun R => cubeAverage R energy)
                (((D.card : ℝ)⁻¹) * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) * Finset.sum D (fun R => cubeAverage R energy)) := by
            ring
  rw [hconst, havg_eq] at hdesc
  simpa [negativeBesovVectorDepthAverage_eq_old,
    Homogenization.cubeBesovNegativeVectorDepthAverage] using hdesc

theorem pointwiseCoeffField_isEllipticFieldOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (aQ : Ch02.CoeffOn (Ch02.cubeDomain Q)) :
    IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet Q)
      (Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) aQ) := by
  classical
  have hmeas :
      Measurable
        (fun x i j =>
          if x ∈ cubeSet Q then
            Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) aQ x i j
          else 0) := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    have hcoeff :
        Measurable fun x : Vec d =>
          Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) aQ x i j := by
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (Internal.Ch02.BookCh02.pointwiseCoeffField_measurable (Ch02.cubeDomain Q) aQ) i) j)
    exact Measurable.ite (measurableSet_cubeSet Q) hcoeff measurable_const
  refine ⟨hmeas, ?_⟩
  intro x _hxQ
  by_cases hxGood : x ∈ (Internal.Ch02.BookCh02.goodSetData (Ch02.cubeDomain Q) aQ).set
  · simpa [Internal.Ch02.BookCh02.pointwiseCoeffField, hxGood] using
      (Internal.Ch02.BookCh02.goodSetData (Ch02.cubeDomain Q) aQ).elliptic x hxGood
  · simpa [Internal.Ch02.BookCh02.pointwiseCoeffField, hxGood] using
      Internal.Ch02.BookCh02.isEllipticMatrix_smul_one
        (d := d) aQ.lam_pos aQ.lam_le_Lam


end

end Ch03
end Book
end Homogenization
