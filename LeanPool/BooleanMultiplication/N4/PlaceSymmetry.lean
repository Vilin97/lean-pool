/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceBridge

/-!
# Algebraic normalization of a rational place

The two nontrivial changes of variable are translation `t ↦ t + 1` and
reversal `t ↦ 1/t` on coefficient vectors.  Their substitutions on the eight
input coordinates define ANF algebra homomorphisms.  They carry the selected
rational place and its first tangent to the zero place.  No circuit states or
Boolean functions are enumerated.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Images of the eight coordinate linear forms under the identity,
translation, and reversal substitutions. -/
@[expose] def inputPlaceChange : Fin 3 → Fin 8 → LinearForm :=
  ![
    ![![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
      ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
      ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
      ![0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,1]],
    ![![1,1,1,1,0,0,0,0], ![0,1,0,1,0,0,0,0],
      ![0,0,1,1,0,0,0,0], ![0,0,0,1,0,0,0,0],
      ![0,0,0,0,1,1,1,1], ![0,0,0,0,0,1,0,1],
      ![0,0,0,0,0,0,1,1], ![0,0,0,0,0,0,0,1]],
    ![![0,0,0,1,0,0,0,0], ![0,0,1,0,0,0,0,0],
      ![0,1,0,0,0,0,0,0], ![1,0,0,0,0,0,0,0],
      ![0,0,0,0,0,0,0,1], ![0,0,0,0,0,0,1,0],
      ![0,0,0,0,0,1,0,0], ![0,0,0,0,1,0,0,0]]]

/-- Apply the input coordinate change moving the chosen rational place to zero. -/
@[expose] def normalizePlaceLinear (theta : Fin 3) (ell : LinearForm) : LinearForm :=
  ∑ i : Fin 8, ell i • inputPlaceChange theta i

/-- Permute rational-place coefficients under the chosen place normalization. -/
@[expose] def normalizeRationalCoeff
    (theta : Fin 3) (alpha : Fin 3 → F₂) : Fin 3 → F₂ :=
  ![![alpha 0, alpha 1, alpha 2],
    ![alpha 1, alpha 0, alpha 2],
    ![alpha 2, alpha 1, alpha 0]] theta

theorem normalizePlaceLinear_add
    (theta : Fin 3) (ell m : LinearForm) :
    normalizePlaceLinear theta (ell + m) =
      normalizePlaceLinear theta ell + normalizePlaceLinear theta m := by
  simp [normalizePlaceLinear, add_smul, Finset.sum_add_distrib]

theorem normalizePlaceLinear_smul
    (theta : Fin 3) (a : F₂) (ell : LinearForm) :
    normalizePlaceLinear theta (a • ell) =
      a • normalizePlaceLinear theta ell := by
  simp [normalizePlaceLinear, Finset.smul_sum, smul_smul]

theorem normalizeRationalCoeff_add
    (theta : Fin 3) (alpha beta : Fin 3 → F₂) :
    normalizeRationalCoeff theta (alpha + beta) =
      normalizeRationalCoeff theta alpha +
        normalizeRationalCoeff theta beta := by
  funext i
  fin_cases theta <;> fin_cases i <;> rfl

theorem normalizeRationalCoeff_smul
    (theta : Fin 3) (a : F₂) (alpha : Fin 3 → F₂) :
    normalizeRationalCoeff theta (a • alpha) =
      a • normalizeRationalCoeff theta alpha := by
  funext i
  fin_cases theta <;> fin_cases i <;> rfl

theorem normalizeRationalCoeff_injective (theta : Fin 3) :
    Function.Injective (normalizeRationalCoeff theta) := by
  fin_cases theta <;> decide

@[simp] theorem normalizeRationalCoeff_zero (theta : Fin 3) :
    normalizeRationalCoeff theta 0 = 0 := by
  funext i
  fin_cases theta <;> fin_cases i <;> rfl

theorem normalizeRationalCoeff_ne_zero
    (theta : Fin 3) {alpha : Fin 3 → F₂} (h : alpha ≠ 0) :
    normalizeRationalCoeff theta alpha ≠ 0 := by
  intro hzero
  apply h
  apply normalizeRationalCoeff_injective theta
  simpa using hzero

theorem normalizeRationalCoeff_ne
    (theta : Fin 3) {alpha beta : Fin 3 → F₂} (h : alpha ≠ beta) :
    normalizeRationalCoeff theta alpha ≠
      normalizeRationalCoeff theta beta := by
  intro heq
  exact h (normalizeRationalCoeff_injective theta heq)

theorem normalizeRationalCoeff_singleton_self (theta : Fin 3) :
    normalizeRationalCoeff theta (rationalSingleton theta) =
      rationalSingleton 0 := by
  fin_cases theta <;> decide

theorem anf_prod_absorb_subset
    {s t : Finset (Fin 8)} (h : t ⊆ s) (f : Fin 8 → ANF 8) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i ∈ s, f i := by
  classical
  have hs : s \ t ∪ t = s := Finset.sdiff_union_of_subset h
  have hprod :
      (∏ i ∈ s, f i) = (∏ i ∈ s \ t, f i) * ∏ i ∈ t, f i := by
    rw [← Finset.prod_union Finset.sdiff_disjoint, hs]
  rw [hprod]
  calc
    ((∏ i ∈ s \ t, f i) * ∏ i ∈ t, f i) * ∏ i ∈ t, f i =
        (∏ i ∈ s \ t, f i) *
          ((∏ i ∈ t, f i) * ∏ i ∈ t, f i) := by ac_rfl
    _ = (∏ i ∈ s \ t, f i) * ∏ i ∈ t, f i := by
      rw [anf_mul_self]

theorem anf_prod_union
    (s t : Finset (Fin 8)) (f : Fin 8 → ANF 8) :
    (∏ i ∈ s ∪ t, f i) =
      (∏ i ∈ s, f i) * ∏ i ∈ t, f i := by
  classical
  calc
    (∏ i ∈ s ∪ t, f i) =
        (∏ i ∈ s ∪ t, f i) * ∏ i ∈ s ∩ t, f i :=
      (anf_prod_absorb_subset (by intro i hi; simp_all) f).symm
    _ = (∏ i ∈ s, f i) * ∏ i ∈ t, f i :=
      Finset.prod_union_inter

/-- Substitute the normalized linear inputs into a squarefree monomial. -/
@[expose]
def placeSubstitutionMonoid (theta : Fin 3) : Monomial 8 →* ANF 8 where
  toFun s := ∏ i ∈ s.vars, linearANF (inputPlaceChange theta i)
  map_one' := by simp
  map_mul' s t := by
    exact anf_prod_union s.vars t.vars
      (fun i => linearANF (inputPlaceChange theta i))

/-- The Boolean ANF algebra homomorphism induced by a rational-place normalization. -/
def anfPlaceNormalize (theta : Fin 3) : ANF 8 →ₐ[F₂] ANF 8 :=
  MonoidAlgebra.lift F₂ (ANF 8) (Monomial 8)
    (placeSubstitutionMonoid theta)

@[simp] theorem anfPlaceNormalize_monomial
    (theta : Fin 3) (s : Finset (Fin 8)) :
    anfPlaceNormalize theta (monomial s) =
      ∏ i ∈ s, linearANF (inputPlaceChange theta i) := by
  simp [anfPlaceNormalize, monomial, placeSubstitutionMonoid, MonoidAlgebra.lift_apply]

@[simp] theorem anfPlaceNormalize_X (theta : Fin 3) (i : Fin 8) :
    anfPlaceNormalize theta (X i) =
      linearANF (inputPlaceChange theta i) := by
  simp [X]

/-- Convert a coefficient vector to its linear ANF, as a linear map. -/
@[expose]
def linearANFMap : LinearForm →ₗ[F₂] ANF 8 where
  toFun := linearANF
  map_add' := linearANF_add
  map_smul' := linearANF_smul

@[simp] theorem linearANFMap_apply (ell : LinearForm) :
    linearANFMap ell = linearANF ell := rfl

theorem anfPlaceNormalize_linearANF
    (theta : Fin 3) (ell : LinearForm) :
    anfPlaceNormalize theta (linearANF ell) =
      linearANF (normalizePlaceLinear theta ell) := by
  calc
    anfPlaceNormalize theta (linearANF ell) =
        ∑ i : Fin 8, ell i •
          linearANF (inputPlaceChange theta i) := by
      rw [linearANF, map_sum]
      simp only [map_smul, anfPlaceNormalize_X]
    _ = linearANFMap
        (∑ i : Fin 8, ell i • inputPlaceChange theta i) := by
      rw [map_sum]
      simp only [map_smul, linearANFMap_apply]
    _ = linearANF (normalizePlaceLinear theta ell) := rfl

theorem anfPlaceNormalize_affineANF
    (theta : Fin 3) (a : F₂) (ell : LinearForm) :
    anfPlaceNormalize theta (affineANF a ell) =
      affineANF a (normalizePlaceLinear theta ell) := by
  rw [affineANF, map_add, map_smul, map_one,
    anfPlaceNormalize_linearANF, affineANF]

/-- The permutation exchanging the chosen rational place with zero. -/
def normalizePlaceIndex : Fin 3 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![1, 0, 2], ![2, 1, 0]]

theorem normalizePlaceLinear_placeA (theta k : Fin 3) :
    normalizePlaceLinear theta (placeA k) =
      placeA (normalizePlaceIndex theta k) := by
  fin_cases theta <;> fin_cases k <;> decide

theorem normalizePlaceLinear_placeB (theta k : Fin 3) :
    normalizePlaceLinear theta (placeB k) =
      placeB (normalizePlaceIndex theta k) := by
  fin_cases theta <;> fin_cases k <;> decide

theorem anfPlaceNormalize_rationalPlaceANF (theta k : Fin 3) :
    anfPlaceNormalize theta (targetANF (rationalPlaceCoeff k)) =
      targetANF (rationalPlaceCoeff (normalizePlaceIndex theta k)) := by
  rw [rationalPlaceANF_direct, map_mul,
    anfPlaceNormalize_linearANF, anfPlaceNormalize_linearANF,
    normalizePlaceLinear_placeA, normalizePlaceLinear_placeB,
    ← rationalPlaceANF_direct]

theorem anfPlaceNormalize_rationalANF
    (theta : Fin 3) (alpha : Fin 3 → F₂) :
    anfPlaceNormalize theta (rationalANF alpha) =
      rationalANF (normalizeRationalCoeff theta alpha) := by
  rw [rationalANF_eq_sum, map_sum]
  simp_rw [map_smul, anfPlaceNormalize_rationalPlaceANF]
  rw [rationalANF_eq_sum]
  fin_cases theta <;>
    simp [Fin.sum_univ_succ, normalizePlaceIndex, normalizeRationalCoeff] <;> module

theorem anfPlaceNormalize_representedLowFactor
    (theta : Fin 3) (a : F₂) (ell : LinearForm)
    (alpha : Fin 3 → F₂) :
    anfPlaceNormalize theta (representedLowFactor a ell alpha) =
      representedLowFactor a (normalizePlaceLinear theta ell)
        (normalizeRationalCoeff theta alpha) := by
  rw [representedLowFactor, map_add,
    anfPlaceNormalize_affineANF, anfPlaceNormalize_rationalANF,
    representedLowFactor]

theorem aVar_four_eq_X_aCoord (i : Fin 4) :
    aVar 4 i = X (aCoord i) := by
  congr 1

theorem bVar_four_eq_X_bCoord (i : Fin 4) :
    bVar 4 i = X (bCoord i) := by
  congr 1

@[simp] theorem aVar_mul_bVar_eq_targetPair (i j : Fin 4) :
    aVar 4 i * bVar 4 j = monomial (targetPair i j) := by
  rw [aVar_four_eq_X_aCoord, bVar_four_eq_X_bCoord]
  simp [X, targetPair]

theorem targetANF_eq_bilinear_sum (c : TargetCoeff) :
    targetANF c =
      ∑ i : Fin 4, ∑ j : Fin 4,
        c (hankelIndex i j) • (aVar 4 i * bVar 4 j) := by
  simpa only [aVar_mul_bVar_eq_targetPair] using
    targetANF_eq_double_sum c

@[simp] theorem anfPlaceNormalize_aVar
    (theta : Fin 3) (i : Fin 4) :
    anfPlaceNormalize theta (aVar 4 i) =
      linearANF (inputPlaceChange theta (aCoord i)) := by
  rw [aVar_four_eq_X_aCoord, anfPlaceNormalize_X]

@[simp] theorem anfPlaceNormalize_bVar
    (theta : Fin 3) (i : Fin 4) :
    anfPlaceNormalize theta (bVar 4 i) =
      linearANF (inputPlaceChange theta (bCoord i)) := by
  rw [bVar_four_eq_X_bCoord, anfPlaceNormalize_X]

theorem anfPlaceNormalize_tangent_self
    (theta : Fin 3) (eps : F₂) :
    anfPlaceNormalize theta (targetANF (rationalTangentAt theta eps)) =
      targetANF (rationalTangentAt 0 eps) := by
  have htwo : (2 : ANF 8) = 0 := by
    simp
  have hfour : (4 : ANF 8) = 0 := by
    calc
      (4 : ANF 8) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  have hthree : (3 : ANF 8) = 1 := by
    calc
      (3 : ANF 8) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; simp
  have hseven : (7 : ANF 8) = 1 := by
    calc
      (7 : ANF 8) = 4 + 2 + 1 := by norm_num
      _ = 1 := by rw [hfour, htwo]; simp
  have height : (8 : ANF 8) = 0 := by
    calc
      (8 : ANF 8) = 4 + 4 := by norm_num
      _ = 0 := by rw [hfour]; simp
  rw [targetANF_eq_bilinear_sum, map_sum]
  simp_rw [map_sum, map_smul, map_mul,
    anfPlaceNormalize_aVar, anfPlaceNormalize_bVar]
  rw [targetANF_eq_bilinear_sum]
  fin_cases theta <;> rcases f2_eq_zero_or_one eps with rfl | rfl <;>
    simp [rationalTangentAt, hankelIndex, Fin.sum_univ_succ, inputPlaceChange, linearANF,
      aVar, bVar, X, aCoord, bCoord, monomial_mul] <;>
    ring_nf <;>
    simp [htwo, hfour, hseven, height, monomial_mul];
    ring_nf;
    simp [htwo, hfour, height, N3Certificate.two_eq_zero_f2]

end

end N4
end UnrestrictedBooleanMul
