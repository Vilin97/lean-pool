/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceGeometry

/-!
# The feedback factor at a zero-place tangent

Right idempotence for a target tangent at the rational place zero forces the
linear part of the rational feedback factor to use only the two anchor
variables.  Thus the factor has the manuscript form
`δ + ρ x + σ y + x y`.  The proof uses only the cubic homogeneous
projection and six explicit exterior coordinates.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem rZeroCoeff_eq_targetBasis_zero :
    rZeroCoeff = targetBasis 0 := by
  funext i
  fin_cases i <;> simp [rZeroCoeff, targetBasis, Pi.basisFun]

theorem rationalCoeffRep_singleton_zero :
    rationalCoeffRep (rationalSingleton 0) = rZeroCoeff := by
  funext i
  fin_cases i <;>
    simp [rationalCoeffRep, rationalSingleton, rZeroCoeff, rOneCoeff, rInfinityCoeff]

theorem rationalTwo_singleton_zero :
    rationalTwo (rationalSingleton 0) = zeroPlaceTwo := by
  calc
    rationalTwo (rationalSingleton 0) =
        targetTwo (rationalCoeffRep (rationalSingleton 0)) :=
      (targetTwo_rationalCoeffRep _).symm
    _ = zeroPlaceTwo := by
      rw [rationalCoeffRep_singleton_zero,
        rZeroCoeff_eq_targetBasis_zero]
      exact targetTwo_basis_zero

theorem targetTwo_zero_tangent (eps : F₂) :
    targetTwo (rationalTangentAt 0 eps) =
      eps • zeroPlaceTwo + zeroFirstJetTwo := by
  rcases f2_eq_zero_or_one eps with rfl | rfl <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rationalTangentAt, targetTwo, zeroPlaceTwo, zeroFirstJetTwo, vectorWedge, aLinear,
      bLinear, aCoord, bCoord, Pi.basisFun]

theorem targetANF_targetBasis_feedback (s : Fin 7) :
    targetANF (targetBasis s) = Mul 4 s := by
  simp [targetANF, targetBasis_apply]

theorem targetANF_zero_tangent (eps : F₂) :
    targetANF (rationalTangentAt 0 eps) =
      eps • Mul 4 0 + Mul 4 1 := by
  have hcoeff : rationalTangentAt 0 eps =
      eps • targetBasis 0 + targetBasis 1 := by
    funext i
    fin_cases i <;>
      simp [rationalTangentAt, targetBasis, Pi.basisFun]
  change targetANFLinear (rationalTangentAt 0 eps) = _
  rw [hcoeff, map_add, map_smul]
  simp only [targetANFLinear_apply, targetANF_targetBasis_feedback]

theorem rationalANF_singleton_zero :
    rationalANF (rationalSingleton 0) = Mul 4 0 := by
  change targetANF (rationalCoeffRep (rationalSingleton 0)) = _
  rw [rationalCoeffRep_singleton_zero,
    rZeroCoeff_eq_targetBasis_zero]
  exact targetANF_targetBasis_feedback 0

theorem mul_target_one_zero :
    Mul 4 1 * Mul 4 0 =
      monomial ({0, 4, 5} : Finset (Fin 8)) +
        monomial ({0, 1, 4} : Finset (Fin 8)) := by
  simp (disch := decide) only [Nat.reduceMul, Mul, mulCoefficient, Nat.add_one_sub_one,
    Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, aVar, X, bVar, monomial_mul,
    Finset.singleton_union, Fin.sum_univ_succ, Nat.zero_mod, add_zero, Fin.reduceFinMk,
    Fin.val_succ, zero_add, Nat.add_eq_right, Fin.val_eq_zero_iff, Nat.reduceAdd,
    Nat.reduceEqDiff, ↓reduceIte, Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero,
    Finset.sum_const_zero, zero_ne_one, Fin.zero_eta, Fin.succ_ne_zero, Finset.sum_ite_eq',
    Finset.mem_univ, Fin.mk_one, Nat.add_eq_zero_iff, and_true, and_false]
  rw [add_mul]
  simp only [Fin.isValue, monomial_mul, Finset.union_insert, Finset.insert_union,
    Finset.singleton_union, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton,
    or_self, or_false, Finset.insert_eq_of_mem, Finset.union_idempotent, add_left_inj]
  congr 1
  decide

theorem aLinear_eq_coordinateLinear (i : Fin 4) :
    aLinear i = coordinateLinear (aCoord i) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [aLinear, coordinateLinear, aCoord, Pi.basisFun]

theorem bLinear_eq_coordinateLinear (i : Fin 4) :
    bLinear i = coordinateLinear (bCoord i) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [bLinear, coordinateLinear, bCoord, Pi.basisFun]

theorem zero_tangent_cubic_coordinate_form :
    monomialThree ({0, 4, 5} : Finset (Fin 8)) +
        monomialThree ({0, 1, 4} : Finset (Fin 8)) =
      vectorWedgeTwo (sliceU + sliceV) zeroPlaceTwo := by
  change _ = vectorWedgeTwo (aLinear 1 + bLinear 1)
    (vectorWedge (aLinear 0) (bLinear 0))
  rw [aLinear_eq_coordinateLinear, aLinear_eq_coordinateLinear,
    bLinear_eq_coordinateLinear, bLinear_eq_coordinateLinear]
  decide

/-- The only cubic terms in tangent times anchor-place are `x y u` and
`x y v`. -/
theorem anfThreeProjection_zero_tangent_mul_singleton
    (eps : F₂) :
    anfThreeProjection
        (targetANF (rationalTangentAt 0 eps) *
          rationalANF (rationalSingleton 0)) =
      vectorWedgeTwo (sliceU + sliceV) zeroPlaceTwo := by
  rw [targetANF_zero_tangent, rationalANF_singleton_zero, add_mul,
    map_add]
  simp only [smul_mul_assoc, map_smul]
  have hself : anfThreeProjection (Mul 4 0 * Mul 4 0) = 0 := by
    rw [anf_mul_self]
    apply anfThreeProjection_eq_zero_of_mem_targetAmbient
    rw [← targetANF_targetBasis_feedback]
    exact Submodule.mem_sup_right (targetANF_mem_mulTarget _)
  rw [hself, smul_zero, zero_add, mul_target_one_zero]
  simp only [map_add, anfThreeProjection_monomial]
  exact zero_tangent_cubic_coordinate_form

/-- Cubic form of right idempotence at the zero rational place. -/
theorem zero_tangent_right_idempotence_cubic
    {F factor : ANF 8}
    {targetConst factorConst eps : F₂}
    {targetLinear factorLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactorRep : factor =
      affineANF factorConst factorLinear +
        rationalANF (rationalSingleton 0))
    (hright : F * factor = F) :
    vectorWedgeTwo factorLinear
          (eps • zeroPlaceTwo + zeroFirstJetTwo) +
        vectorWedgeTwo targetLinear zeroPlaceTwo +
        vectorWedgeTwo (sliceU + sliceV) zeroPlaceTwo = 0 := by
  have hproj := congrArg anfThreeProjection hright
  rw [hFRep, hfactorRep] at hproj
  simp only [add_mul, mul_add, map_add, anfThreeProjection_affine_mul_affine,
    anfThreeProjection_affine_mul_rational, anfThreeProjection_target_mul_affine,
    anfThreeProjection_zero_tangent_mul_singleton, rationalTwo_singleton_zero,
    targetTwo_zero_tangent, zero_add] at hproj
  have hrightZero :
      anfThreeProjection
        (affineANF targetConst targetLinear +
          targetANF (rationalTangentAt 0 eps)) = 0 := by
    apply anfThreeProjection_eq_zero_of_mem_targetAmbient
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (affineANF_mem _ _))
      (Submodule.mem_sup_right (targetANF_mem_mulTarget _))
  have hrightExpanded :
      anfThreeProjection (affineANF targetConst targetLinear) +
        anfThreeProjection (targetANF (rationalTangentAt 0 eps)) = 0 := by
    simpa only [map_add] using hrightZero
  rw [hrightExpanded] at hproj
  simpa [add_assoc] using hproj

/-- The six complementary coordinates of the feedback linear form vanish. -/
theorem factorLinear_mem_anchor_plane
    {F factor : ANF 8}
    {targetConst factorConst eps : F₂}
    {targetLinear factorLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactorRep : factor =
      affineANF factorConst factorLinear +
        rationalANF (rationalSingleton 0))
    (hright : F * factor = F) :
    ∃ rho sigma : F₂,
      factorLinear = rho • sliceX + sigma • sliceY := by
  have hcubic := zero_tangent_right_idempotence_cubic
    hFRep hfactorRep hright
  have h1 := congrFun (congrFun (congrFun hcubic 1) 0) 5
  have h2 := congrFun (congrFun (congrFun hcubic 2) 0) 5
  have h3 := congrFun (congrFun (congrFun hcubic 3) 0) 5
  have h5 := congrFun (congrFun (congrFun hcubic 5) 1) 4
  have h6 := congrFun (congrFun (congrFun hcubic 6) 1) 4
  have h7 := congrFun (congrFun (congrFun hcubic 7) 1) 4
  simp [zeroFirstJetTwo, zeroPlaceTwo, sliceU, sliceV, vectorWedgeTwo, vectorWedge, aLinear,
    bLinear, aCoord, bCoord, Pi.basisFun] at h1 h2 h3 h5 h6 h7
  refine ⟨factorLinear 0, factorLinear 4, ?_⟩
  funext i
  fin_cases i
  · simp [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun]
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h1
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h2
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h3
  · simp [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun]
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h5
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h6
  · simpa [sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] using h7

/-- The affine perturbations of the zero-place product supported on its two inputs. -/
@[expose]
def ZeroPlaceFeedbackForm (factor : ANF 8) : Prop :=
  ∃ delta rho sigma : F₂,
    factor = affineANF delta (rho • sliceX + sigma • sliceY) +
      rationalANF (rationalSingleton 0)

/-- ANF-level feedback normal form `δ + ρx + σy + xy`. -/
theorem zeroPlaceFeedbackForm_of_right_idempotence
    {F factor : ANF 8}
    {targetConst factorConst eps : F₂}
    {targetLinear factorLinear : LinearForm}
    (hFRep : F =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactorRep : factor =
      affineANF factorConst factorLinear +
        rationalANF (rationalSingleton 0))
    (hright : F * factor = F) :
    ZeroPlaceFeedbackForm factor := by
  rcases factorLinear_mem_anchor_plane hFRep hfactorRep hright with
    ⟨rho, sigma, hlinear⟩
  exact ⟨factorConst, rho, sigma, by rw [hfactorRep, hlinear]⟩

end

end N4
end UnrestrictedBooleanMul
