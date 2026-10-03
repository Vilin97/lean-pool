/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SexticPlane

/-!
# Cubic projection against an arbitrary Hankel target

This extends the rational-place cubic bridge to every coefficient in the
seven-dimensional Hankel target.  It is used only for the `D = 0` branch of
quartic exclusion.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Cubic part of an input variable times an arbitrary product target. -/
def cubicTargetModel (r : Fin 8) (c : TargetCoeff) : ThreeForm :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    c (hankelIndex i j) • monomialThree ({r} ∪ targetPair i j)

private theorem cubicTargetModel_eq :
    ∀ (r : Fin 8) (c : TargetCoeff),
      cubicTargetModel r c =
        vectorWedgeTwo (coordinateLinear r) (targetTwo c) := by
  intro r c
  rw [targetTwo_eq_double_wedge]
  change cubicTargetModel r c =
    vectorWedgeTwoBilinear (coordinateLinear r)
      (∑ i : Fin 4, ∑ j : Fin 4, c (hankelIndex i j) •
        vectorWedge (coordinateLinear (aCoord i))
          (coordinateLinear (bCoord j)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, monomialThree_union_targetPair]
  rfl

private theorem anfThreeProjection_X_target
    (r : Fin 8) (c : TargetCoeff) :
    anfThreeProjection (X r * targetANF c) =
      vectorWedgeTwo (coordinateLinear r) (targetTwo c) := by
  rw [targetANF_eq_double_sum]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, X, monomial_mul,
    anfThreeProjection_monomial]
  exact cubicTargetModel_eq r c

/-- Multiplying a linear ANF by a target quadratic has cubic part given by
the vector--two-form exterior product. -/
theorem anfThreeProjection_linear_mul_target
    (ell : LinearForm) (c : TargetCoeff) :
    anfThreeProjection (linearANF ell * targetANF c) =
      vectorWedgeTwo ell (targetTwo c) := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, anfThreeProjection_X_target]
  change (∑ i : Fin 8, ell i •
      vectorWedgeTwo (coordinateLinear i) (targetTwo c)) = _
  change _ = vectorWedgeTwoBilinear ell (targetTwo c)
  symm
  calc
    vectorWedgeTwoBilinear ell (targetTwo c) =
        vectorWedgeTwoBilinear
          (∑ i : Fin 8, ell i • coordinateLinear i) (targetTwo c) := by
      rw [← linear_eq_sum_coordinate ell]
    _ = ∑ i : Fin 8, ell i •
        vectorWedgeTwo (coordinateLinear i) (targetTwo c) := by
      simp only [map_sum, map_smul]
      rfl

theorem anfThreeProjection_target_mul_affine
    (c : TargetCoeff) (a : F₂) (ell : LinearForm) :
    anfThreeProjection (targetANF c * affineANF a ell) =
      vectorWedgeTwo ell (targetTwo c) := by
  rw [mul_comm, affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfThreeProjection_linear_mul_target]
  have htarget : anfThreeProjection (targetANF c) = 0 :=
    anfThreeProjection_eq_zero_of_mem_targetAmbient
      (Submodule.mem_sup_right (targetANF_mem_mulTarget c))
  rw [htarget]
  simp

theorem anfThreeProjection_targetRep_mul_affine
    (A b : F₂) (ell m : LinearForm) (c : TargetCoeff) :
    anfThreeProjection
        ((affineANF A ell + targetANF c) * affineANF b m) =
      vectorWedgeTwo m (targetTwo c) := by
  rw [add_mul, map_add, anfThreeProjection_affine_mul_affine,
    anfThreeProjection_target_mul_affine, zero_add]

/-- A nonrational Hankel target has no nonzero vector annihilator.  Otherwise
the target two-form would be decomposable and hence one of the three rational
rank-one places. -/
theorem nonrational_target_vectorWedge_injective
    {c : TargetCoeff} (hc : ¬ IsRationalCoeff c)
    {ell : LinearForm}
    (h : vectorWedgeTwo ell (targetTwo c) = 0) : ell = 0 := by
  by_contra hell
  have hN : vectorWedgeTwoN ell (targetTwo c) = 0 := by
    funext i j k
    have hijk := congrFun (congrFun (congrFun h i) j) k
    simpa [vectorWedgeTwoN, vectorWedgeTwo] using hijk
  rcases decomposable_of_vectorWedgeTwoN_zero ell (targetTwo c) hell hN with
    ⟨v, hv⟩
  have hv' : targetTwo c = vectorWedge ell v := by
    funext i j
    have hij := congrFun (congrFun hv i) j
    simpa [vectorWedgeN, vectorWedge] using hij
  have hdecomp : IsDecomposableTwo (targetTwo c) := ⟨ell, v, hv'⟩
  have hcne : c ≠ 0 := by
    intro hzero
    apply hc
    subst c
    exact ⟨0, 0, 0, by simp⟩
  rcases decomposableTarget_classification
      (targetTwo_decomposableTarget hdecomp) hcne with hzero | hone | hinfinity
  · apply hc
    rw [hzero]
    exact ⟨1, 0, 0, by simp⟩
  · apply hc
    rw [hone]
    exact ⟨0, 1, 0, by simp⟩
  · apply hc
    rw [hinfinity]
    exact ⟨0, 0, 1, by simp⟩

/-- A seed outside the target ambient forces every seed-using factor to have
a nonzero rational quadratic coefficient. -/
theorem seedUsing_factorCoeff_ne_zero_of_not_mem_targetAmbient
    {g correction factor target : ANF 8}
    {targetConst factorConst : F₂}
    {targetLinear factorLinear : LinearForm}
    {targetCoeff : TargetCoeff} {factorCoeff : Fin 3 → F₂}
    (hseed : g ∉ targetAmbient 8 (mulTarget 4))
    (hcorrection : correction ∈ rationalLowSpace)
    (htargetEq : target = (g + correction) * factor)
    (htargetMem : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetNotLow : target ∉ rationalLowSpace)
    (htargetRep : target =
      affineANF targetConst targetLinear + targetANF targetCoeff)
    (hfactorRep : factor =
      affineANF factorConst factorLinear + rationalANF factorCoeff)
    (htargetNonrational : ¬ IsRationalCoeff targetCoeff)
    (hright : target * factor = target) : factorCoeff ≠ 0 := by
  intro hfactorCoeff
  subst factorCoeff
  have hfactorAffine : factor = affineANF factorConst factorLinear := by
    simpa using hfactorRep
  have hcubic :
      vectorWedgeTwo factorLinear (targetTwo targetCoeff) = 0 := by
    have hleft := congrArg anfThreeProjection hright
    rw [htargetRep, hfactorAffine,
      anfThreeProjection_targetRep_mul_affine] at hleft
    have htargetCubic : anfThreeProjection target = 0 :=
      anfThreeProjection_eq_zero_of_mem_targetAmbient htargetMem
    have htargetRepCubic :
        anfThreeProjection
          (affineANF targetConst targetLinear + targetANF targetCoeff) = 0 := by
      rw [← htargetRep]
      exact htargetCubic
    exact hleft.trans htargetRepCubic
  have hlinear : factorLinear = 0 :=
    nonrational_target_vectorWedge_injective htargetNonrational hcubic
  subst factorLinear
  have hfactorConst : factorConst = 1 := by
    rcases f2_eq_zero_or_one factorConst with hzero | hone
    · exfalso
      have htargetZero : target = 0 := by
        have hfactorZero : factor = 0 := by
          rw [hfactorAffine, hzero]
          simp [affineANF]
        rw [hfactorZero, mul_zero] at hright
        exact hright.symm
      apply htargetNotLow
      rw [htargetZero]
      exact Submodule.zero_mem _
    · exact hone
  have hfactorOne : factor = 1 := by
    rw [hfactorAffine, hfactorConst]
    simp [affineANF]
  have htargetSeed : target = g + correction := by
    rw [htargetEq, hfactorOne, mul_one]
  have hgAmbient : g ∈ targetAmbient 8 (mulTarget 4) := by
    have hcorrAmbient := rationalLowSpace_le_targetAmbient hcorrection
    have hsum := Submodule.add_mem _ htargetMem hcorrAmbient
    rw [htargetSeed] at hsum
    simpa [add_assoc] using hsum
  exact hseed hgAmbient

/-- Quartic specialization of the ambient-space obstruction. -/
theorem seedUsing_factorCoeff_ne_zero
    {g correction factor target : ANF 8}
    {targetConst factorConst : F₂}
    {targetLinear factorLinear : LinearForm}
    {targetCoeff : TargetCoeff} {factorCoeff : Fin 3 → F₂}
    (hquartic : quarticProbeANF g ≠ 0)
    (hcorrection : correction ∈ rationalLowSpace)
    (htargetEq : target = (g + correction) * factor)
    (htargetMem : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetNotLow : target ∉ rationalLowSpace)
    (htargetRep : target =
      affineANF targetConst targetLinear + targetANF targetCoeff)
    (hfactorRep : factor =
      affineANF factorConst factorLinear + rationalANF factorCoeff)
    (htargetNonrational : ¬ IsRationalCoeff targetCoeff)
    (hright : target * factor = target) : factorCoeff ≠ 0 := by
  apply seedUsing_factorCoeff_ne_zero_of_not_mem_targetAmbient ?_
    hcorrection htargetEq htargetMem htargetNotLow htargetRep hfactorRep
    htargetNonrational hright
  intro hgAmbient
  exact hquartic (quarticProbeANF_eq_zero_of_mem_targetAmbient hgAmbient)

/-- Cubic specialization of the ambient-space obstruction. -/
theorem seedUsing_factorCoeff_ne_zero_of_cubic
    {g correction factor target : ANF 8}
    {targetConst factorConst : F₂}
    {targetLinear factorLinear : LinearForm}
    {targetCoeff : TargetCoeff} {factorCoeff : Fin 3 → F₂}
    (hcubicSeed : anfThreeProjection g ≠ 0)
    (hcorrection : correction ∈ rationalLowSpace)
    (htargetEq : target = (g + correction) * factor)
    (htargetMem : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetNotLow : target ∉ rationalLowSpace)
    (htargetRep : target =
      affineANF targetConst targetLinear + targetANF targetCoeff)
    (hfactorRep : factor =
      affineANF factorConst factorLinear + rationalANF factorCoeff)
    (htargetNonrational : ¬ IsRationalCoeff targetCoeff)
    (hright : target * factor = target) : factorCoeff ≠ 0 := by
  apply seedUsing_factorCoeff_ne_zero_of_not_mem_targetAmbient ?_
    hcorrection htargetEq htargetMem htargetNotLow htargetRep hfactorRep
    htargetNonrational hright
  intro hgAmbient
  exact hcubicSeed (anfThreeProjection_eq_zero_of_mem_targetAmbient hgAmbient)

end

end N4
end UnrestrictedBooleanMul
