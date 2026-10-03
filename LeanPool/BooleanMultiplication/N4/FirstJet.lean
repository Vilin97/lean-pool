/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicSlice

/-!
# The first low--low collision

After the seed-using branch is excluded, the first useful suffix gate is a
low--low product.  This file first removes the remaining circuit bookkeeping:
the useful target cannot arise from that product alone, so the old-state
shift contains the cubic seed with coefficient one.  Consequently the seed
and the new low--low product have a genuinely non-rational quadratic
collision in `Aff + T`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A low-low child collides with a cubic seed modulo low terms to produce a new target. -/
def CubicLowLowCollision (g : ANF 8) : Prop :=
  ∃ (child low target : ANF 8),
    IsLowLowProduct child ∧
    low ∈ rationalLowSpace ∧
    target ∈ targetAmbient 8 (mulTarget 4) ∧
    target ∉ rationalLowSpace ∧
    target = (low + g) + child

/-- Preserve the particular child and target when extracting the cubic-seed collision. -/
theorem NormalizedEight.cubicLowLowCollision_of_firstUsefulChild
    {C : Circuit 8 8} (h : NormalizedEight C)
    {target child shift : ANF 8}
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetOld : target ∉ circuitFlag C 4)
    (hshift : shift ∈ circuitFlag C 4)
    (htargetEq : target = shift + child)
    (hchild : IsLowLowProduct child) :
    ∃ low : ANF 8, low ∈ rationalLowSpace ∧
      target ∉ rationalLowSpace ∧ target = (low + C.gate 3) + child := by
  have hlowFour : rationalLowSpace ≤ circuitFlag C 4 := by
    rw [h.wireSpace_four_eq]
    exact le_sup_left
  have htargetNotLow : target ∉ rationalLowSpace := by
    intro htargetLow
    exact htargetOld (hlowFour htargetLow)
  rcases exists_low_add_seed_of_mem_four h hshift with
    ⟨low, e, hlow, hshiftEq⟩
  rcases f2_eq_zero_or_one e with rfl | rfl
  · have htargetEq' : target = low + child := by
      simpa using htargetEq.trans
        (congrArg (fun z : ANF 8 => z + child) hshiftEq)
    have hchildAmbient : child ∈ targetAmbient 8 (mulTarget 4) := by
      have htargetPlus := add_mem_targetAmbient_of_mem_rationalLow
        htarget hlow
      have heq : target + low = child := by
        rw [htargetEq']
        calc
          (low + child) + low = (low + low) + child := by ac_rfl
          _ = child := by rw [anf_add_self, zero_add]
      rwa [heq] at htargetPlus
    rcases hchild with ⟨u, v, hu, hv, hchildEq⟩
    have hchildLow : child ∈ rationalLowSpace := by
      rw [hchildEq]
      exact rationalLow_mul_mem_of_mem_targetAmbient hu hv
        (by simpa [hchildEq] using hchildAmbient)
    exact (htargetNotLow (by
      rw [htargetEq']
      exact Submodule.add_mem _ hlow hchildLow)).elim
  · refine ⟨low, hlow, htargetNotLow, ?_⟩
    simpa only [one_smul] using htargetEq.trans
      (congrArg (fun z : ANF 8 => z + child) hshiftEq)

/-- The first useful low-low child must cancel the seed high part. -/
theorem NormalizedEight.cubicLowLowCollision
    {C : Circuit 8 8} (h : NormalizedEight C) :
    CubicLowLowCollision (C.gate 3) := by
  rcases h.firstUsefulChild_isLowLow with
    ⟨target, child, shift, htarget, htargetOld, _htargetNew, hshift,
      htargetEq, hchild⟩
  rcases h.cubicLowLowCollision_of_firstUsefulChild
      htarget htargetOld hshift htargetEq hchild with
    ⟨low, hlow, htargetNotLow, hcollision⟩
  exact ⟨child, low, target, hchild, hlow, htarget, htargetNotLow, hcollision⟩

/-- Coordinate-ready form of the collision.  The child has zero quartic
probe, its cubic projection equals the nonzero seed cubic, and the surviving
quadratic target coefficient is outside the rational-place span. -/
def CubicLowLowNormalCollisionAt
    (g target targetAffine : ANF 8) (targetCoeff : TargetCoeff) : Prop :=
  ∃ (child low : ANF 8)
    (childLeftConst childRightConst : F₂)
    (childLeftLinear childRightLinear : LinearForm)
    (childLeftCoeff childRightCoeff : Fin 3 → F₂),
    CubicSeedNormalForm g ∧
    low ∈ rationalLowSpace ∧
    targetAffine ∈ affine 8 ∧
    child =
      (affineANF childLeftConst childLeftLinear +
          rationalANF childLeftCoeff) *
        (affineANF childRightConst childRightLinear +
          rationalANF childRightCoeff) ∧
    target = (low + g) + child ∧
    target = targetAffine + targetANF targetCoeff ∧
    quarticWedgeProbe (rationalTwo childLeftCoeff)
      (rationalTwo childRightCoeff) = 0 ∧
    anfThreeProjection child = anfThreeProjection g ∧
    anfThreeProjection g ≠ 0 ∧
    ¬ IsRationalCoeff targetCoeff

/-- Existence of a target and affine correction in the normalized cubic low-low collision form. -/
@[expose]
def CubicLowLowNormalCollision (g : ANF 8) : Prop :=
  ∃ (target targetAffine : ANF 8) (targetCoeff : TargetCoeff),
    CubicLowLowNormalCollisionAt g target targetAffine targetCoeff

/-- Normalize a fixed low-low collision without changing its target witness. -/
theorem NormalizedEight.cubicLowLowNormalCollisionAt
    {C : Circuit 8 8} (h : NormalizedEight C)
    {child low target : ANF 8}
    (hchild : IsLowLowProduct child) (hlow : low ∈ rationalLowSpace)
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetNotLow : target ∉ rationalLowSpace)
    (htargetEq : target = (low + C.gate 3) + child) :
    ∃ (targetAffine : ANF 8) (targetCoeff : TargetCoeff),
      CubicLowLowNormalCollisionAt (C.gate 3) target targetAffine targetCoeff := by
  rcases hchild with ⟨childLeft, childRight,
    hchildLeft, hchildRight, hchildEq⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildLeft with
    ⟨childLeftConst, childLeftLinear, childLeftCoeff, hchildLeftRep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildRight with
    ⟨childRightConst, childRightLinear, childRightCoeff, hchildRightRep⟩
  rcases exists_targetAmbient_rep htarget with
    ⟨targetAffine, targetCoeff, htargetAffine, htargetRep⟩
  have hchildRep : child =
      (affineANF childLeftConst childLeftLinear +
          rationalANF childLeftCoeff) *
        (affineANF childRightConst childRightLinear +
          rationalANF childRightCoeff) := by
    rw [hchildEq, hchildLeftRep, hchildRightRep]
  have htargetQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient htarget
  have hlowQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hgQuartic := h.seed_quarticProbe_eq_zero
  have hchildQuartic : quarticProbeANF child = 0 := by
    have heq := congrArg quarticProbeANF htargetEq
    rw [map_add, map_add, hlowQuartic, hgQuartic, htargetQuartic] at heq
    simpa using heq.symm
  have hchildProbe : quarticWedgeProbe (rationalTwo childLeftCoeff)
      (rationalTwo childRightCoeff) = 0 := by
    rw [hchildRep, lowProduct_quarticProjection] at hchildQuartic
    exact hchildQuartic
  have htargetCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient htarget
  have hlowCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hchildCubic : anfThreeProjection child =
      anfThreeProjection (C.gate 3) := by
    have heq := congrArg anfThreeProjection htargetEq
    rw [map_add, map_add, hlowCubic, htargetCubic, zero_add] at heq
    exact ((add_eq_zero_iff_eq_neg.mp heq.symm).trans
      (by funext i j k; exact neg_eq_self_f2 _)).symm
  have htargetNonrational : ¬ IsRationalCoeff targetCoeff := by
    intro hrat
    rcases (IsRationalCoeff_iff targetCoeff).mp hrat with
      ⟨alpha, halpha⟩
    apply htargetNotLow
    rw [htargetRep, halpha]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left htargetAffine
    · apply Submodule.mem_sup_right
      exact (mem_rationalTargetSpace_iff _).mpr ⟨alpha, rfl⟩
  exact
    ⟨targetAffine, targetCoeff,
      child, low,
      childLeftConst, childRightConst, childLeftLinear, childRightLinear,
      childLeftCoeff, childRightCoeff,
      h.cubicSeedNormalForm, hlow, htargetAffine, hchildRep,
      htargetEq, htargetRep, hchildProbe, hchildCubic,
      h.seed_cubicProjection_ne_zero, htargetNonrational⟩

theorem NormalizedEight.cubicLowLowNormalCollision
    {C : Circuit 8 8} (h : NormalizedEight C) :
    CubicLowLowNormalCollision (C.gate 3) := by
  rcases h.cubicLowLowCollision with
    ⟨child, low, target, hchild, hlow, htarget, htargetNotLow, htargetEq⟩
  rcases h.cubicLowLowNormalCollisionAt hchild hlow htarget htargetNotLow htargetEq with
    ⟨targetAffine, targetCoeff, hcollision⟩
  exact ⟨target, targetAffine, targetCoeff, hcollision⟩

/-- Exterior-coordinate data describing a cubic low-low collision at a first jet. -/
def ExteriorFirstJetCollision : Prop :=
  ∃ (seedCoeff childCoeff lowCoeff : Fin 3 → F₂)
    (seedLinear seedCompanion childLinear childCompanion : LinearForm)
    (seedRho childRho : F₂) (targetCoeff : TargetCoeff),
    seedCoeff ≠ 0 ∧
    childCoeff ≠ 0 ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) ≠ 0 ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
      vectorWedgeTwo childLinear (rationalTwo childCoeff) ∧
    ¬ IsRationalCoeff targetCoeff ∧
    targetTwo targetCoeff =
      (rationalTwo lowCoeff +
        (seedRho • rationalTwo seedCoeff +
          vectorWedge seedCompanion seedLinear +
          booleanContraction seedLinear (rationalTwo seedCoeff))) +
        (childRho • rationalTwo childCoeff +
          vectorWedge childCompanion childLinear +
          booleanContraction childLinear (rationalTwo childCoeff))

/-- Exterior collision data retaining the seed projections and the particular target. -/
@[expose]
def ExteriorFirstJetCollisionAt
    (g target targetAffine : ANF 8) (targetCoeff : TargetCoeff) : Prop :=
  targetAffine ∈ affine 8 ∧
  target = targetAffine + targetANF targetCoeff ∧
  ∃ (seedCoeff childCoeff lowCoeff : Fin 3 → F₂)
    (seedLinear seedCompanion childLinear childCompanion : LinearForm)
    (seedRho childRho : F₂),
    seedCoeff ≠ 0 ∧ childCoeff ≠ 0 ∧
    anfThreeProjection g = vectorWedgeTwo seedLinear (rationalTwo seedCoeff) ∧
    anfTwoProjection g = seedRho • rationalTwo seedCoeff +
      vectorWedge seedCompanion seedLinear +
      booleanContraction seedLinear (rationalTwo seedCoeff) ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) ≠ 0 ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
      vectorWedgeTwo childLinear (rationalTwo childCoeff) ∧
    ¬ IsRationalCoeff targetCoeff ∧
    targetTwo targetCoeff =
      (rationalTwo lowCoeff +
        (seedRho • rationalTwo seedCoeff +
          vectorWedge seedCompanion seedLinear +
          booleanContraction seedLinear (rationalTwo seedCoeff))) +
        (childRho • rationalTwo childCoeff +
          vectorWedge childCompanion childLinear +
          booleanContraction childLinear (rationalTwo childCoeff))

/-- Project a fixed collision to exterior coordinates, retaining its correlated witnesses. -/
theorem cubicLowLowNormalCollisionAt_exterior
    {g target targetAffine : ANF 8} {targetCoeff : TargetCoeff}
    (h : CubicLowLowNormalCollisionAt g target targetAffine targetCoeff) :
    ExteriorFirstJetCollisionAt g target targetAffine targetCoeff := by
  rcases h with
    ⟨child, low,
      childLeftConst, childRightConst, childLeftLinear, childRightLinear,
      childLeftCoeff, childRightCoeff,
      hseedNormal, hlow, htargetAffine, hchildRep,
      htargetEq, htargetRep, hchildProbe, hchildCubic,
      hgCubicNonzero, htargetNonrational⟩
  rcases hseedNormal with
    ⟨_seedLeftConst, _seedRightConst, _seedLeftLinear, _seedRightLinear,
      _seedLeftCoeff, _seedRightCoeff, seedCoeff, seedLinear,
      seedCompanion, seedRho, _hseedRep, _hseedQuartic, hseedCoeff,
      hgCubic, hgCubicNonzero', hgQuadratic⟩
  have hchildCubicFormula : anfThreeProjection child =
      rationalProductCubic childLeftLinear childRightLinear
        childLeftCoeff childRightCoeff := by
    rw [hchildRep]
    exact lowProduct_cubicProjection_of_quartic_zero
      childLeftConst childRightConst childLeftLinear childRightLinear
      childLeftCoeff childRightCoeff hchildProbe
  have hchildProductCubicNonzero :
      rationalProductCubic childLeftLinear childRightLinear
        childLeftCoeff childRightCoeff ≠ 0 := by
    intro hz
    apply hgCubicNonzero
    rw [← hchildCubic, hchildCubicFormula, hz]
  rcases low_product_quadratic_normal_form
      childLeftConst childRightConst childLeftLinear childRightLinear
      childLeftCoeff childRightCoeff
      (rational_wedge_zero_of_probe_zero _ _ hchildProbe)
      hchildProductCubicNonzero with
    ⟨childCoeff, childLinear, childCompanion, childRho,
      hchildCoeff, hchildNormalCubic, hchildNormalQuadratic⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hlow with
    ⟨lowConst, lowLinear, lowCoeff, hlowRep⟩
  have hlowQuadratic : anfTwoProjection low = rationalTwo lowCoeff := by
    rw [hlowRep, map_add,
      anfTwoProjection_kills_affine (affineANF_mem lowConst lowLinear),
      anfTwoProjection_rationalANF, zero_add]
  have hchildQuadratic : anfTwoProjection child =
      childRho • rationalTwo childCoeff +
        vectorWedge childCompanion childLinear +
        booleanContraction childLinear (rationalTwo childCoeff) := by
    rw [hchildRep,
      lowProduct_quadraticProjection_of_quartic_zero
        childLeftConst childRightConst childLeftLinear childRightLinear
        childLeftCoeff childRightCoeff hchildProbe,
      hchildNormalQuadratic]
  have htargetQuadratic : anfTwoProjection target = targetTwo targetCoeff := by
    rw [htargetRep, map_add,
      anfTwoProjection_kills_affine htargetAffine,
      anfTwoProjection_targetANF, zero_add]
  have hquadratic := congrArg anfTwoProjection htargetEq
  rw [htargetQuadratic, map_add, map_add, hlowQuadratic,
    hgQuadratic, hchildQuadratic] at hquadratic
  have hcubicEquality :
      vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
        vectorWedgeTwo childLinear (rationalTwo childCoeff) := by
    calc
      vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
          anfThreeProjection g := hgCubic.symm
      _ = anfThreeProjection child := hchildCubic.symm
      _ = rationalProductCubic childLeftLinear childRightLinear
          childLeftCoeff childRightCoeff := hchildCubicFormula
      _ = vectorWedgeTwo childLinear (rationalTwo childCoeff) :=
        hchildNormalCubic
  exact
    ⟨htargetAffine, htargetRep, seedCoeff, childCoeff, lowCoeff,
      seedLinear, seedCompanion, childLinear, childCompanion, seedRho, childRho,
      hseedCoeff, hchildCoeff, hgCubic, hgQuadratic, hgCubicNonzero',
      hcubicEquality, htargetNonrational, hquadratic⟩

/-- Existential exterior collision obtained from the correlated projection theorem. -/
theorem NormalizedEight.exteriorFirstJetCollision
    {C : Circuit 8 8} (h : NormalizedEight C) : ExteriorFirstJetCollision := by
  rcases h.cubicLowLowNormalCollision with ⟨target, targetAffine, targetCoeff, hcollision⟩
  rcases cubicLowLowNormalCollisionAt_exterior hcollision with
    ⟨_htargetAffine, _htargetRep, seedCoeff, childCoeff, lowCoeff,
      seedLinear, seedCompanion, childLinear, childCompanion, seedRho, childRho,
      hseedCoeff, hchildCoeff, _hgCubic, _hgQuadratic, hcubicNonzero,
      hcubic, htargetNonrational, hquadratic⟩
  exact ⟨seedCoeff, childCoeff, lowCoeff, seedLinear, seedCompanion,
    childLinear, childCompanion, seedRho, childRho, targetCoeff,
    hseedCoeff, hchildCoeff, hcubicNonzero, hcubic, htargetNonrational, hquadratic⟩

/-- Two equal cubic presentations yield a zero direct sum after addition in characteristic two. -/
theorem rationalCubicDirectSum_eq_zero_of_cubic_equal
    (alpha beta : Fin 3 → F₂) (N N' : LinearForm)
    (hcubic : vectorWedgeTwo N (rationalTwo alpha) =
      vectorWedgeTwo N' (rationalTwo beta)) :
    rationalCubicDirectSum (fun theta => alpha theta • N + beta theta • N') = 0 := by
  have hdirectExpansion : rationalCubicDirectSum (fun theta => alpha theta • N + beta theta • N') =
      vectorWedgeTwo N (rationalTwo alpha) +
        vectorWedgeTwo N' (rationalTwo beta) := by
    funext i j k
    simp [rationalCubicDirectSum, cubicPlaceLinear, rationalTwo, vectorWedgeTwo,
      rationalPlaceTwo, Fin.sum_univ_succ]
    ring
  rw [hdirectExpansion, hcubic]
  funext i j k
  exact CharTwo.add_self_eq_zero (vectorWedgeTwo N' (rationalTwo beta) i j k)

/-- The Boolean degree-lowering contractions attached to two equal rational
cubic presentations differ only by a rational quadratic form.  This is the
coordinate-free role of the direct-sum kernel `I₀ ⊕ I₁ ⊕ I∞`. -/
theorem contraction_sum_mem_rational_of_cubic_equal
    (alpha beta : Fin 3 → F₂) (N N' : LinearForm)
    (hcubic : vectorWedgeTwo N (rationalTwo alpha) =
      vectorWedgeTwo N' (rationalTwo beta)) :
    booleanContraction N (rationalTwo alpha) +
        booleanContraction N' (rationalTwo beta) ∈
      rationalPlaceTwoSpace := by
  let M : Fin 3 → LinearForm := fun theta =>
    alpha theta • N + beta theta • N'
  have hdirect : rationalCubicDirectSum M = 0 :=
    rationalCubicDirectSum_eq_zero_of_cubic_equal alpha beta N N' hcubic
  have hkernel := rationalCubicDirectSum_kernel M hdirect
  have hcontraction :
      booleanContraction N (rationalTwo alpha) +
          booleanContraction N' (rationalTwo beta) =
        ∑ theta : Fin 3,
          booleanContraction (M theta) (rationalPlaceTwo theta) := by
    funext i j
    simp [rationalTwo, M, booleanContraction, Fin.sum_univ_succ]
    ring
  rw [hcontraction]
  apply Submodule.sum_mem
  intro theta _
  rcases hkernel theta with ⟨a, b, hM⟩
  rw [hM, booleanContraction_rationalPlace]
  exact Submodule.smul_mem _ _ (rationalPlaceTwo_mem theta)

/-- The reduced exterior-coordinate form of a first-jet collision. -/
@[expose]
def ExteriorFirstJetReducedCollision : Prop :=
  ∃ (seedCoeff childCoeff rationalCoeff : Fin 3 → F₂)
    (seedLinear seedCompanion childLinear childCompanion : LinearForm)
    (targetCoeff : TargetCoeff),
    seedCoeff ≠ 0 ∧
    childCoeff ≠ 0 ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) ≠ 0 ∧
    vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
      vectorWedgeTwo childLinear (rationalTwo childCoeff) ∧
    ¬ IsRationalCoeff targetCoeff ∧
    targetTwo targetCoeff =
      rationalTwo rationalCoeff +
        vectorWedge seedCompanion seedLinear +
        vectorWedge childCompanion childLinear

/-- Equal cubic parts make the Boolean contractions rational, preserving all linear witnesses. -/
theorem exteriorFirstJetCollision_reduce_quadratic
    {seedCoeff childCoeff lowCoeff : Fin 3 → F₂}
    {seedLinear seedCompanion childLinear childCompanion : LinearForm}
    {seedRho childRho : F₂} {targetCoeff : TargetCoeff}
    (hcubic : vectorWedgeTwo seedLinear (rationalTwo seedCoeff) =
      vectorWedgeTwo childLinear (rationalTwo childCoeff))
    (hquadratic : targetTwo targetCoeff =
      (rationalTwo lowCoeff +
        (seedRho • rationalTwo seedCoeff +
          vectorWedge seedCompanion seedLinear +
          booleanContraction seedLinear (rationalTwo seedCoeff))) +
        (childRho • rationalTwo childCoeff +
          vectorWedge childCompanion childLinear +
          booleanContraction childLinear (rationalTwo childCoeff))) :
    ∃ rationalCoeff : Fin 3 → F₂,
      targetTwo targetCoeff = rationalTwo rationalCoeff +
        vectorWedge seedCompanion seedLinear + vectorWedge childCompanion childLinear := by
  let rationalPart : TwoForm :=
    rationalTwo lowCoeff + seedRho • rationalTwo seedCoeff +
      childRho • rationalTwo childCoeff +
      (booleanContraction seedLinear (rationalTwo seedCoeff) +
        booleanContraction childLinear (rationalTwo childCoeff))
  have hrationalPart : rationalPart ∈ rationalPlaceTwoSpace := by
    dsimp [rationalPart]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _ (rationalTwo_mem lowCoeff)
          (Submodule.smul_mem _ _ (rationalTwo_mem seedCoeff)))
        (Submodule.smul_mem _ _ (rationalTwo_mem childCoeff)))
      (contraction_sum_mem_rational_of_cubic_equal
        seedCoeff childCoeff seedLinear childLinear hcubic)
  rcases exists_rationalTwo_of_mem hrationalPart with
    ⟨rationalCoeff, hrationalCoeff⟩
  refine ⟨rationalCoeff, ?_⟩
  rw [hquadratic, ← hrationalCoeff]
  dsimp [rationalPart]
  module


theorem exteriorFirstJetCollision_reduced
    (h : ExteriorFirstJetCollision) : ExteriorFirstJetReducedCollision := by
  rcases h with
    ⟨seedCoeff, childCoeff, lowCoeff, seedLinear, seedCompanion,
      childLinear, childCompanion, seedRho, childRho, targetCoeff,
      hseedCoeff, hchildCoeff, hcubicNonzero, hcubic,
      htargetNonrational, hquadratic⟩
  rcases exteriorFirstJetCollision_reduce_quadratic hcubic hquadratic with
    ⟨rationalCoeff, htarget⟩
  exact ⟨seedCoeff, childCoeff, rationalCoeff, seedLinear, seedCompanion,
    childLinear, childCompanion, targetCoeff, hseedCoeff, hchildCoeff,
    hcubicNonzero, hcubic, htargetNonrational, htarget⟩

/-- A linear form lies in the two-input support of a rational place. -/
@[expose]
def InPlaceSupport (theta : Fin 3) (u : LinearForm) : Prop :=
  ∃ a b : F₂, u = a • placeA theta + b • placeB theta

theorem cubic_equal_support_relation
    (alpha beta : Fin 3 → F₂) (N N' : LinearForm)
    (hcubic : vectorWedgeTwo N (rationalTwo alpha) =
      vectorWedgeTwo N' (rationalTwo beta)) :
    ∀ theta, InPlaceSupport theta
      (alpha theta • N + beta theta • N') := by
  let M : Fin 3 → LinearForm := fun theta =>
    alpha theta • N + beta theta • N'
  have hdirect : rationalCubicDirectSum M = 0 :=
    rationalCubicDirectSum_eq_zero_of_cubic_equal alpha beta N N' hcubic
  intro theta
  rcases rationalCubicDirectSum_kernel M hdirect theta with ⟨a, b, hab⟩
  exact ⟨a, b, hab⟩

theorem place_supports_disjoint
    {theta phi : Fin 3} (hne : theta ≠ phi) {u : LinearForm}
    (htheta : InPlaceSupport theta u) (hphi : InPlaceSupport phi u) :
    u = 0 := by
  rcases htheta with ⟨a, b, hu⟩
  rcases hphi with ⟨c, d, hu'⟩
  have heq : a • placeA theta + b • placeB theta =
      c • placeA phi + d • placeB phi := hu.symm.trans hu'
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  have h3 := congrFun heq 3
  have h4 := congrFun heq 4
  have h5 := congrFun heq 5
  have h6 := congrFun heq 6
  have h7 := congrFun heq 7
  fin_cases theta <;> fin_cases phi
  · exact (hne rfl).elim
  · have hc : c = 0 := by simpa [placeA, placeB] using h1.symm
    have ha : a = 0 := by simpa [placeA, placeB, hc] using h0
    have hd : d = 0 := by simpa [placeA, placeB] using h5.symm
    have hb : b = 0 := by simpa [placeA, placeB, hd] using h4
    simp [hu, ha, hb]
  · have ha : a = 0 := by simpa [placeA, placeB] using h0
    have hb : b = 0 := by simpa [placeA, placeB] using h4
    simp [hu, ha, hb]
  · have ha : a = 0 := by simpa [placeA, placeB] using h1
    have hb : b = 0 := by simpa [placeA, placeB] using h5
    simp [hu, ha, hb]
  · exact (hne rfl).elim
  · have ha : a = 0 := by simpa [placeA, placeB] using h0
    have hb : b = 0 := by simpa [placeA, placeB] using h4
    simp [hu, ha, hb]
  · have ha : a = 0 := by simpa [placeA, placeB] using h3
    have hb : b = 0 := by simpa [placeA, placeB] using h7
    simp [hu, ha, hb]
  · have hc : c = 0 := by simpa [placeA, placeB] using h0.symm
    have ha : a = 0 := by simpa [placeA, placeB, hc] using h3
    have hd : d = 0 := by simpa [placeA, placeB] using h4.symm
    have hb : b = 0 := by simpa [placeA, placeB, hd] using h7
    simp [hu, ha, hb]
  · exact (hne rfl).elim

theorem target_rational_of_distinct_place_wedges
    {theta phi : Fin 3} (hne : theta ≠ phi)
    {N N' z w : LinearForm} {gamma : Fin 3 → F₂}
    {c : TargetCoeff}
    (hN : InPlaceSupport theta N) (hN' : InPlaceSupport phi N')
    (htarget : targetTwo c = rationalTwo gamma +
      vectorWedge z N + vectorWedge w N') :
    IsRationalCoeff c := by
  rcases hN with ⟨a, b, rfl⟩
  rcases hN' with ⟨d, e, rfl⟩
  rw [vectorWedge_comm z, vectorWedge_comm w] at htarget
  fin_cases theta <;> fin_cases phi
  · exact (hne rfl).elim
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 0 d e a b w z
    simpa [quarticSupportPair, quarticSupportVector, add_assoc, add_left_comm, add_comm
      ] using htarget
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 1 a b d e z w
    simpa [quarticSupportPair, quarticSupportVector] using htarget
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 0 a b d e z w
    simpa [quarticSupportPair, quarticSupportVector] using htarget
  · exact (hne rfl).elim
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 2 a b d e z w
    simpa [quarticSupportPair, quarticSupportVector] using htarget
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 1 d e a b w z
    simpa [quarticSupportPair, quarticSupportVector, add_assoc, add_left_comm, add_comm
      ] using htarget
  · apply target_eq_rational_add_supportPair_is_rational
      c gamma 2 d e a b w z
    simpa [quarticSupportPair, quarticSupportVector, add_assoc, add_left_comm, add_comm
      ] using htarget
  · exact (hne rfl).elim

theorem target_rational_of_same_second_wedge
    {N z w : LinearForm} {gamma : Fin 3 → F₂} {c : TargetCoeff}
    (htarget : targetTwo c = rationalTwo gamma +
      vectorWedge z N + vectorWedge w N) :
    IsRationalCoeff c := by
  let delta : TargetCoeff := c + rationalCoeffRep gamma
  have hdelta : targetTwo delta = vectorWedge (z + w) N := by
    rw [show targetTwo delta = targetTwo c +
      targetTwo (rationalCoeffRep gamma) by
        exact targetTwoLinear.map_add _ _]
    rw [targetTwo_rationalCoeffRep, htarget]
    funext i j
    simp [vectorWedge]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hdeltaRat : targetTwo delta ∈ rationalPlaceTwoSpace := by
    apply decomposable_mem_rationalPlaceTwoSpace
    · exact ⟨delta, rfl⟩
    · exact ⟨z + w, N, hdelta⟩
  have hdeltaCoeff : delta ∈ rationalCoeffSpace :=
    coeff_mem_rational_of_targetTwo_mem hdeltaRat
  rcases targetCoeff_eq_rationalCoeffRep_of_mem hdeltaCoeff with
    ⟨eta, heta⟩
  apply (IsRationalCoeff_iff c).mpr
  refine ⟨eta + gamma, ?_⟩
  rw [rationalCoeffRep_add, ← heta]
  dsimp [delta]
  funext i
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem target_rational_of_support_and_sum_support
    {theta phi : Fin 3} (hne : theta ≠ phi)
    {N N' z w : LinearForm} {gamma : Fin 3 → F₂} {c : TargetCoeff}
    (hN : InPlaceSupport theta N)
    (hsum : InPlaceSupport phi (N + N'))
    (htarget : targetTwo c = rationalTwo gamma +
      vectorWedge z N + vectorWedge w N') :
    IsRationalCoeff c := by
  rcases hsum with ⟨a, b, hp⟩
  let p := a • placeA phi + b • placeB phi
  have hN' : N' = N + p := by
    calc
      N' = N + (N + N') := by
        funext i
        simp only [Pi.add_apply]
        ring_nf
        simp [N3Certificate.two_eq_zero_f2]
      _ = N + p := by rw [hp]
  have hpSupport : InPlaceSupport phi p := ⟨a, b, rfl⟩
  apply target_rational_of_distinct_place_wedges hne hN hpSupport
  rw [hN'] at htarget
  calc
    targetTwo c = rationalTwo gamma + vectorWedge z N +
        vectorWedge w (N + p) := htarget
    _ = rationalTwo gamma + vectorWedge (z + w) N +
        vectorWedge w p := by
      funext i j
      simp [vectorWedge]
      ring

theorem target_rational_of_support_and_sum_support_right
    {theta phi : Fin 3} (hne : theta ≠ phi)
    {N N' z w : LinearForm} {gamma : Fin 3 → F₂} {c : TargetCoeff}
    (hN' : InPlaceSupport theta N')
    (hsum : InPlaceSupport phi (N + N'))
    (htarget : targetTwo c = rationalTwo gamma +
      vectorWedge z N + vectorWedge w N') :
    IsRationalCoeff c := by
  have htarget' : targetTwo c = rationalTwo gamma +
      vectorWedge w N' + vectorWedge z N := by
    rw [htarget]
    module
  have hsum' : InPlaceSupport phi (N' + N) := by
    simpa [add_comm] using hsum
  exact target_rational_of_support_and_sum_support hne hN' hsum' htarget'

private theorem exists_eq_one_of_ne_zero {n : Nat} (v : Fin n → F₂)
    (hv : v ≠ 0) : ∃ i, v i = 1 := by
  by_contra h
  push Not at h
  apply hv
  funext i
  exact (f2_eq_zero_or_one (v i)).resolve_right (h i)

@[simp] theorem rationalSingleton_apply_self (theta : Fin 3) :
    rationalSingleton theta theta = 1 := by
  fin_cases theta <;> decide

theorem rationalSingleton_apply_ne {theta phi : Fin 3}
    (hne : phi ≠ theta) : rationalSingleton theta phi = 0 := by
  fin_cases theta <;> fin_cases phi <;> simp_all [rationalSingleton]


/-- Non-rationality leaves only a common singleton rational place in the two
equal cubic presentations.  The proof uses the three direct-sum support
relations and the support-pair separators; it does not enumerate coefficient
words. -/
theorem cubic_collision_forces_common_singleton
    (alpha beta : Fin 3 → F₂) (N N' z w : LinearForm)
    (gamma : Fin 3 → F₂) (c : TargetCoeff)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hcubic : vectorWedgeTwo N (rationalTwo alpha) =
      vectorWedgeTwo N' (rationalTwo beta))
    (htargetNonrational : ¬ IsRationalCoeff c)
    (htarget : targetTwo c = rationalTwo gamma +
      vectorWedge z N + vectorWedge w N') :
    ∃ theta : Fin 3,
      alpha = rationalSingleton theta ∧
      beta = rationalSingleton theta := by
  have hsupport := cubic_equal_support_relation alpha beta N N' hcubic
  have hab : alpha = beta := by
    by_contra hab
    have hex : ∃ theta, alpha theta ≠ beta theta := by
      by_contra h
      push Not at h
      exact hab (funext h)
    rcases hex with ⟨theta, htheta⟩
    rcases f2_eq_zero_or_one (alpha theta) with ha0 | ha1 <;>
      rcases f2_eq_zero_or_one (beta theta) with hb0 | hb1
    · exact (htheta (ha0.trans hb0.symm)).elim
    · have hN' : InPlaceSupport theta N' := by
        simpa [ha0, hb1] using hsupport theta
      by_cases hcross : ∃ phi : Fin 3,
          alpha phi = 1 ∧ beta phi = 0
      · rcases hcross with ⟨phi, hpa, hpb⟩
        have hN : InPlaceSupport phi N := by
          simpa [hpa, hpb] using hsupport phi
        have hne : theta ≠ phi := by
          intro heq
          subst phi
          exact zero_ne_one (ha0.symm.trans hpa)
        have htarget' : targetTwo c = rationalTwo gamma +
            vectorWedge w N' + vectorWedge z N := by
          rw [htarget]
          module
        exact htargetNonrational
          (target_rational_of_distinct_place_wedges hne hN' hN htarget')
      · rcases exists_eq_one_of_ne_zero alpha halpha with ⟨phi, hpa⟩
        have hpb : beta phi = 1 := by
          rcases f2_eq_zero_or_one (beta phi) with hpb | hpb
          · exact (hcross ⟨phi, hpa, hpb⟩).elim
          · exact hpb
        have hsum : InPlaceSupport phi (N + N') := by
          simpa [hpa, hpb] using hsupport phi
        have hne : theta ≠ phi := by
          intro heq
          subst phi
          exact zero_ne_one (ha0.symm.trans hpa)
        exact htargetNonrational
          (target_rational_of_support_and_sum_support_right
            hne hN' hsum htarget)
    · have hN : InPlaceSupport theta N := by
        simpa [ha1, hb0] using hsupport theta
      by_cases hcross : ∃ phi : Fin 3,
          beta phi = 1 ∧ alpha phi = 0
      · rcases hcross with ⟨phi, hpb, hpa⟩
        have hN' : InPlaceSupport phi N' := by
          simpa [hpa, hpb] using hsupport phi
        have hne : theta ≠ phi := by
          intro heq
          subst phi
          exact zero_ne_one (hb0.symm.trans hpb)
        exact htargetNonrational
          (target_rational_of_distinct_place_wedges hne hN hN' htarget)
      · rcases exists_eq_one_of_ne_zero beta hbeta with ⟨phi, hpb⟩
        have hpa : alpha phi = 1 := by
          rcases f2_eq_zero_or_one (alpha phi) with hpa | hpa
          · exact (hcross ⟨phi, hpb, hpa⟩).elim
          · exact hpa
        have hsum : InPlaceSupport phi (N + N') := by
          simpa [hpa, hpb] using hsupport phi
        have hne : theta ≠ phi := by
          intro heq
          subst phi
          exact zero_ne_one (hb0.symm.trans hpb)
        exact htargetNonrational
          (target_rational_of_support_and_sum_support hne hN hsum htarget)
    · exact (htheta (ha1.trans hb1.symm)).elim
  subst beta
  rcases exists_eq_one_of_ne_zero alpha halpha with ⟨theta, htheta⟩
  have hother : ∀ phi : Fin 3, phi ≠ theta → alpha phi = 0 := by
    intro phi hne
    rcases f2_eq_zero_or_one (alpha phi) with hzero | hone
    · exact hzero
    · have hsumTheta : InPlaceSupport theta (N + N') := by
        simpa [htheta] using hsupport theta
      have hsumPhi : InPlaceSupport phi (N + N') := by
        simpa [hone] using hsupport phi
      have hsumZero : N + N' = 0 :=
        place_supports_disjoint hne hsumPhi hsumTheta
      have hNN' : N = N' := by
        funext i
        have hi := congrFun hsumZero i
        exact (add_eq_zero_iff_eq_neg.mp hi).trans (neg_eq_self_f2 _)
      exact (htargetNonrational (by
        rw [hNN'] at htarget
        exact target_rational_of_same_second_wedge htarget)).elim
  have halphaSingleton : alpha = rationalSingleton theta := by
    funext phi
    by_cases hphi : phi = theta
    · subst phi
      exact htheta.trans (rationalSingleton_apply_self theta).symm
    · exact (hother phi hphi).trans (rationalSingleton_apply_ne hphi).symm
  exact ⟨theta, halphaSingleton, halphaSingleton⟩


end

end N4
end UnrestrictedBooleanMul
