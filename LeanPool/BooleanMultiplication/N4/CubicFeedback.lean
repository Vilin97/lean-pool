/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuinticBridge

/-!
# Cubic seed and first-feedback interfaces

After quartic exclusion the normalized seed is the product of two rational-low
factors with dependent quadratic parts.  This file packages the resulting
exterior normal form at circuit level.  The package records both homogeneous
parts needed later: the nonzero anchored cubic `N ∧ G` and its Boolean
quadratic companion `ρ G + z ∧ N + κ_G(N)`.

No circuit configurations are enumerated here; the proof is obtained from the
three algebraic dependency cases in `low_product_quadratic_normal_form`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Complete homogeneous normal form of a cubic seed arising from the
normalized rational prefix. -/
@[expose]
def CubicSeedNormalForm (g : ANF 8) : Prop :=
  ∃ (leftConst rightConst : F₂) (leftLinear rightLinear : LinearForm)
    (leftCoeff rightCoeff anchorCoeff : Fin 3 → F₂)
    (anchorLinear companionLinear : LinearForm) (rho : F₂),
    g =
      (affineANF leftConst leftLinear + rationalANF leftCoeff) *
        (affineANF rightConst rightLinear + rationalANF rightCoeff) ∧
    quarticWedgeProbe (rationalTwo leftCoeff) (rationalTwo rightCoeff) = 0 ∧
    anchorCoeff ≠ 0 ∧
    anfThreeProjection g =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ∧
    vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ≠ 0 ∧
    anfTwoProjection g =
      rho • rationalTwo anchorCoeff +
        vectorWedge companionLinear anchorLinear +
        booleanContraction anchorLinear (rationalTwo anchorCoeff)

/-- The normalized seed has the manuscript's anchored cubic normal form and
the matching quadratic shadow. -/
theorem NormalizedEight.cubicSeedNormalForm
    {C : Circuit 8 8} (h : NormalizedEight C) :
    CubicSeedNormalForm (C.gate 3) := by
  rcases h.seedFactorData with
    ⟨leftAffine, rightAffine, leftCoeff, rightCoeff,
      hleftAffine, hrightAffine, _hleftRep, _hrightRep, hseed⟩
  rcases exists_affineANF_of_mem hleftAffine with
    ⟨leftConst, leftLinear, hleftAffineRep⟩
  rcases exists_affineANF_of_mem hrightAffine with
    ⟨rightConst, rightLinear, hrightAffineRep⟩
  have hseedRep : C.gate 3 =
      (affineANF leftConst leftLinear + rationalANF leftCoeff) *
        (affineANF rightConst rightLinear + rationalANF rightCoeff) := by
    simpa [rationalANF, hleftAffineRep, hrightAffineRep] using hseed
  have hquartic :
      quarticWedgeProbe (rationalTwo leftCoeff) (rationalTwo rightCoeff) = 0 := by
    have hz := h.seed_quarticProbe_eq_zero
    rw [hseedRep, lowProduct_quarticProjection] at hz
    exact hz
  have hcubicProjection :
      anfThreeProjection (C.gate 3) =
        rationalProductCubic leftLinear rightLinear leftCoeff rightCoeff := by
    rw [hseedRep]
    exact lowProduct_cubicProjection_of_quartic_zero
      leftConst rightConst leftLinear rightLinear leftCoeff rightCoeff hquartic
  have hcubicProduct :
      rationalProductCubic leftLinear rightLinear leftCoeff rightCoeff ≠ 0 := by
    intro hz
    apply h.seed_cubicProjection_ne_zero
    rw [hcubicProjection, hz]
  rcases low_product_quadratic_normal_form
      leftConst rightConst leftLinear rightLinear leftCoeff rightCoeff
      (rational_wedge_zero_of_probe_zero leftCoeff rightCoeff hquartic)
      hcubicProduct with
    ⟨anchorCoeff, anchorLinear, companionLinear, rho,
      hanchorCoeff, hcubic, hquadratic⟩
  have htwoProjection :
      anfTwoProjection (C.gate 3) =
        rationalProductQuadratic leftConst rightConst leftLinear rightLinear
          leftCoeff rightCoeff := by
    rw [hseedRep]
    exact lowProduct_quadraticProjection_of_quartic_zero
      leftConst rightConst leftLinear rightLinear leftCoeff rightCoeff hquartic
  refine
    ⟨leftConst, rightConst, leftLinear, rightLinear,
      leftCoeff, rightCoeff, anchorCoeff, anchorLinear, companionLinear, rho,
      hseedRep, hquartic, hanchorCoeff, ?_, ?_, ?_⟩
  · exact hcubicProjection.trans hcubic
  · rw [← hcubic, ← hcubicProjection]
    exact h.seed_cubicProjection_ne_zero
  · exact htwoProjection.trans hquadratic

/-- A degree-three ANF with zero cubic homogeneous part is in fact of
degree at most two. -/
theorem degreeLE_two_of_degreeLE_three_of_cubic_zero
    {p : ANF 8} (hp : DegreeLE 3 p)
    (hcubic : anfThreeProjection p = 0) : DegreeLE 2 p := by
  intro s hs
  by_cases hhigh : 3 < s.vars.card
  · exact hp s hhigh
  have hcard : s.vars.card = 3 := by omega
  rcases Finset.card_eq_three.mp hcard with
    ⟨i, j, k, hij, hik, hjk, hsvars⟩
  have hcoord := congrFun (congrFun (congrFun hcubic i) j) k
  have hseq : s = ⟨{i, j, k}⟩ := Monomial.ext hsvars
  subst s
  simpa [anfThreeProjection, hij, hik, hjk] using hcoord

/-- Coefficient reconstruction in degrees zero and one. -/
theorem mem_affine_of_degreeLE_two_of_twoProjection_zero
    {p : ANF 8} (hp : DegreeLE 2 p)
    (htwo : anfTwoProjection p = 0) : p ∈ affine 8 := by
  rw [← lowReconstruct_eq hp]
  apply Submodule.sum_mem
  intro s _
  split_ifs with hs
  · interval_cases hcard : s.vars.card
    · have hs0 : s.vars = ∅ := Finset.card_eq_zero.mp hcard
      rw [hs0]
      have hone : (monomial ∅ : ANF 8) = 1 := by
        rw [monomial, MonoidAlgebra.one_def]
        congr 1
      rw [hone]
      exact Submodule.smul_mem _ _ (one_mem_affine 8)
    · rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
      rw [hi]
      exact Submodule.smul_mem _ _ (X_mem_affine i)
    · rcases Finset.card_eq_two.mp hcard with ⟨i, j, hij, hsij⟩
      have hcoord := congrFun (congrFun htwo i) j
      have hcoeff : p.coeff s = 0 := by
        have hseq : s = ⟨{i, j}⟩ := Monomial.ext hsij
        subst s
        simpa [anfTwoProjection, hij] using hcoord
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

/-- A degree-at-most-two ANF whose quadratic shadow is in the rational-place
span belongs to the rational-low state `Aff + R`. -/
theorem mem_rationalLow_of_degreeLE_two_of_twoProjection_mem
    {p : ANF 8} (hp : DegreeLE 2 p)
    (htwo : anfTwoProjection p ∈ rationalPlaceTwoSpace) :
    p ∈ rationalLowSpace := by
  rw [rationalPlaceTwoSpace] at htwo
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂)
      (v := fun theta : Fin 3 => targetTwo (rationalPlaceCoeff theta))
      (x := anfTwoProjection p)).mp htwo with ⟨gamma, hgamma⟩
  have hgamma' : rationalTwo gamma = anfTwoProjection p := by
    rw [rationalTwo]
    simpa only [targetTwo_rationalPlaceCoeff] using hgamma
  let r := rationalANF gamma
  have hrDegree : DegreeLE 2 r := degreeLE_two_rationalANF gamma
  have hresTwo : anfTwoProjection (p + r) = 0 := by
    rw [map_add]
    change anfTwoProjection p + anfTwoProjection (rationalANF gamma) = 0
    rw [anfTwoProjection_rationalANF, hgamma']
    funext i j
    exact CharTwo.add_self_eq_zero _
  have hresAffine : p + r ∈ affine 8 :=
    mem_affine_of_degreeLE_two_of_twoProjection_zero
      (hp.add hrDegree) hresTwo
  have hrLow : r ∈ rationalLowSpace := by
    change rationalANF gamma ∈ rationalLowSpace
    simpa [representedLowFactor, affineANF, linearANF] using
      representedLowFactor_mem 0 0 gamma
  have hpEq : p = (p + r) + r := by
    rw [add_assoc, anf_add_self, add_zero]
  rw [hpEq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hresAffine) hrLow

/-- The manuscript's seed-coset representative `M (z + G)`, with all lower
terms absorbed into `Aff + R`. -/
def CubicSeedAnchoredForm (g : ANF 8) : Prop :=
  ∃ (anchorCoeff : Fin 3 → F₂) (anchorLinear companionLinear : LinearForm)
    (correction : ANF 8),
    anchorCoeff ≠ 0 ∧
    vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ≠ 0 ∧
    correction ∈ rationalLowSpace ∧
    g + correction =
      linearANF anchorLinear *
        (linearANF companionLinear + rationalANF anchorCoeff)

/-- Upgrade the homogeneous seed normal form to an equality modulo the
rational-low state. -/
theorem NormalizedEight.cubicSeedAnchoredForm
    {C : Circuit 8 8} (h : NormalizedEight C) :
    CubicSeedAnchoredForm (C.gate 3) := by
  rcases h.cubicSeedNormalForm with
    ⟨_leftConst, _rightConst, _leftLinear, _rightLinear,
      _leftCoeff, _rightCoeff, anchorCoeff, anchorLinear, companionLinear,
      rho, _hseedRep, _hquartic, hanchorCoeff, hcubic, hcubicNonzero,
      hquadratic⟩
  let model := linearANF anchorLinear *
    (linearANF companionLinear + rationalANF anchorCoeff)
  let correction := C.gate 3 + model
  have hlinearAnchor : DegreeLE 1 (linearANF anchorLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 anchorLinear
  have hlinearCompanion : DegreeLE 1 (linearANF companionLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 companionLinear
  have hmodelDegree : DegreeLE 3 model := by
    exact hlinearAnchor.mul
      (hlinearCompanion.mono (by omega) |>.add
        (degreeLE_two_rationalANF anchorCoeff))
  have hmodelCubic : anfThreeProjection model =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) := by
    dsimp [model]
    rw [mul_add, map_add, anfThreeProjection_linear_mul_linear,
      anfThreeProjection_linear_mul_rational, zero_add]
  have hcorrectionCubic : anfThreeProjection correction = 0 := by
    dsimp [correction]
    rw [map_add, hcubic, hmodelCubic]
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcorrectionDegree : DegreeLE 2 correction :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero
      (h.seed_degreeLE_three.add hmodelDegree) hcorrectionCubic
  have hmodelQuadratic : anfTwoProjection model =
      vectorWedge companionLinear anchorLinear +
        booleanContraction anchorLinear (rationalTwo anchorCoeff) := by
    dsimp [model]
    rw [mul_add, map_add, anfTwoProjection_linear_mul_linear,
      anfTwoProjection_linear_mul_rational,
      vectorWedge_comm anchorLinear companionLinear]
  have hcorrectionQuadratic : anfTwoProjection correction =
      rho • rationalTwo anchorCoeff := by
    dsimp [correction]
    rw [map_add, hquadratic, hmodelQuadratic]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hcorrectionTwoMem :
      anfTwoProjection correction ∈ rationalPlaceTwoSpace := by
    rw [hcorrectionQuadratic]
    exact Submodule.smul_mem _ _ (rationalTwo_mem anchorCoeff)
  have hcorrectionLow : correction ∈ rationalLowSpace :=
    mem_rationalLow_of_degreeLE_two_of_twoProjection_mem
      hcorrectionDegree hcorrectionTwoMem
  refine ⟨anchorCoeff, anchorLinear, companionLinear, correction,
    hanchorCoeff, hcubicNonzero, hcorrectionLow, ?_⟩
  dsimp [correction]
  rw [← add_assoc, anf_add_self, zero_add]

/-- Multiplication by a quadratic target sees only the cubic homogeneous
part in degree five. -/
theorem anfQuinticAnchorProbe_mul_target_congr_of_cubic
    {p q : ANF 8} (hp : DegreeLE 3 p) (hq : DegreeLE 3 q)
    (hcubic : anfThreeProjection p = anfThreeProjection q)
    (c : TargetCoeff) :
    anfQuinticAnchorProbe (p * targetANF c) =
      anfQuinticAnchorProbe (q * targetANF c) := by
  have hpqCubic : anfThreeProjection (p + q) = 0 := by
    rw [map_add, hcubic]
    funext i j k
    exact CharTwo.add_self_eq_zero _
  have hpqLow : DegreeLE 2 (p + q) :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero (hp.add hq) hpqCubic
  have hprobe :
      anfQuinticAnchorProbe ((p + q) * targetANF c) = 0 :=
    anfQuinticAnchorProbe_low_mul_target_zero hpqLow c
  rw [add_mul, map_add] at hprobe
  calc
    anfQuinticAnchorProbe (p * targetANF c) =
        (anfQuinticAnchorProbe (p * targetANF c) +
          anfQuinticAnchorProbe (q * targetANF c)) +
            anfQuinticAnchorProbe (q * targetANF c) := by
      symm
      rw [add_assoc]
      have hself :
          anfQuinticAnchorProbe (q * targetANF c) +
              anfQuinticAnchorProbe (q * targetANF c) = 0 := by
        funext k
        exact CharTwo.add_self_eq_zero _
      rw [hself, add_zero]
    _ = anfQuinticAnchorProbe (q * targetANF c) := by rw [hprobe]; simp

/-- Classified algebraic output of a seed-using useful child at a specified
rational place.  Indexing by the place keeps every later normalization tied
to the very same feedback witness. -/
@[expose]
def SeedUsingCubicClassifiedFormAt (g : ANF 8) (theta : Fin 3) : Prop :=
  ∃ (correction factor target : ANF 8)
    (targetConst factorConst : F₂)
    (targetLinear factorLinear : LinearForm)
    (targetCoeff : TargetCoeff) (factorCoeff : Fin 3 → F₂)
    (eps : F₂),
    correction ∈ rationalLowSpace ∧
    factor ∈ rationalLowSpace ∧
    target = (g + correction) * factor ∧
    target ∈ targetAmbient 8 (mulTarget 4) ∧
    target ∉ rationalLowSpace ∧
    target = affineANF targetConst targetLinear + targetANF targetCoeff ∧
    factor = affineANF factorConst factorLinear + rationalANF factorCoeff ∧
    ¬ IsRationalCoeff targetCoeff ∧
    VanishesOnQuarticAnnihilatorProbe targetCoeff factorCoeff ∧
    (g + correction) * target = target ∧
    target * factor = target ∧
    factorCoeff = rationalSingleton theta ∧
    targetCoeff = rationalTangentAt theta eps

/-- Classified algebraic output of a seed-using useful child after quartic
exclusion.  Right idempotence makes the low factor a rational singleton and
the new target its first tangent. -/
@[expose] def SeedUsingCubicClassifiedForm (g : ANF 8) : Prop :=
  ∃ theta : Fin 3, SeedUsingCubicClassifiedFormAt g theta

/-- A seed-using branch of the first useful child has the classified cubic
feedback form. -/
theorem NormalizedEight.seedUsingCubicClassifiedForm_of_child
    {C : Circuit 8 8} (h : NormalizedEight C)
    {target representative shift : ANF 8}
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetOld : target ∉ circuitFlag C 4)
    (hshift : shift ∈ circuitFlag C 4)
    (htargetEq : target = shift + representative)
    (hseedUsing : IsSeedUsingProduct (C.gate 3) representative) :
    SeedUsingCubicClassifiedForm (C.gate 3) := by
  rcases h.seedUsingTargetWitness htarget htargetOld hshift htargetEq
      hseedUsing with
    ⟨correction, factor, feedbackTarget, hcorrection, hfactorLow,
      hfeedbackTarget, hfeedbackAmbient, hfeedbackNotLow⟩
  rcases seedUsing_idempotence hfeedbackTarget with ⟨hleft, hright⟩
  rcases quartic_data_of_right_idempotence
      hfeedbackAmbient hfeedbackNotLow hfactorLow hright with
    ⟨targetConst, factorConst, targetLinear, factorLinear,
      targetCoeff, factorCoeff, htargetRep, hfactorRep,
      htargetNonrational, hann⟩
  have hfactorCoeff : factorCoeff ≠ 0 :=
    seedUsing_factorCoeff_ne_zero_of_cubic
      h.seed_cubicProjection_ne_zero hcorrection hfeedbackTarget
      hfeedbackAmbient hfeedbackNotLow htargetRep hfactorRep
      htargetNonrational hright
  rcases rational_target_annihilator_classification
      factorCoeff targetCoeff hfactorCoeff htargetNonrational hann with
    ⟨theta, eps, hsingleton, htangent⟩
  exact
    ⟨theta, correction, factor, feedbackTarget, targetConst, factorConst,
      targetLinear, factorLinear, targetCoeff, factorCoeff, eps,
      hcorrection, hfactorLow, hfeedbackTarget, hfeedbackAmbient,
      hfeedbackNotLow, htargetRep, hfactorRep, htargetNonrational,
      hann, hleft, hright, hsingleton, htangent⟩

/-- Degree five in the left idempotence identity forces a rational
cubic to share the zero-place anchor of a tangent target. -/
theorem cubic_anchor_zero_of_left_idempotence
    {g correction target : ANF 8}
    {targetConst eps : F₂} {targetLinear anchorLinear : LinearForm}
    {anchorCoeff : Fin 3 → F₂}
    (hg : DegreeLE 3 g)
    (hcubic : anfThreeProjection g =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff))
    (hcorrection : correction ∈ rationalLowSpace)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hleft : (g + correction) * target = target) :
    vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) =
      vectorWedgeTwo (anchorCoeff 0 • anchorLinear)
        (rationalPlaceTwo 0) := by
  have hcorrectionDegree : DegreeLE 2 correction :=
    degreeLE_two_of_mem_rationalLow hcorrection
  have htargetAffineDegree :
      DegreeLE 1 (affineANF targetConst targetLinear) :=
    degreeLE_one_affineANF targetConst targetLinear
  have htargetQuadraticDegree :
      DegreeLE 2 (targetANF (rationalTangentAt 0 eps)) :=
    degreeLE_two_targetANF _
  have htargetAffineProbe :
      anfQuinticAnchorProbe (affineANF targetConst targetLinear) = 0 :=
    anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
      (htargetAffineDegree.mono (by omega))
  have htargetQuadraticProbe :
      anfQuinticAnchorProbe (targetANF (rationalTangentAt 0 eps)) = 0 :=
    anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
      (htargetQuadraticDegree.mono (by omega))
  have hgAffineProbe :
      anfQuinticAnchorProbe
        (g * affineANF targetConst targetLinear) = 0 :=
    anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
      (by simpa using hg.mul htargetAffineDegree)
  have hcorrectionAffineProbe :
      anfQuinticAnchorProbe
        (correction * affineANF targetConst targetLinear) = 0 :=
    anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
      ((hcorrectionDegree.mul htargetAffineDegree).mono (by omega))
  have hcorrectionTargetProbe :
      anfQuinticAnchorProbe
        (correction * targetANF (rationalTangentAt 0 eps)) = 0 :=
    anfQuinticAnchorProbe_low_mul_target_zero hcorrectionDegree _
  have hprobeIdentity := congrArg anfQuinticAnchorProbe hleft
  rw [htarget] at hprobeIdentity
  simp only [add_mul, mul_add, map_add] at hprobeIdentity
  rw [hgAffineProbe, hcorrectionAffineProbe, hcorrectionTargetProbe,
    htargetAffineProbe, htargetQuadraticProbe] at hprobeIdentity
  have hgTargetProbe :
      anfQuinticAnchorProbe
        (g * targetANF (rationalTangentAt 0 eps)) = 0 := by
    simpa using hprobeIdentity
  let cubicModel := linearANF anchorLinear * rationalANF anchorCoeff
  have hcubicModelDegree : DegreeLE 3 cubicModel := by
    have hlinear : DegreeLE 1 (linearANF anchorLinear) := by
      simpa [affineANF] using degreeLE_one_affineANF 0 anchorLinear
    exact hlinear.mul (degreeLE_two_rationalANF anchorCoeff)
  have hcubicModelProjection :
      anfThreeProjection cubicModel =
        vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) := by
    exact anfThreeProjection_linear_mul_rational anchorLinear anchorCoeff
  have hprobeCongr := anfQuinticAnchorProbe_mul_target_congr_of_cubic
    hg hcubicModelDegree (hcubic.trans hcubicModelProjection.symm)
      (rationalTangentAt 0 eps)
  have hcubicModelProbe :
      anfQuinticAnchorProbe
        (cubicModel * targetANF (rationalTangentAt 0 eps)) = 0 := by
    rw [← hprobeCongr]
    exact hgTargetProbe
  have hann : cubicAnchorWedgeProbe
      (vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff))
      (targetTwo (rationalTangentAt 0 eps)) = 0 := by
    rw [← anfQuinticAnchorProbe_linear_rational_zero_tangent]
    exact hcubicModelProbe
  exact cubicAnchorProbe_zero_tangent_classification
    anchorLinear anchorCoeff eps hann

/-- The three place-normalizing changes of variables are involutions on
linear forms. -/
theorem normalizePlaceLinear_involutive
    (theta : Fin 3) (ell : LinearForm) :
    normalizePlaceLinear theta (normalizePlaceLinear theta ell) = ell := by
  funext i
  fin_cases theta <;> fin_cases i <;>
    simp [normalizePlaceLinear, inputPlaceChange, Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

/-- The corresponding permutation of rational-place coefficients is also
an involution. -/
theorem normalizeRationalCoeff_involutive
    (theta : Fin 3) (alpha : Fin 3 → F₂) :
    normalizeRationalCoeff theta (normalizeRationalCoeff theta alpha) =
      alpha := by
  funext i
  fin_cases theta <;> fin_cases i <;> rfl

/-- Place normalization preserves the rational-low state. -/
theorem anfPlaceNormalize_mem_rationalLow
    (theta : Fin 3) {p : ANF 8} (hp : p ∈ rationalLowSpace) :
    anfPlaceNormalize theta p ∈ rationalLowSpace := by
  rcases exists_lowProduct_rep_of_mem_rationalLow hp with
    ⟨a, ell, alpha, hpRep⟩
  rw [hpRep]
  change anfPlaceNormalize theta
      (representedLowFactor a ell alpha) ∈ rationalLowSpace
  rw [anfPlaceNormalize_representedLowFactor]
  exact representedLowFactor_mem _ _ _

/-- Nonzero anchored rational cubics remain nonzero under place
normalization.  The proof uses involutivity and rational-low reconstruction,
not a rank computation. -/
theorem normalized_anchored_cubic_ne_zero
    (theta : Fin 3) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (hnonzero : vectorWedgeTwo ell (rationalTwo alpha) ≠ 0) :
    vectorWedgeTwo (normalizePlaceLinear theta ell)
      (rationalTwo (normalizeRationalCoeff theta alpha)) ≠ 0 := by
  intro hzero
  let ell' := normalizePlaceLinear theta ell
  let alpha' := normalizeRationalCoeff theta alpha
  let q' := linearANF ell' * rationalANF alpha'
  have hqDegree : DegreeLE 3 q' := by
    have hlinear : DegreeLE 1 (linearANF ell') := by
      simpa [affineANF] using degreeLE_one_affineANF 0 ell'
    exact hlinear.mul (degreeLE_two_rationalANF alpha')
  have hqCubic : anfThreeProjection q' = 0 := by
    dsimp [q']
    rw [anfThreeProjection_linear_mul_rational, hzero]
  have hqDegreeTwo : DegreeLE 2 q' :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero hqDegree hqCubic
  have hqTwo : anfTwoProjection q' =
      booleanContraction ell' (rationalTwo alpha') := by
    exact anfTwoProjection_linear_mul_rational ell' alpha'
  have hqTwoMem : anfTwoProjection q' ∈ rationalPlaceTwoSpace := by
    rw [hqTwo]
    exact rational_contraction_mem_of_cubic_zero alpha' ell' hzero
  have hqLow : q' ∈ rationalLowSpace :=
    mem_rationalLow_of_degreeLE_two_of_twoProjection_mem hqDegreeTwo hqTwoMem
  have hnormalizeLow :
      anfPlaceNormalize theta q' ∈ rationalLowSpace :=
    anfPlaceNormalize_mem_rationalLow theta hqLow
  have hnormalizeQ : anfPlaceNormalize theta q' =
      linearANF ell * rationalANF alpha := by
    dsimp [q', ell', alpha']
    rw [map_mul, anfPlaceNormalize_linearANF,
      anfPlaceNormalize_rationalANF,
      normalizePlaceLinear_involutive,
      normalizeRationalCoeff_involutive]
  have hqOriginalLow :
      linearANF ell * rationalANF alpha ∈ rationalLowSpace := by
    rw [← hnormalizeQ]
    exact hnormalizeLow
  have hqOriginalCubic :
      anfThreeProjection (linearANF ell * rationalANF alpha) = 0 :=
    anfThreeProjection_eq_zero_of_mem_targetAmbient
      (rationalLowSpace_le_targetAmbient hqOriginalLow)
  rw [anfThreeProjection_linear_mul_rational] at hqOriginalCubic
  exact hnonzero hqOriginalCubic

/-- Seed data after normalizing the specified classified feedback place to
zero. -/
def NormalizedCubicAnchorFormAt (theta : Fin 3) (g : ANF 8) : Prop :=
  ∃ (anchorCoeff : Fin 3 → F₂)
    (anchorLinear companionLinear : LinearForm) (correction : ANF 8),
    correction ∈ rationalLowSpace ∧
    anfPlaceNormalize theta g + correction =
      linearANF anchorLinear *
        (linearANF companionLinear + rationalANF anchorCoeff) ∧
    anfThreeProjection (anfPlaceNormalize theta g) =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ∧
    vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ≠ 0 ∧
    vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) =
      vectorWedgeTwo (anchorCoeff 0 • anchorLinear)
        (rationalPlaceTwo 0)

/-- The normalized cubic anchor form holds at some rational place. -/
def NormalizedCubicAnchorForm (g : ANF 8) : Prop :=
  ∃ theta : Fin 3, NormalizedCubicAnchorFormAt theta g

/-- A classified seed-using feedback forces the normalized seed cubic to be
anchored at the feedback place. -/
theorem seedUsingCubicClassified_normalized_anchor_at
    {g : ANF 8} {theta : Fin 3}
    (hseed : CubicSeedAnchoredForm g)
    (hfeedback : SeedUsingCubicClassifiedFormAt g theta) :
    NormalizedCubicAnchorFormAt theta g := by
  rcases hseed with
    ⟨seedCoeff, seedLinear, seedCompanion, seedCorrection,
      _hseedCoeff, hseedCubicNonzero, hseedCorrectionLow, hseedEq⟩
  rcases hfeedback with
    ⟨feedbackCorrection, _factor, target, targetConst, _factorConst,
      targetLinear, _factorLinear, targetCoeff, _factorCoeff, eps,
      hfeedbackCorrectionLow, _hfactorLow, _htargetEq, _htargetAmbient,
      _htargetNotLow, htargetRep, _hfactorRep, _htargetNonrational,
      _hann, hleft, _hright, _hfactorSingleton, htargetTangent⟩
  let Phi := anfPlaceNormalize theta
  let anchorCoeff := normalizeRationalCoeff theta seedCoeff
  let anchorLinear := normalizePlaceLinear theta seedLinear
  let companionLinear := normalizePlaceLinear theta seedCompanion
  have hseedNorm : Phi g + Phi seedCorrection =
      linearANF anchorLinear *
        (linearANF companionLinear + rationalANF anchorCoeff) := by
    calc
      Phi g + Phi seedCorrection = Phi (g + seedCorrection) :=
        (map_add Phi g seedCorrection).symm
      _ = Phi (linearANF seedLinear *
          (linearANF seedCompanion + rationalANF seedCoeff)) :=
        congrArg Phi hseedEq
      _ = linearANF anchorLinear *
          (linearANF companionLinear + rationalANF anchorCoeff) := by
        rw [map_mul, map_add, anfPlaceNormalize_linearANF,
          anfPlaceNormalize_linearANF, anfPlaceNormalize_rationalANF]
  have hseedCorrectionNormLow :
      Phi seedCorrection ∈ rationalLowSpace :=
    anfPlaceNormalize_mem_rationalLow theta hseedCorrectionLow
  have hseedCorrectionNormDegree : DegreeLE 2 (Phi seedCorrection) :=
    degreeLE_two_of_mem_rationalLow hseedCorrectionNormLow
  have hseedNormEq : Phi g =
      linearANF anchorLinear *
          (linearANF companionLinear + rationalANF anchorCoeff) +
        Phi seedCorrection := by
    calc
      Phi g = (Phi g + Phi seedCorrection) + Phi seedCorrection := by
        rw [add_assoc, anf_add_self, add_zero]
      _ = linearANF anchorLinear *
            (linearANF companionLinear + rationalANF anchorCoeff) +
          Phi seedCorrection :=
        congrArg (fun p => p + Phi seedCorrection) hseedNorm
  have hanchorLinearDegree : DegreeLE 1 (linearANF anchorLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 anchorLinear
  have hcompanionLinearDegree : DegreeLE 1 (linearANF companionLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 companionLinear
  have hmodelDegree : DegreeLE 3
      (linearANF anchorLinear *
        (linearANF companionLinear + rationalANF anchorCoeff)) := by
    exact hanchorLinearDegree.mul
      ((hcompanionLinearDegree.mono (by omega)).add
        (degreeLE_two_rationalANF anchorCoeff))
  have hgNormDegree : DegreeLE 3 (Phi g) := by
    rw [hseedNormEq]
    exact hmodelDegree.add (hseedCorrectionNormDegree.mono (by omega))
  have hseedCorrectionNormCubic :
      anfThreeProjection (Phi seedCorrection) = 0 :=
    anfThreeProjection_eq_zero_of_mem_targetAmbient
      (rationalLowSpace_le_targetAmbient hseedCorrectionNormLow)
  have hmodelCubic : anfThreeProjection
      (linearANF anchorLinear *
        (linearANF companionLinear + rationalANF anchorCoeff)) =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) := by
    rw [mul_add, map_add, anfThreeProjection_linear_mul_linear,
      anfThreeProjection_linear_mul_rational, zero_add]
  have hgNormCubic : anfThreeProjection (Phi g) =
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) := by
    rw [hseedNormEq, map_add, hmodelCubic, hseedCorrectionNormCubic,
      add_zero]
  have hgNormCubicNonzero :
      vectorWedgeTwo anchorLinear (rationalTwo anchorCoeff) ≠ 0 :=
    normalized_anchored_cubic_ne_zero theta seedLinear seedCoeff
      hseedCubicNonzero
  have hfeedbackCorrectionNormLow :
      Phi feedbackCorrection ∈ rationalLowSpace :=
    anfPlaceNormalize_mem_rationalLow theta hfeedbackCorrectionLow
  have htargetNorm : Phi target =
      affineANF targetConst (normalizePlaceLinear theta targetLinear) +
        targetANF (rationalTangentAt 0 eps) := by
    rw [htargetRep, map_add, anfPlaceNormalize_affineANF,
      htargetTangent, anfPlaceNormalize_tangent_self]
  have hleftNorm :
      (Phi g + Phi feedbackCorrection) * Phi target = Phi target := by
    calc
      (Phi g + Phi feedbackCorrection) * Phi target =
          Phi (g + feedbackCorrection) * Phi target := by rw [map_add]
      _ = Phi ((g + feedbackCorrection) * target) :=
        (map_mul Phi _ _).symm
      _ = Phi target := congrArg Phi hleft
  have hanchor := cubic_anchor_zero_of_left_idempotence
    hgNormDegree hgNormCubic
      hfeedbackCorrectionNormLow htargetNorm hleftNorm
  exact ⟨anchorCoeff, anchorLinear, companionLinear,
    Phi seedCorrection, hseedCorrectionNormLow, hseedNorm,
    hgNormCubic, hgNormCubicNonzero, hanchor⟩

theorem seedUsingCubicClassified_normalized_anchor
    {g : ANF 8}
    (hseed : CubicSeedAnchoredForm g)
    (hfeedback : SeedUsingCubicClassifiedForm g) :
    NormalizedCubicAnchorForm g := by
  rcases hfeedback with ⟨theta, hfeedback⟩
  exact ⟨theta,
    seedUsingCubicClassified_normalized_anchor_at hseed hfeedback⟩

/-- Canonical zero-place representative of the seed coset. -/
@[expose] def ZeroAnchoredCubicSeedForm (g : ANF 8) : Prop :=
  ∃ (anchorLinear companionLinear : LinearForm) (correction : ANF 8),
    correction ∈ rationalLowSpace ∧
    g + correction =
      linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) ∧
    vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) ≠ 0

/-- Extra rational-place components in an anchored cubic contribute only a
rational-low correction, so the seed coset has the canonical `M(z+E₀)`
representative. -/
theorem normalizedCubicAnchorForm_zeroRepresentative_at
    {g : ANF 8} {theta : Fin 3}
    (h : NormalizedCubicAnchorFormAt theta g) :
    ZeroAnchoredCubicSeedForm (anfPlaceNormalize theta g) := by
  rcases h with
    ⟨alpha, anchorLinear, companionLinear, correction,
      hcorrectionLow, hseedEq, _hgCubic, hcubicNonzero, hanchor⟩
  have halphaZero : alpha 0 = 1 := by
    rcases f2_eq_zero_or_one (alpha 0) with hzero | hone
    · exfalso
      apply hcubicNonzero
      rw [hanchor, hzero, zero_smul, vectorWedgeTwo_zero_left]
    · exact hone
  have hanchor' :
      vectorWedgeTwo anchorLinear (rationalTwo alpha) =
        vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) := by
    simpa [halphaZero] using hanchor
  have hzeroCubicNonzero :
      vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) ≠ 0 := by
    rw [← hanchor']
    exact hcubicNonzero
  let qAlpha := linearANF anchorLinear *
    (linearANF companionLinear + rationalANF alpha)
  let qZero := linearANF anchorLinear *
    (linearANF companionLinear + rationalANF (rationalSingleton 0))
  let delta := alpha + rationalSingleton 0
  have hrationalDelta : rationalTwo delta =
      rationalTwo alpha + rationalTwo (rationalSingleton 0) := by
    dsimp [delta]
    rw [rationalTwo, rationalTwo, rationalTwo]
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hwedgeDelta :
      vectorWedgeTwo anchorLinear (rationalTwo delta) = 0 := by
    rw [hrationalDelta, vectorWedgeTwo_add_right_h,
      hanchor', rationalTwo_singleton_zero, rationalPlaceTwo_zero_eq]
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hlinearDegree : DegreeLE 1 (linearANF anchorLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 anchorLinear
  have hcompanionDegree : DegreeLE 1 (linearANF companionLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 companionLinear
  have hqAlphaDegree : DegreeLE 3 qAlpha := by
    exact hlinearDegree.mul
      ((hcompanionDegree.mono (by omega)).add
        (degreeLE_two_rationalANF alpha))
  have hqZeroDegree : DegreeLE 3 qZero := by
    exact hlinearDegree.mul
      ((hcompanionDegree.mono (by omega)).add
        (degreeLE_two_rationalANF (rationalSingleton 0)))
  have hqAlphaCubic : anfThreeProjection qAlpha =
      vectorWedgeTwo anchorLinear (rationalTwo alpha) := by
    dsimp [qAlpha]
    rw [mul_add, map_add, anfThreeProjection_linear_mul_linear,
      anfThreeProjection_linear_mul_rational, zero_add]
  have hqZeroCubic : anfThreeProjection qZero =
      vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) := by
    dsimp [qZero]
    rw [mul_add, map_add, anfThreeProjection_linear_mul_linear,
      anfThreeProjection_linear_mul_rational, zero_add,
      rationalTwo_singleton_zero, rationalPlaceTwo_zero_eq]
  have hqDiffCubic : anfThreeProjection (qAlpha + qZero) = 0 := by
    rw [map_add, hqAlphaCubic, hqZeroCubic, hanchor']
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hqDiffDegree : DegreeLE 2 (qAlpha + qZero) :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero
      (hqAlphaDegree.add hqZeroDegree) hqDiffCubic
  have hqAlphaTwo : anfTwoProjection qAlpha =
      vectorWedge anchorLinear companionLinear +
        booleanContraction anchorLinear (rationalTwo alpha) := by
    dsimp [qAlpha]
    rw [mul_add, map_add, anfTwoProjection_linear_mul_linear,
      anfTwoProjection_linear_mul_rational]
  have hqZeroTwo : anfTwoProjection qZero =
      vectorWedge anchorLinear companionLinear +
        booleanContraction anchorLinear
          (rationalTwo (rationalSingleton 0)) := by
    dsimp [qZero]
    rw [mul_add, map_add, anfTwoProjection_linear_mul_linear,
      anfTwoProjection_linear_mul_rational]
  have hqDiffTwo : anfTwoProjection (qAlpha + qZero) =
      booleanContraction anchorLinear (rationalTwo delta) := by
    rw [map_add, hqAlphaTwo, hqZeroTwo, hrationalDelta,
      booleanContraction_add_right_h]
    funext i j
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hqDiffTwoMem :
      anfTwoProjection (qAlpha + qZero) ∈ rationalPlaceTwoSpace := by
    rw [hqDiffTwo]
    exact rational_contraction_mem_of_cubic_zero
      delta anchorLinear hwedgeDelta
  have hqDiffLow : qAlpha + qZero ∈ rationalLowSpace :=
    mem_rationalLow_of_degreeLE_two_of_twoProjection_mem
      hqDiffDegree hqDiffTwoMem
  let correction' := correction + (qAlpha + qZero)
  have hcorrection'Low : correction' ∈ rationalLowSpace :=
    Submodule.add_mem _ hcorrectionLow hqDiffLow
  refine ⟨anchorLinear, companionLinear, correction',
    hcorrection'Low, ?_, hzeroCubicNonzero⟩
  dsimp [correction']
  calc
    anfPlaceNormalize theta g + (correction + (qAlpha + qZero)) =
        (anfPlaceNormalize theta g + correction) + qAlpha + qZero := by
      abel
    _ = qAlpha + qAlpha + qZero := by rw [hseedEq]
    _ = qZero := by rw [anf_add_self, zero_add]
    _ = linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) := rfl

theorem normalizedCubicAnchorForm_zeroRepresentative
    {g : ANF 8} (h : NormalizedCubicAnchorForm g) :
    ∃ theta : Fin 3,
      ZeroAnchoredCubicSeedForm (anfPlaceNormalize theta g) := by
  rcases h with ⟨theta, h⟩
  exact ⟨theta, normalizedCubicAnchorForm_zeroRepresentative_at h⟩

/-- Circuit-level endpoint of the cubic annihilator/degree-five argument for
a seed-using first child. -/
theorem NormalizedEight.seedUsingFirstFeedback_zeroAnchor
    {C : Circuit 8 8} (h : NormalizedEight C)
    {target representative shift : ANF 8}
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetOld : target ∉ circuitFlag C 4)
    (hshift : shift ∈ circuitFlag C 4)
    (htargetEq : target = shift + representative)
    (hseedUsing : IsSeedUsingProduct (C.gate 3) representative) :
    ∃ theta : Fin 3,
      ZeroAnchoredCubicSeedForm
        (anfPlaceNormalize theta (C.gate 3)) := by
  have hclassified := h.seedUsingCubicClassifiedForm_of_child
    htarget htargetOld hshift htargetEq hseedUsing
  have hnormalized := seedUsingCubicClassified_normalized_anchor
    h.cubicSeedAnchoredForm hclassified
  exact normalizedCubicAnchorForm_zeroRepresentative hnormalized

end

end N4
end UnrestrictedBooleanMul
