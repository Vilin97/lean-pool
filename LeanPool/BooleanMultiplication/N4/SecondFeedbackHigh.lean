/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.JetShadow

/-!
# The cancelled-high low--low branch

The second low--low gate can cancel the cubic seed only through a common
first-jet target direction.  Its quadratic shadow is then a sum of a term
supported on `K₀` and at most two exterior directions.  Jet separation sends
the resulting target back to the feedback state.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem normalizedFirstJetVector_not_mem_anchorPlane
    (pa pb ja jb : F₂) (hjet : ja ≠ 0 ∨ jb ≠ 0) :
    normalizedFirstJetVector pa pb ja jb ∉ anchorPlane := by
  intro hmem
  rcases (Submodule.mem_span_range_iff_exists_fun
    (R := F₂) (v := ![aLinear 0, bLinear 0])
    (x := normalizedFirstJetVector pa pb ja jb)).mp hmem with
    ⟨f, hf⟩
  have hja := congrFun hf 1
  have hjb := congrFun hf 5
  simp [normalizedFirstJetVector, Fin.sum_univ_succ, aLinear, bLinear, aCoord, bCoord,
    Pi.basisFun] at hja hjb
  rcases hjet with hja0 | hjb0
  · exact hja0 hja.symm
  · exact hjb0 hjb.symm

theorem normalizedFirstJet_span_two_ne_anchorPlane
    (pa pb ja jb : F₂) (N : LinearForm)
    (hjet : ja ≠ 0 ∨ jb ≠ 0) :
    Submodule.span F₂
      (Set.range ![normalizedFirstJetVector pa pb ja jb, N]) ≠
        anchorPlane := by
  intro heq
  apply normalizedFirstJetVector_not_mem_anchorPlane pa pb ja jb hjet
  rw [← heq]
  exact Submodule.subset_span ⟨0, by simp⟩

theorem rationalCoeffRep_mem_feedbackCoeffSpace (alpha : Fin 3 → F₂) :
    rationalCoeffRep alpha ∈ feedbackCoeffSpace := by
  apply (mem_feedbackCoeffSpace_iff_exists_rep _).mpr
  let q : FeedbackCoord := ![alpha 0, 0, alpha 2, alpha 1]
  refine ⟨q, ?_⟩
  funext i
  fin_cases i <;>
    simp [q, rationalCoeffRep, feedbackCoeffRep, rZeroCoeff, rOneCoeff, rInfinityCoeff,
      targetBasis, Pi.basisFun]
  ring

theorem SupportedK0Two.booleanContraction
    (ell : LinearForm) {k : TwoForm} (hk : SupportedK0Two k) :
    SupportedK0Two (booleanContraction ell k) := by
  intro z j hz
  unfold UnrestrictedBooleanMul.N4.booleanContraction
  rw [hk z j hz, mul_zero]

theorem SupportedK0Two.rationalPlaceTwo_zero :
    SupportedK0Two (rationalPlaceTwo 0) := by
  intro z j hz
  rcases hz with rfl | rfl | rfl | rfl <;> fin_cases j <;>
    decide

theorem SupportedK0Two.booleanContraction_zeroPlace
    (M : LinearForm) :
    SupportedK0Two
      (UnrestrictedBooleanMul.N4.booleanContraction M
        (rationalPlaceTwo 0)) :=
  SupportedK0Two.booleanContraction M
    SupportedK0Two.rationalPlaceTwo_zero

theorem SupportedK0Two.targetTwo_feedback_firstPlane
    (q : FeedbackCoord) (hq : InFirstJetPlane q) :
    SupportedK0Two (targetTwo (feedbackCoeffRep q)) := by
  rw [feedbackCoeffRep_firstPlane q hq]
  intro z j hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    fin_cases j <;>
    simp [targetTwo, targetBasis, Pi.basisFun]

private theorem mulTargetZero_coordinateQuadratic :
    Mul 4 0 =
      linearANF (coordinateLinear 0) *
        linearANF (coordinateLinear 4) := by
  rw [linearANF_coordinate, linearANF_coordinate,
    mul_target_zero_anf]
  simp [X, monomial_mul]

private theorem mulTargetOne_coordinateQuadratic :
    Mul 4 1 =
      linearANF (coordinateLinear 0) *
          linearANF (coordinateLinear 5) +
        linearANF (coordinateLinear 1) *
          linearANF (coordinateLinear 4) := by
  rw [linearANF_coordinate, linearANF_coordinate,
    linearANF_coordinate, linearANF_coordinate,
    mul_target_one_anf]
  simp [X, monomial_mul]

theorem SupportedK0Two.affine_mul_coordinateQuadratic
    (a : F₂) (ell u v : LinearForm)
    (hu : InK0Linear u) (hv : InK0Linear v)
    (hdisjoint : pointwiseLinearProduct u v = 0) :
    SupportedK0Two
      (anfTwoProjection
        (affineANF a ell * (linearANF u * linearANF v))) := by
  have hw : SupportedK0Two
      (UnrestrictedBooleanMul.N4.vectorWedge u v) :=
    SupportedK0Two.vectorWedge hu hv
  rw [affineANF, add_mul, smul_mul_assoc, one_mul,
    map_add, map_smul, anfTwoProjection_linear_mul_linear,
    anfTwoProjection_linear_mul_quadratic ell u v hdisjoint]
  exact (SupportedK0Two.smul a hw).add
    (SupportedK0Two.booleanContraction ell hw)

theorem SupportedK0Two.affine_mul_feedback_firstPlane
    (a : F₂) (ell : LinearForm) (q : FeedbackCoord)
    (hq : InFirstJetPlane q) :
    SupportedK0Two
      (anfTwoProjection
        (affineANF a ell * targetANF (feedbackCoeffRep q))) := by
  have h0 : InK0Linear (coordinateLinear 0) := by
    simp [InK0Linear, coordinateLinear]
  have h1 : InK0Linear (coordinateLinear 1) := by
    simp [InK0Linear, coordinateLinear]
  have h4 : InK0Linear (coordinateLinear 4) := by
    simp [InK0Linear, coordinateLinear]
  have h5 : InK0Linear (coordinateLinear 5) := by
    simp [InK0Linear, coordinateLinear]
  have hd04 : pointwiseLinearProduct
      (coordinateLinear 0) (coordinateLinear 4) = 0 := by decide
  have hd05 : pointwiseLinearProduct
      (coordinateLinear 0) (coordinateLinear 5) = 0 := by decide
  have hd14 : pointwiseLinearProduct
      (coordinateLinear 1) (coordinateLinear 4) = 0 := by decide
  have h04 := SupportedK0Two.affine_mul_coordinateQuadratic
    a ell _ _ h0 h4 hd04
  have h05 := SupportedK0Two.affine_mul_coordinateQuadratic
    a ell _ _ h0 h5 hd05
  have h14 := SupportedK0Two.affine_mul_coordinateQuadratic
    a ell _ _ h1 h4 hd14
  rw [targetANF_feedback_firstPlane q hq,
    mulTargetZero_coordinateQuadratic,
    mulTargetOne_coordinateQuadratic]
  simp only [mul_add, mul_smul_comm, map_add, map_smul]
  exact (SupportedK0Two.smul (q 0) h04).add
    (SupportedK0Two.smul (q 1) (h05.add h14))

theorem SupportedK0Two.feedback_firstPlane_mul_affine
    (q : FeedbackCoord) (a : F₂) (ell : LinearForm)
    (hq : InFirstJetPlane q) :
    SupportedK0Two
      (anfTwoProjection
        (targetANF (feedbackCoeffRep q) * affineANF a ell)) := by
  rw [mul_comm]
  exact SupportedK0Two.affine_mul_feedback_firstPlane a ell q hq

theorem SupportedK0Two.feedback_firstPlane_mul_feedback_firstPlane
    (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c) :
    SupportedK0Two
      (anfTwoProjection
        (targetANF (feedbackCoeffRep q) *
          targetANF (feedbackCoeffRep c))) := by
  intro z j hz
  simpa [affineANF, linearANF] using
    firstPlane_product_two_outside 0 0 0 0 q c
      (by simp [InK0Linear]) (by simp [InK0Linear]) hq hc z hz j

/-- After removing the affine--affine wedge, a product whose two target
parts lie in the first-jet plane is wholly supported on `K₀`. -/
theorem feedbackProduct_twoShadow_supported
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c) :
    SupportedK0Two
      (anfTwoProjection
          ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
            (affineANF b m + targetANF (feedbackCoeffRep c))) +
        vectorWedge ell m) := by
  have hAT := SupportedK0Two.affine_mul_feedback_firstPlane
    a ell c hc
  have hTA := SupportedK0Two.feedback_firstPlane_mul_affine
    q b m hq
  have hTT := SupportedK0Two.feedback_firstPlane_mul_feedback_firstPlane
    q c hq hc
  have heq :
      anfTwoProjection
          ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
            (affineANF b m + targetANF (feedbackCoeffRep c))) +
          vectorWedge ell m =
        anfTwoProjection
            (affineANF a ell * targetANF (feedbackCoeffRep c)) +
          anfTwoProjection
            (targetANF (feedbackCoeffRep q) * affineANF b m) +
          anfTwoProjection
            (targetANF (feedbackCoeffRep q) *
              targetANF (feedbackCoeffRep c)) := by
    simp only [add_mul, mul_add, map_add]
    rw [anfTwoProjection_affine_mul_affine]
    funext i j
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [heq]
  exact (hAT.add hTA).add hTT

theorem feedbackCoeffRep_zero :
    feedbackCoeffRep (0 : FeedbackCoord) = 0 := by
  funext i
  simp [feedbackCoeffRep]

theorem targetANF_feedbackCoeffRep_zero :
    targetANF (feedbackCoeffRep (0 : FeedbackCoord)) = 0 := by
  rw [feedbackCoeffRep_zero]
  exact map_zero targetANFLinear

/-- A computational presentation of the feedback coefficient word.  It is
kept separate from the basis-vector presentation so the small fixed cubic
certificate below contains no classical `Pi.basisFun`. -/
def feedbackCoeffPure (q : FeedbackCoord) : TargetCoeff := fun s =>
  q 3 + (if s = 0 then q 0 else 0) +
    (if s = 1 then q 1 else 0) +
    (if s = 6 then q 2 else 0)

theorem feedbackCoeffRep_eq_pure (q : FeedbackCoord) :
    feedbackCoeffRep q = feedbackCoeffPure q := by
  funext s
  simp [feedbackCoeffRep, feedbackCoeffPure, targetBasis_apply, rOneCoeff_apply, eq_comm]
  ring

private theorem feedback_firstJet_scalar
    (a b c d lambda x0 x1 x2 x3 : F₂)
    (hlambda : lambda ≠ 0)
    (h01 : x0 * (d + b) + x1 * (d + a) = lambda)
    (h02 : x0 * d + x2 * (d + a) = 0)
    (h03 : x0 * d + x3 * (d + a) = 0)
    (h12 : x1 * d + x2 * (d + b) = 0)
    (h13 : x1 * d + x3 * (d + b) = 0)
    (h03last : x0 * (d + c) + x3 * d = 0)
    (h13last : x1 * (d + c) + x3 * d = 0) :
    c = 0 ∧ d = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  rcases f2_eq_zero_or_one d with rfl | rfl
  · rcases f2_eq_zero_or_one c with rfl | rfl
    · refine ⟨rfl, rfl, ?_, ?_⟩
      · rcases f2_eq_zero_or_one x2 with rfl | rfl
        · rfl
        · exfalso
          apply hlambda
          have ha : a = 0 := by linear_combination h02
          have hb : b = 0 := by linear_combination h12
          simpa [ha, hb] using h01.symm
      · rcases f2_eq_zero_or_one x3 with rfl | rfl
        · rfl
        · exfalso
          apply hlambda
          have ha : a = 0 := by linear_combination h03
          have hb : b = 0 := by linear_combination h13
          simpa [ha, hb] using h01.symm
    · exfalso
      apply hlambda
      have hx0 : x0 = 0 := by linear_combination h03last
      have hx1 : x1 = 0 := by linear_combination h13last
      simpa [hx0, hx1] using h01.symm
  · exfalso
    apply hlambda
    have hx0 : x0 = x2 * (1 + a) := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa using h02
    have hx1 : x1 = x2 * (1 + b) := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa using h12
    rw [hx0, hx1] at h01
    rw [← h01]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]

private theorem feedback_plane_outside_zero
    (a b x2 x3 : F₂) (hab : a ≠ 0 ∨ b ≠ 0)
    (h2a : x2 * a = 0) (h2b : x2 * b = 0)
    (h3a : x3 * a = 0) (h3b : x3 * b = 0) :
    x2 = 0 ∧ x3 = 0 := by
  rcases hab with ha | hb
  · exact ⟨(mul_eq_zero.mp h2a).resolve_right ha,
      (mul_eq_zero.mp h3a).resolve_right ha⟩
  · exact ⟨(mul_eq_zero.mp h2b).resolve_right hb,
      (mul_eq_zero.mp h3b).resolve_right hb⟩

private theorem commonFeedback_seedCubic_certificate :
    ∀ (pa pb ja jb : F₂) (q : FeedbackCoord) (N : LinearForm),
      (ja ≠ 0 ∨ jb ≠ 0) → q ≠ 0 →
      vectorWedgeTwo N (targetTwo (feedbackCoeffPure q)) =
        vectorWedgeTwo (normalizedFirstJetVector pa pb ja jb)
          (rationalPlaceTwo 0) →
      InFirstJetPlane q ∧ InK0Linear N := by
  change ∀ (pa pb ja jb : F₂) (q : FeedbackCoord) (N : LinearForm),
    (ja ≠ 0 ∨ jb ≠ 0) → q ≠ 0 →
    vectorWedgeTwo N (targetTwo (feedbackCoeffPure q)) =
      vectorWedgeTwo (normalizedFirstJetVector pa pb ja jb)
        (rationalPlaceTwo 0) →
    (q 2 = 0 ∧ q 3 = 0) ∧
      (N 2 = 0 ∧ N 3 = 0 ∧ N 6 = 0 ∧ N 7 = 0)
  intro pa pb ja jb q N hjet hq0 hcubic
  have hA01 : N 0 * (q 3 + q 1) + N 1 * (q 3 + q 0) = ja := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 1) 4
  have hA02 : N 0 * q 3 + N 2 * (q 3 + q 0) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 2) 4
  have hA03 : N 0 * q 3 + N 3 * (q 3 + q 0) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 3) 4
  have hA12 : N 1 * q 3 + N 2 * (q 3 + q 1) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 1) 2) 4
  have hA13 : N 1 * q 3 + N 3 * (q 3 + q 1) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 1) 3) 4
  have hA03last : N 0 * (q 3 + q 2) + N 3 * q 3 = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 3) 7
  have hA13last : N 1 * (q 3 + q 2) + N 3 * q 3 = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 1) 3) 7
  have hB01 : N 4 * (q 3 + q 1) + N 5 * (q 3 + q 0) = jb := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 4) 5
  have hB02 : N 4 * q 3 + N 6 * (q 3 + q 0) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 4) 6
  have hB03 : N 4 * q 3 + N 7 * (q 3 + q 0) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 4) 7
  have hB12 : N 5 * q 3 + N 6 * (q 3 + q 1) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 5) 6
  have hB13 : N 5 * q 3 + N 7 * (q 3 + q 1) = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 0) 5) 7
  have hB03last : N 4 * (q 3 + q 2) + N 7 * q 3 = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 3) 4) 7
  have hB13last : N 5 * (q 3 + q 2) + N 7 * q 3 = 0 := by
    simpa [vectorWedgeTwo, targetTwo, feedbackCoeffPure, normalizedFirstJetVector,
      rationalPlaceTwo, vectorWedge, placeA, placeB]
      using congrFun (congrFun (congrFun hcubic 3) 5) 7
  rcases hjet with hja | hjb
  · rcases feedback_firstJet_scalar (q 0) (q 1) (q 2) (q 3) ja
        (N 0) (N 1) (N 2) (N 3) hja hA01 hA02 hA03 hA12 hA13
        hA03last hA13last with ⟨hq2, hq3, hN2, hN3⟩
    have hab : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      rcases h with ⟨hq0c, hq1c⟩
      apply hq0
      funext i
      fin_cases i
      · exact hq0c
      · exact hq1c
      · exact hq2
      · exact hq3
    rcases feedback_plane_outside_zero (q 0) (q 1) (N 6) (N 7) hab
        (by simpa [hq3] using hB02) (by simpa [hq3] using hB12)
        (by simpa [hq3] using hB03) (by simpa [hq3] using hB13) with ⟨hN6, hN7⟩
    exact ⟨⟨hq2, hq3⟩, hN2, hN3, hN6, hN7⟩
  · rcases feedback_firstJet_scalar (q 0) (q 1) (q 2) (q 3) jb
        (N 4) (N 5) (N 6) (N 7) hjb hB01 hB02 hB03 hB12 hB13
        hB03last hB13last with ⟨hq2, hq3, hN6, hN7⟩
    have hab : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      rcases h with ⟨hq0c, hq1c⟩
      apply hq0
      funext i
      fin_cases i
      · exact hq0c
      · exact hq1c
      · exact hq2
      · exact hq3
    rcases feedback_plane_outside_zero (q 0) (q 1) (N 2) (N 3) hab
        (by simpa [hq3] using hA02) (by simpa [hq3] using hA12)
        (by simpa [hq3] using hA03) (by simpa [hq3] using hA13) with ⟨hN2, hN3⟩
    exact ⟨⟨hq2, hq3⟩, hN2, hN3, hN6, hN7⟩

theorem commonFeedback_seedCubic_classification
    (pa pb ja jb : F₂) (q : FeedbackCoord) (N : LinearForm)
    (hjet : ja ≠ 0 ∨ jb ≠ 0) (hq0 : q ≠ 0)
    (hcubic :
      vectorWedgeTwo N (targetTwo (feedbackCoeffRep q)) =
        vectorWedgeTwo (normalizedFirstJetVector pa pb ja jb)
          (rationalPlaceTwo 0)) :
    InFirstJetPlane q ∧ InK0Linear N :=
  commonFeedback_seedCubic_certificate pa pb ja jb q N hjet hq0
    (by simpa [feedbackCoeffRep_eq_pure] using hcubic)

theorem feedbackProduct_cubic_zero_left
    (a b : F₂) (ell m : LinearForm) (c : FeedbackCoord) :
    anfThreeProjection
        ((affineANF a ell + targetANF (feedbackCoeffRep 0)) *
          (affineANF b m + targetANF (feedbackCoeffRep c))) =
      vectorWedgeTwo ell (targetTwo (feedbackCoeffRep c)) := by
  rw [targetANF_feedbackCoeffRep_zero, add_zero, mul_add, map_add,
    anfThreeProjection_affine_mul_affine,
    anfThreeProjection_affine_mul_target, zero_add]

theorem feedbackProduct_cubic_zero_right
    (a b : F₂) (ell m : LinearForm) (q : FeedbackCoord) :
    anfThreeProjection
        ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep 0))) =
      vectorWedgeTwo m (targetTwo (feedbackCoeffRep q)) := by
  rw [mul_comm]
  exact feedbackProduct_cubic_zero_left b a m ell q

theorem feedbackProduct_cubic_equal
    (a b : F₂) (ell m : LinearForm) (q : FeedbackCoord) :
    anfThreeProjection
        ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep q))) =
      vectorWedgeTwo (ell + m) (targetTwo (feedbackCoeffRep q)) := by
  let T := targetANF (feedbackCoeffRep q)
  have hTthree : anfThreeProjection T = 0 :=
    anfThreeProjection_eq_zero_of_mem_targetAmbient
      (Submodule.mem_sup_right (targetANF_mem_mulTarget _))
  change anfThreeProjection
    ((affineANF a ell + T) * (affineANF b m + T)) = _
  simp only [add_mul, mul_add, map_add]
  have hAT : anfThreeProjection (affineANF a ell * T) =
      vectorWedgeTwo ell (targetTwo (feedbackCoeffRep q)) :=
    anfThreeProjection_affine_mul_target a ell _
  rw [anfThreeProjection_affine_mul_affine, hAT,
    anfThreeProjection_target_mul_affine, anf_mul_self, hTthree,
    vectorWedgeTwo_add_left]
  abel

/-- Assemble the seed quadratic identity and a one-direction product shadow,
then invoke jet separation. -/
theorem target_mem_feedback_of_seed_product_shadow
    {g correction shift product F : ANF 8}
    {M companion N R : LinearForm} {pa pb ja jb : F₂}
    (hcorrection : correction ∈ rationalLowSpace)
    (hseed : g + correction = linearANF M *
      (linearANF companion + rationalANF (rationalSingleton 0)))
    (hM : M = normalizedFirstJetVector pa pb ja jb)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (hshift : shift ∈ zeroFeedbackLowSpace)
    (hFmem : F ∈ targetAmbient 8 (mulTarget 4))
    (hF : F = shift + g + product)
    (hN : InK0Linear N)
    (hproductShadow : SupportedK0Two
      (anfTwoProjection product + vectorWedge N R)) :
    F ∈ zeroFeedbackLowSpace := by
  rcases exists_lowProduct_rep_of_mem_rationalLow hcorrection with
    ⟨corrConst, corrLinear, alpha, hcorrRep⟩
  rcases exists_feedbackLow_rep hshift with
    ⟨shiftConst, shiftLinear, qShift, hshiftRep⟩
  rcases exists_targetAmbient_rep hFmem with ⟨u, d, hu, hFrepU⟩
  rcases exists_affineANF_of_mem hu with ⟨fConst, fLinear, huRep⟩
  have hFrep : F = affineANF fConst fLinear + targetANF d := by
    rw [hFrepU, huRep]
  have hseedTwo := congrArg anfTwoProjection hseed
  rw [hcorrRep, map_add, map_add,
    anfTwoProjection_kills_affine (affineANF_mem corrConst corrLinear),
    anfTwoProjection_rationalANF, zero_add,
    mul_add, map_add, anfTwoProjection_linear_mul_linear,
    anfTwoProjection_linear_mul_rational,
    rationalTwo_singleton_zero] at hseedTwo
  have hseedTwo' : anfTwoProjection g =
      rationalTwo alpha + vectorWedge M companion +
        booleanContraction M zeroPlaceTwo := by
    have hself : rationalTwo alpha + rationalTwo alpha = 0 := by
      funext i j
      exact CharTwo.add_self_eq_zero _
    calc
      anfTwoProjection g =
          (anfTwoProjection g + rationalTwo alpha) +
            rationalTwo alpha := by
              rw [add_assoc, hself, add_zero]
      _ = (vectorWedge M companion +
            booleanContraction M zeroPlaceTwo) +
          rationalTwo alpha := by rw [hseedTwo]
      _ = _ := by ac_rfl
  have hFtwo := congrArg anfTwoProjection hF
  rw [hFrep, hshiftRep] at hFtwo
  simp only [map_add] at hFtwo
  rw [anfTwoProjection_kills_affine (affineANF_mem fConst fLinear),
    anfTwoProjection_targetANF,
    anfTwoProjection_kills_affine
      (affineANF_mem shiftConst shiftLinear),
    anfTwoProjection_targetANF, zero_add, zero_add] at hFtwo
  let s : TargetCoeff :=
    feedbackCoeffRep qShift + rationalCoeffRep alpha
  have hs : s ∈ feedbackCoeffSpace := by
    apply Submodule.add_mem
    · exact (mem_feedbackCoeffSpace_iff_exists_rep _).mpr
        ⟨qShift, rfl⟩
    · exact rationalCoeffRep_mem_feedbackCoeffSpace alpha
  let kprod : TwoForm :=
    anfTwoProjection product + vectorWedge N R
  let k : TwoForm :=
    kprod + booleanContraction M zeroPlaceTwo
  have hk : SupportedK0Two k := by
    apply hproductShadow.add
    simpa [rationalPlaceTwo_zero_eq] using
      (SupportedK0Two.booleanContraction_zeroPlace M)
  have hproductTwo : anfTwoProjection product =
      kprod + vectorWedge N R := by
    dsimp [kprod]
    have hself : vectorWedge N R + vectorWedge N R = 0 := by
      funext i j
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [add_assoc, hself, add_zero]
  have htargetS : targetTwo s =
      targetTwo (feedbackCoeffRep qShift) + rationalTwo alpha := by
    dsimp [s]
    calc
      targetTwo (feedbackCoeffRep qShift + rationalCoeffRep alpha) =
          targetTwo (feedbackCoeffRep qShift) +
            targetTwo (rationalCoeffRep alpha) :=
        targetTwoLinear.map_add _ _
      _ = _ := by rw [targetTwo_rationalCoeffRep]
  have hshadow : targetTwo d = targetTwo s + k +
      vectorWedge M companion + vectorWedge N R := by
    rw [htargetS, hFtwo, hseedTwo', hproductTwo]
    dsimp [k]
    ac_rfl
  have hMK0 : InK0Linear M := by
    rw [hM]
    exact normalizedFirstJetVector_inK0 pa pb ja jb
  have hUne : Submodule.span F₂ (Set.range ![M, N]) ≠
      anchorPlane := by
    rw [hM]
    exact normalizedFirstJet_span_two_ne_anchorPlane pa pb ja jb N hjet
  have hd : d ∈ feedbackCoeffSpace :=
    jet_separation_of_twoWedge_shadow M N companion R k s d
      hMK0 hN hk hs hUne hshadow
  rw [hFrep]
  exact (targetRep_mem_zeroFeedbackLow_iff fConst fLinear d).mpr hd

/-- Algebraic exclusion of the low--low second feedback whose cubic part
cancels the normalized seed. -/
theorem no_normalizedLowLow_feedbackTarget
    {g correction shift p r F : ANF 8}
    {M companion : LinearForm} {pa pb ja jb : F₂}
    (hg : DegreeLE 3 g)
    (hcorrection : correction ∈ rationalLowSpace)
    (hseed : g + correction = linearANF M *
      (linearANF companion + rationalANF (rationalSingleton 0)))
    (hM : M = normalizedFirstJetVector pa pb ja jb)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (hseedCubic : vectorWedgeTwo M (rationalPlaceTwo 0) ≠ 0)
    (hshift : shift ∈ zeroFeedbackLowSpace)
    (hp : p ∈ zeroFeedbackLowSpace)
    (hr : r ∈ zeroFeedbackLowSpace)
    (hFmem : F ∈ targetAmbient 8 (mulTarget 4))
    (hFoutside : F ∉ zeroFeedbackLowSpace)
    (hF : F = shift + g + p * r) : False := by
  have hcorrectionCubic := anfThreeProjection_eq_zero_of_degreeLE_two
    (degreeLE_two_of_mem_rationalLow hcorrection)
  have hseedProjection := congrArg anfThreeProjection hseed
  rw [map_add, hcorrectionCubic, add_zero, mul_add, map_add,
    anfThreeProjection_linear_mul_linear,
    anfThreeProjection_linear_mul_rational, zero_add,
    rationalTwo_singleton_zero] at hseedProjection
  rw [← rationalPlaceTwo_zero_eq] at hseedProjection
  have hshiftDegree := degreeLE_two_of_mem_zeroFeedbackLowSpace hshift
  have hshiftCubic := anfThreeProjection_eq_zero_of_degreeLE_two
    hshiftDegree
  have hFzero := anfThreeProjection_eq_zero_of_mem_targetAmbient hFmem
  have hFprojection := congrArg anfThreeProjection hF
  rw [hFzero, map_add, map_add, hshiftCubic, zero_add,
    hseedProjection] at hFprojection
  have hprodThree : anfThreeProjection (p * r) =
      vectorWedgeTwo M (rationalPlaceTwo 0) := by
    funext i j k
    have hij := congrFun (congrFun (congrFun hFprojection i) j) k
    simp only [Pi.zero_apply, Pi.add_apply] at hij ⊢
    calc
      anfThreeProjection (p * r) i j k =
          anfThreeProjection (p * r) i j k + 0 := by rw [add_zero]
      _ = anfThreeProjection (p * r) i j k +
          (vectorWedgeTwo M (rationalPlaceTwo 0) i j k +
            anfThreeProjection (p * r) i j k) := by rw [← hij]
      _ = vectorWedgeTwo M (rationalPlaceTwo 0) i j k := by
        ring_nf
        simp [N3Certificate.two_eq_zero_f2]
  have hFquartic : feedbackQuarticProbeANF F = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((targetAmbient_le_quadraticANFSpace hFmem).mono (by omega))
  have hshiftQuartic : feedbackQuarticProbeANF shift = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      (hshiftDegree.mono (by omega))
  have hgQuartic : feedbackQuarticProbeANF g = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three hg
  have hquarticEq := congrArg feedbackQuarticProbeANF hF
  rw [hFquartic, map_add, map_add, hshiftQuartic, hgQuartic,
    zero_add, zero_add] at hquarticEq
  have hprodQuartic : feedbackQuarticProbeANF (p * r) = 0 := by
    simpa using hquarticEq.symm
  rcases exists_feedbackLow_rep hp with ⟨a, ell, q, hpRep⟩
  rcases exists_feedbackLow_rep hr with ⟨b, m, c, hrRep⟩
  have hthreeRep :
      anfThreeProjection
          ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
            (affineANF b m + targetANF (feedbackCoeffRep c))) =
        vectorWedgeTwo M (rationalPlaceTwo 0) := by
    simpa [hpRep, hrRep] using hprodThree
  have hquarticRep : feedbackQuarticProbeANF
      ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
        (affineANF b m + targetANF (feedbackCoeffRep c))) = 0 := by
    simpa [hpRep, hrRep] using hprodQuartic
  have hstructure := feedbackProduct_zeroWedgeStructure
    a b ell m q c hquarticRep
  have hcases : q = 0 ∨ c = 0 ∨ q = c ∨
      (InFirstJetPlane q ∧ InFirstJetPlane c ∧
        q ≠ 0 ∧ c ≠ 0 ∧ q ≠ c) := by
    rcases hstructure with hq0 | hc0 | hqc | hplane
    · exact Or.inl hq0
    · exact Or.inr (Or.inl hc0)
    · exact Or.inr (Or.inr (Or.inl hqc))
    · by_cases hq0 : q = 0
      · exact Or.inl hq0
      by_cases hc0 : c = 0
      · exact Or.inr (Or.inl hc0)
      by_cases hqc : q = c
      · exact Or.inr (Or.inr (Or.inl hqc))
      · exact Or.inr (Or.inr (Or.inr
          ⟨hplane.1, hplane.2, hq0, hc0, hqc⟩))
  have hMK0 : InK0Linear M := by
    rw [hM]
    exact normalizedFirstJetVector_inK0 pa pb ja jb
  rcases hcases with hq0 | hc0 | hqc | hindependent
  · subst q
    have hcubic : vectorWedgeTwo ell
        (targetTwo (feedbackCoeffRep c)) =
          vectorWedgeTwo M (rationalPlaceTwo 0) := by
      rw [← hthreeRep]
      exact (feedbackProduct_cubic_zero_left a b ell m c).symm
    have hc0 : c ≠ 0 := by
      intro hc
      subst c
      apply hseedCubic
      rw [← hcubic, feedbackCoeffRep_zero]
      rw [show targetTwo (0 : TargetCoeff) = 0 from targetTwoLinear.map_zero]
      exact vectorWedgeTwo_zero_right ell
    have hclass : InFirstJetPlane c ∧ InK0Linear ell := by
      apply commonFeedback_seedCubic_classification
        pa pb ja jb c ell hjet hc0
      rw [← hM]
      exact hcubic
    have hzeroPlane : InFirstJetPlane (0 : FeedbackCoord) := ⟨rfl, rfl⟩
    have hshadow := feedbackProduct_twoShadow_supported
      a b ell m 0 c hzeroPlane hclass.1
    apply hFoutside
    apply target_mem_feedback_of_seed_product_shadow
      (g := g) (correction := correction) (shift := shift)
      (product := p * r) (F := F) (M := M) (companion := companion)
      (N := ell) (R := m) (pa := pa) (pb := pb) (ja := ja) (jb := jb)
      hcorrection hseed hM hjet hshift hFmem hF hclass.2
    simpa [hpRep, hrRep] using hshadow
  · subst c
    have hcubic : vectorWedgeTwo m
        (targetTwo (feedbackCoeffRep q)) =
          vectorWedgeTwo M (rationalPlaceTwo 0) := by
      rw [← hthreeRep]
      exact (feedbackProduct_cubic_zero_right a b ell m q).symm
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      apply hseedCubic
      rw [← hcubic, feedbackCoeffRep_zero]
      rw [show targetTwo (0 : TargetCoeff) = 0 from targetTwoLinear.map_zero]
      exact vectorWedgeTwo_zero_right m
    have hclass : InFirstJetPlane q ∧ InK0Linear m := by
      apply commonFeedback_seedCubic_classification
        pa pb ja jb q m hjet hq0
      rw [← hM]
      exact hcubic
    have hzeroPlane : InFirstJetPlane (0 : FeedbackCoord) := ⟨rfl, rfl⟩
    have hshadow := feedbackProduct_twoShadow_supported
      a b ell m q 0 hclass.1 hzeroPlane
    apply hFoutside
    apply target_mem_feedback_of_seed_product_shadow
      (g := g) (correction := correction) (shift := shift)
      (product := p * r) (F := F) (M := M) (companion := companion)
      (N := m) (R := ell) (pa := pa) (pb := pb) (ja := ja) (jb := jb)
      hcorrection hseed hM hjet hshift hFmem hF hclass.2
    simpa [hpRep, hrRep, vectorWedge_comm] using hshadow
  · subst c
    have hcubic : vectorWedgeTwo (ell + m)
        (targetTwo (feedbackCoeffRep q)) =
          vectorWedgeTwo M (rationalPlaceTwo 0) := by
      rw [← hthreeRep]
      exact (feedbackProduct_cubic_equal a b ell m q).symm
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      apply hseedCubic
      rw [← hcubic, feedbackCoeffRep_zero]
      rw [show targetTwo (0 : TargetCoeff) = 0 from targetTwoLinear.map_zero]
      exact vectorWedgeTwo_zero_right (ell + m)
    have hclass : InFirstJetPlane q ∧ InK0Linear (ell + m) := by
      apply commonFeedback_seedCubic_classification
        pa pb ja jb q (ell + m) hjet hq0
      rw [← hM]
      exact hcubic
    have hshadow := feedbackProduct_twoShadow_supported
      a b ell m q q hclass.1 hclass.1
    apply hFoutside
    apply target_mem_feedback_of_seed_product_shadow
      (g := g) (correction := correction) (shift := shift)
      (product := p * r) (F := F) (M := M) (companion := companion)
      (N := ell + m) (R := m) (pa := pa) (pb := pb) (ja := ja) (jb := jb)
      hcorrection hseed hM hjet hshift hFmem hF hclass.2
    rw [hpRep, hrRep]
    simpa [vectorWedge_add_left_qp, vectorWedge_self] using hshadow
  · rcases hindependent with
      ⟨hqPlane, hcPlane, hq0, hc0, hqc⟩
    rcases independentFirstPlane_linears_inK0_of_seedCubic
      a b ell m M q c hqPlane hcPlane hq0 hc0 hqc hMK0 hthreeRep with
      ⟨hell, hm⟩
    have hshadow := feedbackProduct_twoShadow_supported
      a b ell m q c hqPlane hcPlane
    apply hFoutside
    apply target_mem_feedback_of_seed_product_shadow
      (g := g) (correction := correction) (shift := shift)
      (product := p * r) (F := F) (M := M) (companion := companion)
      (N := ell) (R := m) (pa := pa) (pb := pb) (ja := ja) (jb := jb)
      hcorrection hseed hM hjet hshift hFmem hF hell
    simpa [hpRep, hrRep] using hshadow

end

end N4
end UnrestrictedBooleanMul
