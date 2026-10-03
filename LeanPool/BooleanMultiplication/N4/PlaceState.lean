/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FirstJetState
public import LeanPool.BooleanMultiplication.N4.Feedback

/-!
# Place normalization on the complete target state

The first-jet argument chooses one of three rational places.  This file
extends the existing change of variables from rational generators and
tangents to every Hankel target.  The change is an involution on the Boolean
ANF algebra, so target-ambient and rational-low membership can be transported
in both directions.  The only coordinate certificate is the displayed
`7 × 7` change of Hankel coefficients.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The induced changes on the seven Hankel coefficients: identity,
translation, and reversal. -/
def normalizeTargetCoeff : Fin 3 → TargetCoeff → TargetCoeff :=
  ![fun c => c,
    fun c => ![c 0, c 0 + c 1, c 0 + c 2,
      c 0 + c 1 + c 2 + c 3, c 0 + c 4,
      c 0 + c 1 + c 4 + c 5, c 0 + c 2 + c 4 + c 6],
    fun c => ![c 6, c 5, c 4, c 3, c 2, c 1, c 0]]

theorem anfPlaceNormalize_targetANF (theta : Fin 3) (c : TargetCoeff) :
    anfPlaceNormalize theta (targetANF c) =
      targetANF (normalizeTargetCoeff theta c) := by
  have htwo : (2 : ANF 8) = 0 := by simp
  have hfour : (4 : ANF 8) = 0 := by
    calc
      (4 : ANF 8) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  have hthree : (3 : ANF 8) = 1 := by
    calc
      (3 : ANF 8) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; simp
  rw [targetANF_eq_bilinear_sum, map_sum]
  simp_rw [map_sum, map_smul, map_mul,
    anfPlaceNormalize_aVar, anfPlaceNormalize_bVar]
  rw [targetANF_eq_bilinear_sum]
  fin_cases theta <;>
    simp [normalizeTargetCoeff, hankelIndex, Fin.sum_univ_succ, inputPlaceChange, linearANF,
      aVar, bVar, X, aCoord, bCoord, monomial_mul]
  · ring_nf
    simp only [Fin.isValue, monomial_mul, Finset.singleton_union, smul_add]
    ring_nf
    simp only [Fin.isValue, htwo, mul_zero, add_zero, hthree, mul_one, hfour]
    module
  · module

theorem normalizePlaceLinear_coordinate
    (theta : Fin 3) (i : Fin 8) :
    normalizePlaceLinear theta (coordinateLinear i) =
      inputPlaceChange theta i := by
  funext j
  fin_cases theta <;> fin_cases i <;> fin_cases j <;>
    decide

theorem prod_X_eq_monomial (s : Finset (Fin 8)) :
    (∏ i ∈ s, X i) = monomial s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, monomial, MonoidAlgebra.one_def]
      congr 1
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, X, monomial_mul]
      congr 1

/-- Each of the three place changes is an involution on all Boolean ANFs. -/
theorem anfPlaceNormalize_involutive
    (theta : Fin 3) (p : ANF 8) :
    anfPlaceNormalize theta (anfPlaceNormalize theta p) = p := by
  refine MonoidAlgebra.induction_on
    (motive := fun x => anfPlaceNormalize theta (anfPlaceNormalize theta x) = x)
    p ?_ ?_ ?_
  · intro s
    have hs : s = (⟨s.vars⟩ : Monomial 8) := Monomial.ext rfl
    rw [MonoidAlgebra.of_apply, hs]
    change anfPlaceNormalize theta
      (anfPlaceNormalize theta (monomial s.vars)) = monomial s.vars
    simp only [anfPlaceNormalize_monomial, map_prod]
    simp_rw [anfPlaceNormalize_linearANF,
      ← normalizePlaceLinear_coordinate theta,
      normalizePlaceLinear_involutive, linearANF_coordinate]
    exact prod_X_eq_monomial s.vars
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro a p hp
    simp only [map_smul, hp]

theorem anfPlaceNormalize_injective (theta : Fin 3) :
    Function.Injective (anfPlaceNormalize theta) := by
  intro p q h
  have h' := congrArg (anfPlaceNormalize theta) h
  simpa [anfPlaceNormalize_involutive] using h'

theorem anfPlaceNormalize_mem_targetAmbient
    (theta : Fin 3) {p : ANF 8}
    (hp : p ∈ targetAmbient 8 (mulTarget 4)) :
    anfPlaceNormalize theta p ∈ targetAmbient 8 (mulTarget 4) := by
  rcases exists_targetAmbient_rep hp with ⟨u, c, hu, rfl⟩
  rw [map_add, anfPlaceNormalize_targetANF]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (by
      rcases exists_affineANF_of_mem hu with ⟨a, ell, rfl⟩
      rw [anfPlaceNormalize_affineANF]
      exact affineANF_mem _ _))
    (Submodule.mem_sup_right (targetANF_mem_mulTarget _))

theorem anfPlaceNormalize_mem_targetAmbient_iff
    (theta : Fin 3) (p : ANF 8) :
    anfPlaceNormalize theta p ∈ targetAmbient 8 (mulTarget 4) ↔
      p ∈ targetAmbient 8 (mulTarget 4) := by
  constructor
  · intro hp
    have h := anfPlaceNormalize_mem_targetAmbient theta hp
    rwa [anfPlaceNormalize_involutive] at h
  · exact anfPlaceNormalize_mem_targetAmbient theta

theorem anfPlaceNormalize_mem_rationalLow_iff
    (theta : Fin 3) (p : ANF 8) :
    anfPlaceNormalize theta p ∈ rationalLowSpace ↔
      p ∈ rationalLowSpace := by
  constructor
  · intro hp
    have h := anfPlaceNormalize_mem_rationalLow theta hp
    rwa [anfPlaceNormalize_involutive] at h
  · exact anfPlaceNormalize_mem_rationalLow theta

/-- The correlated first-jet state after moving its selected place to zero.
The seed representative uses the very same linear form whose nonzero
first-jet component was obtained in `FirstJetSupport`. -/
@[expose]
def ZeroNormalizedFirstJetState (C : Circuit 8 8) : Prop :=
  ∃ (theta : Fin 3) (eps : F₂) (anchorLinear companionLinear : LinearForm)
    (correction : ANF 8) (pa pb ja jb : F₂),
    correction ∈ rationalLowSpace ∧
    anfPlaceNormalize theta (C.gate 3) + correction =
      linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) ∧
    vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) ≠ 0 ∧
    anchorLinear = normalizedFirstJetVector pa pb ja jb ∧
    (ja ≠ 0 ∨ jb ≠ 0) ∧
    circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)}

theorem NormalizedEight.zeroNormalizedFirstJetState
    {C : Circuit 8 8} (h : NormalizedEight C) :
    ZeroNormalizedFirstJetState C := by
  rcases h.firstJetState with
    ⟨theta, eps, seedLinear, seedCompanion, seedRho,
      hgCubic, hgTwo, hgCubicNonzero, hnormal, hflag⟩
  rcases hnormal with ⟨pa, pb, ja, jb, hseedLinear, hjetNonzero⟩
  let model : ANF 8 := linearANF seedLinear *
    (linearANF seedCompanion + rationalANF (rationalSingleton theta))
  let correctionOriginal : ANF 8 := C.gate 3 + model
  have hseedLinearDegree : DegreeLE 1 (linearANF seedLinear) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 seedLinear
  have hseedCompanionDegree : DegreeLE 1 (linearANF seedCompanion) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 seedCompanion
  have hmodelDegree : DegreeLE 3 model := by
    exact hseedLinearDegree.mul
      ((hseedCompanionDegree.mono (by omega)).add
        (degreeLE_two_rationalANF (rationalSingleton theta)))
  have hmodelCubic : anfThreeProjection model =
      vectorWedgeTwo seedLinear
        (rationalTwo (rationalSingleton theta)) := by
    dsimp [model]
    rw [mul_add, map_add, anfThreeProjection_linear_mul_linear,
      anfThreeProjection_linear_mul_rational, zero_add]
  have hcorrectionCubic : anfThreeProjection correctionOriginal = 0 := by
    dsimp [correctionOriginal]
    rw [map_add, hgCubic, hmodelCubic]
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcorrectionDegree : DegreeLE 2 correctionOriginal :=
    degreeLE_two_of_degreeLE_three_of_cubic_zero
      (h.seed_degreeLE_three.add hmodelDegree) hcorrectionCubic
  have hmodelTwo : anfTwoProjection model =
      vectorWedge seedCompanion seedLinear +
        booleanContraction seedLinear
          (rationalTwo (rationalSingleton theta)) := by
    dsimp [model]
    rw [mul_add, map_add, anfTwoProjection_linear_mul_linear,
      anfTwoProjection_linear_mul_rational,
      vectorWedge_comm seedLinear seedCompanion]
  have hcorrectionTwo : anfTwoProjection correctionOriginal =
      seedRho • rationalTwo (rationalSingleton theta) := by
    dsimp [correctionOriginal]
    rw [map_add, hgTwo, hmodelTwo]
    let q := vectorWedge seedCompanion seedLinear +
      booleanContraction seedLinear
        (rationalTwo (rationalSingleton theta))
    have hqq : q + q = 0 := by
      funext i j
      change q i j + q i j = (0 : F₂)
      exact CharTwo.add_self_eq_zero _
    calc
      seedRho • rationalTwo (rationalSingleton theta) +
            vectorWedge seedCompanion seedLinear +
            booleanContraction seedLinear
              (rationalTwo (rationalSingleton theta)) + q =
          seedRho • rationalTwo (rationalSingleton theta) + (q + q) := by
            dsimp [q]
            ac_rfl
      _ = _ := by rw [hqq, add_zero]
  have hcorrectionTwoMem :
      anfTwoProjection correctionOriginal ∈ rationalPlaceTwoSpace := by
    rw [hcorrectionTwo]
    exact Submodule.smul_mem _ _
      (rationalTwo_mem (rationalSingleton theta))
  have hcorrectionOriginalLow : correctionOriginal ∈ rationalLowSpace :=
    mem_rationalLow_of_degreeLE_two_of_twoProjection_mem
      hcorrectionDegree hcorrectionTwoMem
  let anchorLinear := normalizePlaceLinear theta seedLinear
  let companionLinear := normalizePlaceLinear theta seedCompanion
  let correction := anfPlaceNormalize theta correctionOriginal
  have hcorrectionLow : correction ∈ rationalLowSpace :=
    anfPlaceNormalize_mem_rationalLow theta hcorrectionOriginalLow
  have hmodelNormalize : anfPlaceNormalize theta model =
      linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) := by
    dsimp [model, anchorLinear, companionLinear]
    rw [map_mul, map_add, anfPlaceNormalize_linearANF,
      anfPlaceNormalize_linearANF, anfPlaceNormalize_rationalANF,
      normalizeRationalCoeff_singleton_self]
  have hseedEq : anfPlaceNormalize theta (C.gate 3) + correction =
      linearANF anchorLinear *
        (linearANF companionLinear +
          rationalANF (rationalSingleton 0)) := by
    dsimp [correction, correctionOriginal]
    rw [map_add]
    calc
      anfPlaceNormalize theta (C.gate 3) +
          (anfPlaceNormalize theta (C.gate 3) +
            anfPlaceNormalize theta model) =
          anfPlaceNormalize theta model := by
            rw [← add_assoc, anf_add_self, zero_add]
      _ = _ := hmodelNormalize
  have hnormalizedNonzero :
      vectorWedgeTwo anchorLinear (rationalPlaceTwo 0) ≠ 0 := by
    have hn := normalized_anchored_cubic_ne_zero theta seedLinear
      (rationalSingleton theta) hgCubicNonzero
    dsimp [anchorLinear] at hn
    rw [normalizeRationalCoeff_singleton_self,
      rationalTwo_singleton_zero] at hn
    rw [rationalPlaceTwo_zero_eq]
    exact hn
  refine ⟨theta, eps, anchorLinear, companionLinear, correction,
    pa, pb, ja, jb, hcorrectionLow, hseedEq, hnormalizedNonzero, ?_,
    hjetNonzero, hflag⟩
  dsimp [anchorLinear]
  exact hseedLinear

/-- The degree-at-most-two state after the first feedback, in zero-place
coordinates.  The choice of tangent representative is immaterial modulo the
rational place `E₀`. -/
@[expose]
def zeroFeedbackLowSpace : Submodule F₂ (ANF 8) :=
  rationalLowSpace ⊔
    Submodule.span F₂ {targetANF (rationalTangentAt 0 0)}

theorem zero_tangent_mem_feedbackLow (eps : F₂) :
    targetANF (rationalTangentAt 0 eps) ∈ zeroFeedbackLowSpace := by
  apply Submodule.mem_sup.mpr
  refine ⟨eps • rZeroANF, ?_,
    targetANF (rationalTangentAt 0 0),
    Submodule.mem_span_singleton_self _, ?_⟩
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_right
        (Submodule.subset_span (Set.mem_insert _ _)))
  · change eps • targetANF (rationalPlaceCoeff 0) +
      targetANF (rationalTangentAt 0 0) =
        targetANF (rationalTangentAt 0 eps)
    change eps • targetANFLinear (rationalPlaceCoeff 0) +
      targetANFLinear (rationalTangentAt 0 0) =
        targetANFLinear (rationalTangentAt 0 eps)
    rw [← map_smul, ← map_add]
    congr 1
    funext i
    fin_cases i <;>
      simp [rationalPlaceCoeff, rZeroCoeff, rationalTangentAt]

/-- Every wire in the fifth flag becomes a feedback-low wire plus at most
one copy of the normalized seed. -/
theorem exists_normalized_feedback_add_seed_of_mem_five
    {C : Circuit 8 8} (h : NormalizedEight C)
    {theta : Fin 3} {eps : F₂}
    (hflag : circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)})
    {w : ANF 8} (hw : w ∈ circuitFlag C 5) :
    ∃ (low : ANF 8) (e : F₂),
      low ∈ zeroFeedbackLowSpace ∧
      anfPlaceNormalize theta w = low +
        e • anfPlaceNormalize theta (C.gate 3) := by
  rw [hflag] at hw
  rcases Submodule.mem_sup.mp hw with ⟨old, hold, tangent, htangent, rfl⟩
  rcases Submodule.mem_span_singleton.mp htangent with ⟨b, rfl⟩
  rw [h.wireSpace_four_eq] at hold
  rcases Submodule.mem_sup.mp hold with ⟨rational, hrational, seed, hseed, rfl⟩
  rcases Submodule.mem_span_singleton.mp hseed with ⟨e, rfl⟩
  let low := anfPlaceNormalize theta rational +
    b • targetANF (rationalTangentAt 0 eps)
  have hlow : low ∈ zeroFeedbackLowSpace := by
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left
        (anfPlaceNormalize_mem_rationalLow theta hrational)
    · exact Submodule.smul_mem _ _ (zero_tangent_mem_feedbackLow eps)
  refine ⟨low, e, hlow, ?_⟩
  dsimp [low]
  rw [map_add, map_add, map_smul, map_smul,
    anfPlaceNormalize_tangent_self]
  ac_rfl

theorem feedbackCoeffRep_injective :
    Function.Injective feedbackCoeffRep := by
  intro q c h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  have h6 := congrFun h 6
  simp only [feedbackCoeffRep, Fin.isValue, rOneCoeff, Matrix.smul_cons, smul_eq_mul, mul_one,
    Matrix.smul_empty, Pi.add_apply, Pi.smul_apply, targetBasis_apply, ↓reduceIte,
    one_ne_zero, mul_zero, add_zero, Fin.reduceEq, Matrix.cons_val_zero, zero_ne_one,
    zero_add, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h3 h6
  funext i
  fin_cases i
  · exact add_right_cancel (h0.trans (congrArg (fun x => c 0 + x) h3.symm))
  · exact add_right_cancel (h1.trans (congrArg (fun x => c 1 + x) h3.symm))
  · exact add_right_cancel (h6.trans (congrArg (fun x => c 2 + x) h3.symm))
  · exact h3

/-- Concrete affine-plus-`S` representation of the feedback-low state. -/
theorem exists_feedbackLow_rep {p : ANF 8}
    (hp : p ∈ zeroFeedbackLowSpace) :
    ∃ (a : F₂) (ell : LinearForm) (q : FeedbackCoord),
      p = affineANF a ell + targetANF (feedbackCoeffRep q) := by
  rcases Submodule.mem_sup.mp hp with
    ⟨rational, hrational, tangent, htangent, hpEq⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hrational with
    ⟨a, ell, alpha, hrationalEq⟩
  rcases Submodule.mem_span_singleton.mp htangent with ⟨b, hb⟩
  let q : FeedbackCoord := ![
    alpha 0, b, alpha 2, alpha 1]
  have hcoeff : rationalCoeffRep alpha +
      b • rationalTangentAt 0 0 = feedbackCoeffRep q := by
    funext i
    fin_cases i <;>
      simp [q, rationalCoeffRep, rationalTangentAt, feedbackCoeffRep, rZeroCoeff, rOneCoeff,
        rInfinityCoeff, targetBasis, Pi.basisFun] <;>
      ring
  refine ⟨a, ell, q, ?_⟩
  rw [← hpEq, hrationalEq, ← hb]
  change affineANF a ell + targetANFLinear (rationalCoeffRep alpha) +
      b • targetANFLinear (rationalTangentAt 0 0) = _
  rw [← map_smul, add_assoc, ← map_add, hcoeff]
  rfl

end

end N4
end UnrestrictedBooleanMul
