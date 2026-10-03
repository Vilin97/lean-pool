/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicFeedback

/-!
# Cubic first-feedback slice exclusion

This file formalizes the `Q`/`L` comparison in the manuscript's exclusion
of a seed-using first feedback.  The seed has already been normalized to
`M (z + E₀)` modulo `Aff + R`.  On an active `(x,y)` slice both seed
factors are affine in the six complementary variables, so the quadratic
equation is independent of the corner.  The three active corners then force
two independent target differences into a space of dimension at most one,
or into one of the two disjoint support planes.

The proof is exterior-linear and does not enumerate circuits or Boolean
functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Restrict a linear factor to fixed values of the two anchor inputs. -/
def sliceLinearFactorModel
    (ell : LinearForm) (x y : F₂) : ANF 8 :=
  affineANF (sliceAnchorValue ell x y) (sliceComplementLinear ell)

/-- The sliced cubic seed, including its affine and rational-target correction. -/
def sliceCubicSeedFullModel
    (anchorLinear companionLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) : ANF 8 :=
  sliceLinearFactorModel anchorLinear x y *
      sliceZeroFactorModel 0 companionLinear x y +
    sliceCorrectionModel correctionConst correctionLinear
      correctionCoeff x y

theorem eval_sliceLinearFactorModel
    (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceLinearFactorModel ell x y) (sliceAssignment x y z) =
      eval (linearANF ell) (sliceAssignment x y z) := by
  simpa [sliceLinearFactorModel, affineANF] using
    (eval_affineANF_slice 0 ell x y z).symm

theorem eval_sliceCubicSeedFullModel_eq_normalized
    (anchorLinear companionLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) (z : Fin 6 → F₂) :
    eval
        (sliceCubicSeedFullModel anchorLinear companionLinear
          correctionConst correctionLinear correctionCoeff x y)
        (sliceAssignment x y z) =
      eval
        (linearANF anchorLinear *
            (linearANF companionLinear +
              rationalANF (rationalSingleton 0)) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff)
        (sliceAssignment x y z) := by
  simp only [sliceCubicSeedFullModel, eval_add', eval_mul']
  rw [eval_sliceLinearFactorModel]
  have hzero := eval_sliceZeroFactorModel
    0 companionLinear x y z
  have hcorrection := eval_sliceCorrectionModel
    correctionConst correctionLinear correctionCoeff x y z
  simpa [representedLowFactor, affineANF] using
    congrArg₂ (fun a b : F₂ => a + b)
      (congrArg₂ (fun a b : F₂ => a * b) rfl hzero)
      hcorrection

theorem anchorsIndependent_sliceLinearFactorModel
    (ell : LinearForm) (x y : F₂) :
    AnchorsIndependent (sliceLinearFactorModel ell x y) := by
  apply anchorsIndependent_affineANF
  · exact (sliceComplementLinear_anchor_zero ell).1
  · exact (sliceComplementLinear_anchor_zero ell).2

theorem anchorsIndependent_sliceCubicSeedFullModel
    (anchorLinear companionLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    AnchorsIndependent
      (sliceCubicSeedFullModel anchorLinear companionLinear
        correctionConst correctionLinear correctionCoeff x y) := by
  exact
    ((anchorsIndependent_sliceLinearFactorModel anchorLinear x y).mul
      (anchorsIndependent_sliceZeroFactorModel 0 companionLinear x y)).add
      (anchorsIndependent_sliceCorrectionModel correctionConst
        correctionLinear correctionCoeff x y)

@[simp] theorem anfTwoProjection_sliceCubicSeedFullModel
    (anchorLinear companionLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfTwoProjection
        (sliceCubicSeedFullModel anchorLinear companionLinear
          correctionConst correctionLinear correctionCoeff x y) =
      vectorWedge (sliceComplementLinear anchorLinear)
          (sliceComplementLinear companionLinear) +
        correctionCoeff 1 • sliceQuadraticA +
        correctionCoeff 2 • sliceInfinityQuadratic := by
  simp [sliceCubicSeedFullModel, sliceLinearFactorModel, sliceZeroFactorModel,
    anfTwoProjection_affine_mul_affine, anfTwoProjection_sliceCorrectionModel, add_assoc]

@[simp] theorem anfLinearProjection_sliceCubicSeedFullModel
    (anchorLinear companionLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfLinearProjection
        (sliceCubicSeedFullModel anchorLinear companionLinear
          correctionConst correctionLinear correctionCoeff x y) =
      sliceProductLinear
        (sliceAnchorValue anchorLinear x y)
        (sliceAnchorValue companionLinear x y + x * y)
        (sliceComplementLinear anchorLinear)
        (sliceComplementLinear companionLinear)
        (sliceComplementLinear correctionLinear)
        (correctionCoeff 1) x y := by
  simp [sliceCubicSeedFullModel, sliceLinearFactorModel, sliceZeroFactorModel,
    sliceProductLinear, anfLinearProjection_affine_mul_affine,
    anfLinearProjection_sliceCorrectionModel, add_assoc]

/-- The third linear form belongs to the span of the first two. -/
def InLinearPair (m n w : LinearForm) : Prop :=
  ∃ a b : F₂, w = a • m + b • n

theorem vectorWedge_linear_combinations
    (a b c d : F₂) (m n : LinearForm) :
    vectorWedge (a • m + b • n) (c • m + d • n) =
      (a * d + b * c) • vectorWedge m n := by
  funext i j
  simp [vectorWedge]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem vectorWedge_eq_zero_of_pair
    {m n u v : LinearForm}
    (hmn : vectorWedge m n = 0)
    (hu : InLinearPair m n u) (hv : InLinearPair m n v) :
    vectorWedge u v = 0 := by
  rcases hu with ⟨a, b, rfl⟩
  rcases hv with ⟨c, d, rfl⟩
  rw [vectorWedge_linear_combinations, hmn, smul_zero]

theorem vectorWedge_sliceU_sliceV_ne_zero :
    vectorWedge sliceU sliceV ≠ 0 := by
  intro h
  have hc := congrFun (congrFun h (aCoord 1)) (bCoord 1)
  simp [vectorWedge, sliceU, sliceV, aLinear, bLinear, aCoord, bCoord, Pi.basisFun] at hc

theorem sliceQuadraticB_ne_zero : sliceQuadraticB ≠ 0 := by
  intro h
  have hc := congrFun (congrFun h (aCoord 1)) (bCoord 1)
  simp [sliceQuadraticB, sliceQuadraticA, sliceInfinityQuadratic, vectorWedge, sliceABar,
    sliceBBar, placeA, placeB, aCoord, bCoord] at hc

private theorem sliceProduct_pair_eq_targetDifference
    {x y x' y' mu nu mu' nu' lambdaOne : F₂}
    {m n base targetBase : LinearForm}
    (hlinear : sliceProductLinear mu nu m n base lambdaOne x y =
      targetBase + y • sliceU + x • sliceV)
    (hlinear' : sliceProductLinear mu' nu' m n base lambdaOne x' y' =
      targetBase + y' • sliceU + x' • sliceV) :
    sliceProductLinear mu nu m n base lambdaOne x y +
        sliceProductLinear mu' nu' m n base lambdaOne x' y' =
      sliceTargetDifference x y x' y' := by
  rw [hlinear, hlinear']
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sliceTargetDifference]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem targetDifference_mem_pair_of_zero_feedback
    {x y x' y' mu nu mu' nu' : F₂}
    {m n base targetBase : LinearForm}
    (hlinear : sliceProductLinear mu nu m n base 0 x y =
      targetBase + y • sliceU + x • sliceV)
    (hlinear' : sliceProductLinear mu' nu' m n base 0 x' y' =
      targetBase + y' • sliceU + x' • sliceV) :
    InLinearPair m n (sliceTargetDifference x y x' y') := by
  refine ⟨nu + nu', mu + mu', ?_⟩
  rw [← sliceProduct_pair_eq_targetDifference hlinear hlinear']
  funext i
  simp only [sliceProductLinear, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    pointwiseLinearProduct]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Algebraic `Q`/`L` exclusion for the three active corners. -/
theorem no_cubic_seed_three_active_slices
    {delta rho sigma lambdaOne lambdaInfinity : F₂}
    {m n base targetBase : LinearForm}
    (hcorners : ExactlyThreeActiveCorners delta rho sigma)
    (hquad : vectorWedge m n +
        lambdaOne • sliceQuadraticA +
        lambdaInfinity • sliceInfinityQuadratic = 0)
    (mu nu : F₂ → F₂ → F₂)
    (hlinear : ∀ x y,
      feedbackCorner delta rho sigma x y = 1 →
      sliceProductLinear (mu x y) (nu x y) m n base
          lambdaOne x y =
        targetBase + y • sliceU + x • sliceV) : False := by
  rcases f2_eq_zero_or_one lambdaOne with hOne | hOne <;>
    rcases f2_eq_zero_or_one lambdaInfinity with hInfinity | hInfinity
  · subst lambdaOne
    subst lambdaInfinity
    have hmn : vectorWedge m n = 0 := by simpa using hquad
    rcases hcorners with ⟨x₀, y₀, _hzero, hactive⟩
    have hA : feedbackCorner delta rho sigma (x₀ + 1) y₀ = 1 :=
      hactive _ _ (Or.inl (f2_add_one_ne_self x₀))
    have hB : feedbackCorner delta rho sigma x₀ (y₀ + 1) = 1 :=
      hactive _ _ (Or.inr (f2_add_one_ne_self y₀))
    have hC : feedbackCorner delta rho sigma (x₀ + 1) (y₀ + 1) = 1 :=
      hactive _ _ (Or.inl (f2_add_one_ne_self x₀))
    have hUmem := targetDifference_mem_pair_of_zero_feedback
      (hlinear _ _ hA) (hlinear _ _ hC)
    have hVmem := targetDifference_mem_pair_of_zero_feedback
      (hlinear _ _ hB) (hlinear _ _ hC)
    have hUeq : sliceTargetDifference (x₀ + 1) y₀
        (x₀ + 1) (y₀ + 1) = sliceU := by
      funext i
      simp [sliceTargetDifference]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    have hVeq : sliceTargetDifference x₀ (y₀ + 1)
        (x₀ + 1) (y₀ + 1) = sliceV := by
      funext i
      simp [sliceTargetDifference]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    rw [hUeq] at hUmem
    rw [hVeq] at hVmem
    exact vectorWedge_sliceU_sliceV_ne_zero
      (vectorWedge_eq_zero_of_pair hmn hUmem hVmem)
  · subst lambdaOne
    subst lambdaInfinity
    have hmn : vectorWedge m n = sliceInfinityQuadratic := by
      funext i j
      have hc := congrFun (congrFun hquad i) j
      simp only [zero_smul, one_smul, Pi.add_apply, Pi.zero_apply] at hc
      simpa using (add_eq_zero_iff_eq_neg.mp hc).trans (neg_eq_self_f2 _)
    have hmAnn : vectorWedgeTwo m sliceInfinityQuadratic = 0 := by
      have hw := congrArg (fun q : TwoForm => vectorWedgeTwo m q) hmn
      rw [vectorWedgeTwo_repeated_left] at hw
      exact hw.symm
    have hmInf := sliceInfinityQuadratic_annihilator hmAnn
    have hmNe : m ≠ 0 := by
      intro hm
      rw [hm, vectorWedge_zero_left_qp] at hmn
      exact sliceInfinityQuadratic_ne_zero hmn.symm
    have hnInf := second_factor_mem_of_infinity_wedge hmInf hmNe
      (a := 1) (by simpa using hmn)
    rcases exists_distinct_active_corner_pair hcorners with
      ⟨x, y, x', y', hdistinct, hactive, hactive'⟩
    have hp := sliceProduct_pair_eq_targetDifference
      (hlinear x y hactive) (hlinear x' y' hactive')
    have hs : InSliceInfinityPlane
        (sliceProductLinear (mu x y) (nu x y) m n base 0 x y + base) :=
      sliceProductLinear_add_base_infinity_mem _ _ _ _ m n base hmInf hnInf
    have hs' : InSliceInfinityPlane
        (sliceProductLinear (mu x' y') (nu x' y') m n base 0 x' y' + base) :=
      sliceProductLinear_add_base_infinity_mem _ _ _ _ m n base hmInf hnInf
    have hsum := hs.add hs'
    have heq :
        (sliceProductLinear (mu x y) (nu x y) m n base 0 x y + base) +
          (sliceProductLinear (mu x' y') (nu x' y') m n base 0 x' y' + base) =
        sliceTargetDifference x y x' y' := by
      rw [← hp]
      funext i
      simp only [Pi.add_apply]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    rw [heq] at hsum
    exact distinct_corner_target_difference_not_in_infinity_plane
      hdistinct hsum
  · subst lambdaOne
    subst lambdaInfinity
    have hmn : vectorWedge m n = sliceQuadraticA := by
      funext i j
      have hc := congrFun (congrFun hquad i) j
      simp only [one_smul, zero_smul, add_zero, Pi.add_apply, Pi.zero_apply] at hc
      exact (add_eq_zero_iff_eq_neg.mp hc).trans (neg_eq_self_f2 _)
    have hmAnn : vectorWedgeTwo m sliceQuadraticA = 0 := by
      have hw := congrArg (fun q : TwoForm => vectorWedgeTwo m q) hmn
      rw [vectorWedgeTwo_repeated_left] at hw
      exact hw.symm
    have hmComp := sliceQuadraticA_annihilator hmAnn
    have hmNe : m ≠ 0 := by
      intro hm
      rw [hm, vectorWedge_zero_left_qp] at hmn
      exact sliceQuadraticA_ne_zero hmn.symm
    have hnComp := second_factor_mem_of_typeA_wedge hmComp hmNe
      (a := 1) (by simpa using hmn)
    rcases exists_distinct_active_corner_pair hcorners with
      ⟨x, y, x', y', hdistinct, hactive, hactive'⟩
    have hp := sliceProduct_pair_eq_targetDifference
      (hlinear x y hactive) (hlinear x' y' hactive')
    have hs := sliceProductLinear_add_base_mem
      (mu x y) (nu x y) 1 x y m n base hmComp hnComp
    have hs' := sliceProductLinear_add_base_mem
      (mu x' y') (nu x' y') 1 x' y' m n base hmComp hnComp
    have hsum := hs.add hs'
    have heq :
        (sliceProductLinear (mu x y) (nu x y) m n base 1 x y + base) +
          (sliceProductLinear (mu x' y') (nu x' y') m n base 1 x' y' + base) =
        sliceTargetDifference x y x' y' := by
      rw [← hp]
      funext i
      simp only [Pi.add_apply]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    rw [heq] at hsum
    exact distinct_corner_target_difference_not_in_plane hdistinct hsum
  · subst lambdaOne
    subst lambdaInfinity
    have hmn : vectorWedge m n = sliceQuadraticB := by
      funext i j
      have hc := congrFun (congrFun hquad i) j
      simp only [one_smul, Pi.add_apply, Pi.zero_apply] at hc
      rw [sliceQuadraticB, Pi.add_apply]
      have hz : vectorWedge m n i j +
          (sliceQuadraticA i j + sliceInfinityQuadratic i j) = 0 := by
        simpa [add_assoc] using hc
      exact (add_eq_zero_iff_eq_neg.mp hz).trans (neg_eq_self_f2 _)
    have hmAnn : vectorWedgeTwo m sliceQuadraticB = 0 := by
      have hw := congrArg (fun q : TwoForm => vectorWedgeTwo m q) hmn
      rw [vectorWedgeTwo_repeated_left] at hw
      exact hw.symm
    have hmZero := sliceQuadraticB_annihilator hmAnn
    rw [hmZero, vectorWedge_zero_left_qp] at hmn
    exact sliceQuadraticB_ne_zero hmn.symm

/-- Semantic wrapper for the algebraic `Q`/`L` exclusion.  It converts an
equality of the three active six-variable slice functions into their
quadratic and linear homogeneous equations; no truth-table enumeration is
used. -/
theorem no_cubic_seed_three_active_slice_functions
    {delta rho sigma : F₂}
    {anchorLinear companionLinear correctionLinear targetLinear : LinearForm}
    {correctionConst targetConst eps : F₂}
    {correctionCoeff : Fin 3 → F₂}
    (hcorners : ExactlyThreeActiveCorners delta rho sigma)
    (hslice : ∀ x y,
      feedbackCorner delta rho sigma x y = 1 →
      ∀ z : Fin 6 → F₂,
        eval
            (sliceCubicSeedFullModel anchorLinear companionLinear
              correctionConst correctionLinear correctionCoeff x y)
            (sliceAssignment x y z) =
          eval (sliceTangentModel targetConst targetLinear eps x y)
            (sliceAssignment x y z)) : False := by
  rcases exists_distinct_active_corner_pair hcorners with
    ⟨x, y, _x', _y', _hdistinct, hactive, _hactive'⟩
  have heval := eval_eq_of_slice_eq
    (anchorsIndependent_sliceCubicSeedFullModel
      anchorLinear companionLinear correctionConst correctionLinear
      correctionCoeff x y)
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x y)
    (hslice x y hactive)
  have hquad := anfTwoProjection_congr_of_eval_eq heval
  rw [anfTwoProjection_sliceCubicSeedFullModel,
    anfTwoProjection_sliceTangentModel] at hquad
  refine no_cubic_seed_three_active_slices
    (base := sliceComplementLinear correctionLinear)
    (targetBase := sliceComplementLinear targetLinear) hcorners hquad
    (fun x y => sliceAnchorValue anchorLinear x y)
    (fun x y => sliceAnchorValue companionLinear x y + x * y) ?_
  intro x' y' hactive'
  have heval' := eval_eq_of_slice_eq
    (anchorsIndependent_sliceCubicSeedFullModel
      anchorLinear companionLinear correctionConst correctionLinear
      correctionCoeff x' y')
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x' y')
    (hslice x' y' hactive')
  have hlinear := anfLinearProjection_congr_of_eval_eq heval'
  rw [anfLinearProjection_sliceCubicSeedFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear
  exact hlinear

/-- A zero-place feedback cannot use the canonical cubic seed
`M (z + E₀)`.  The only finite data are the three active anchor corners; all
six-variable reasoning is transferred through homogeneous projections. -/
theorem no_zeroAnchored_cubic_feedback_target
    {g correction factor target : ANF 8}
    {targetConst eps delta rho sigma : F₂}
    {targetLinear : LinearForm}
    (hseed : ZeroAnchoredCubicSeedForm g)
    (hcorrection : correction ∈ rationalLowSpace)
    (htargetEq : target = (g + correction) * factor)
    (htargetRep : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactorRep : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) : False := by
  rcases hseed with
    ⟨anchorLinear, companionLinear, seedCorrection,
      hseedCorrectionLow, hseedEq, _hcubicNonzero⟩
  have hcombinedLow : seedCorrection + correction ∈ rationalLowSpace :=
    Submodule.add_mem _ hseedCorrectionLow hcorrection
  rcases exists_representedLowFactor_of_mem hcombinedLow with
    ⟨correctionConst, correctionLinear, correctionCoeff,
      hcombinedRep⟩
  have hsourceRepresentative : g + correction =
      linearANF anchorLinear *
            (linearANF companionLinear +
              rationalANF (rationalSingleton 0)) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff := by
    calc
      g + correction =
          (g + seedCorrection) + (seedCorrection + correction) := by
        symm
        calc
          (g + seedCorrection) + (seedCorrection + correction) =
              g + (seedCorrection + seedCorrection) + correction := by abel
          _ = g + correction := by rw [anf_add_self, add_zero]
      _ = linearANF anchorLinear *
            (linearANF companionLinear +
              rationalANF (rationalSingleton 0)) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff := by rw [hseedEq, hcombinedRep]
  have htargetCanonical : target =
      (linearANF anchorLinear *
            (linearANF companionLinear +
              rationalANF (rationalSingleton 0)) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff) * factor := by
    calc
      target = (g + correction) * factor := htargetEq
      _ = (linearANF anchorLinear *
              (linearANF companionLinear +
                rationalANF (rationalSingleton 0)) +
            representedLowFactor correctionConst correctionLinear
              correctionCoeff) * factor :=
        congrArg (fun p : ANF 8 => p * factor) hsourceRepresentative
  have hcorners := exactlyThreeActiveCorners_of_right_idempotence
    htargetRep hfactorRep hright
  refine no_cubic_seed_three_active_slice_functions
    (anchorLinear := anchorLinear) (companionLinear := companionLinear)
    (correctionLinear := correctionLinear) (targetLinear := targetLinear)
    (correctionConst := correctionConst) (targetConst := targetConst)
    (eps := eps) (correctionCoeff := correctionCoeff) hcorners ?_
  intro x y hactive z
  calc
    eval
        (sliceCubicSeedFullModel anchorLinear companionLinear
          correctionConst correctionLinear correctionCoeff x y)
        (sliceAssignment x y z) =
      eval
        (linearANF anchorLinear *
              (linearANF companionLinear +
                rationalANF (rationalSingleton 0)) +
            representedLowFactor correctionConst correctionLinear
              correctionCoeff)
        (sliceAssignment x y z) :=
      eval_sliceCubicSeedFullModel_eq_normalized
        anchorLinear companionLinear correctionConst correctionLinear
        correctionCoeff x y z
    _ = eval target (sliceAssignment x y z) := by
      have hs := congrArg
        (fun p : ANF 8 => eval p (sliceAssignment x y z))
        htargetCanonical
      rw [eval_mul', eval_zero_place_feedback hfactorRep,
        hactive, mul_one] at hs
      exact hs.symm
    _ = eval (sliceTangentModel targetConst targetLinear eps x y)
        (sliceAssignment x y z) :=
      htargetRep ▸
        (eval_sliceTangentModel targetConst targetLinear eps x y z).symm

/-- The complete cubic classification is incompatible with either
idempotence identity.  The classified place is transported to zero, with the
seed and feedback kept at that same indexed place. -/
theorem seedUsingCubicClassifiedForm_impossible
    {g : ANF 8}
    (hseed : CubicSeedAnchoredForm g)
    (hfeedback : SeedUsingCubicClassifiedForm g) : False := by
  rcases hfeedback with ⟨theta, hfeedbackAt⟩
  have hnormalized := seedUsingCubicClassified_normalized_anchor_at
    hseed hfeedbackAt
  have hzeroSeed := normalizedCubicAnchorForm_zeroRepresentative_at
    hnormalized
  rcases hfeedbackAt with
    ⟨correction, factor, target, targetConst, factorConst,
      targetLinear, factorLinear, targetCoeff, factorCoeff, eps,
      hcorrection, _hfactorLow, htargetEq, _htargetAmbient,
      _htargetNotLow, htargetRep, hfactorRep, _htargetNonrational,
      _hann, _hleft, hright, hfactorSingleton, htargetTangent⟩
  let Phi := anfPlaceNormalize theta
  have hcorrection' : Phi correction ∈ rationalLowSpace :=
    anfPlaceNormalize_mem_rationalLow theta hcorrection
  have htargetRep' : Phi target =
      affineANF targetConst (normalizePlaceLinear theta targetLinear) +
        targetANF (rationalTangentAt 0 eps) := by
    rw [htargetRep, map_add, anfPlaceNormalize_affineANF,
      htargetTangent, anfPlaceNormalize_tangent_self]
  have hfactorRep' : Phi factor =
      affineANF factorConst (normalizePlaceLinear theta factorLinear) +
        rationalANF (rationalSingleton 0) := by
    rw [hfactorRep, map_add, anfPlaceNormalize_affineANF,
      anfPlaceNormalize_rationalANF, hfactorSingleton,
      normalizeRationalCoeff_singleton_self]
  have htargetEq' : Phi target =
      (Phi g + Phi correction) * Phi factor := by
    calc
      Phi target = Phi ((g + correction) * factor) :=
        congrArg Phi htargetEq
      _ = Phi (g + correction) * Phi factor := map_mul Phi _ _
      _ = (Phi g + Phi correction) * Phi factor := by rw [map_add]
  have hright' : Phi target * Phi factor = Phi target := by
    calc
      Phi target * Phi factor = Phi (target * factor) :=
        (map_mul Phi _ _).symm
      _ = Phi target := congrArg Phi hright
  rcases zeroPlaceFeedbackForm_of_right_idempotence
      htargetRep' hfactorRep' hright' with
    ⟨delta, rho, sigma, hfeedbackRep⟩
  exact no_zeroAnchored_cubic_feedback_target hzeroSeed hcorrection'
    htargetEq' htargetRep' hfeedbackRep hright'

/-- A new target at the fifth gate represented, modulo the preceding flag, by a low-low product. -/
@[expose]
def FirstLowLowData (C : Circuit 8 8) : Prop :=
  ∃ (target representative shift : ANF 8),
    target ∈ targetAmbient 8 (mulTarget 4) ∧
    target ∉ circuitFlag C 4 ∧
    target ∈ circuitFlag C 5 ∧
    shift ∈ circuitFlag C 4 ∧
    target = shift + representative ∧
    IsLowLowProduct representative

/-- Circuit-facing endpoint of the first-feedback exclusion: the first useful
post-seed gate is necessarily low--low. -/
theorem NormalizedEight.firstUsefulChild_isLowLow
    {C : Circuit 8 8} (h : NormalizedEight C) : FirstLowLowData C := by
  rcases h.usefulSeedChildData with
    ⟨target, representative, shift, htarget, htargetOld, htargetNew, hshift,
      htargetEq, hlowLow | hseedUsing⟩
  · exact ⟨target, representative, shift, htarget, htargetOld, htargetNew, hshift,
      htargetEq, hlowLow⟩
  · exact (seedUsingCubicClassifiedForm_impossible
      h.cubicSeedAnchoredForm
      (h.seedUsingCubicClassifiedForm_of_child htarget htargetOld hshift
        htargetEq hseedUsing)).elim

end

end N4
end UnrestrictedBooleanMul
