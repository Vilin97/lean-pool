/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SecondJet

/-!
# Excluding a seed-using second feedback

This file composes the manuscript's degree-five, degree-four, and degree-three
rows.  A target outside the feedback state is first forced to be a second
jet.  Its right absorption identity then kills the feedback quadratic and
linear parts of the other factor.  The remaining constant would put the
nonzero seed cubic in the quadratic target ambient.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem mem_feedbackCoeffSpace_iff_exists_rep (c : TargetCoeff) :
    c ∈ feedbackCoeffSpace ↔ ∃ q : FeedbackCoord, c = feedbackCoeffRep q := by
  constructor
  · intro hc
    rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂)
      (v := ![targetBasis 0, targetBasis 1, targetBasis 6, rOneCoeff])
      (x := c)).mp hc with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [← hq]
    funext i
    fin_cases i <;>
      simp [feedbackCoeffRep, Fin.sum_univ_succ, targetBasis, Pi.basisFun, rOneCoeff]
  · rintro ⟨q, rfl⟩
    change q 0 • targetBasis 0 + q 1 • targetBasis 1 +
      q 2 • targetBasis 6 + q 3 • rOneCoeff ∈ feedbackCoeffSpace
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨0, by simp⟩)
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨1, by simp⟩)
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨2, by simp⟩)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨3, by simp⟩)

theorem feedbackTarget_mem_zeroFeedbackLow (q : FeedbackCoord) :
    targetANF (feedbackCoeffRep q) ∈ zeroFeedbackLowSpace := by
  let alpha : Fin 3 → F₂ := ![q 0, q 3, q 2]
  have hcoeff : feedbackCoeffRep q = rationalCoeffRep alpha +
      q 1 • rationalTangentAt 0 0 := by
    funext i
    fin_cases i <;>
      simp [feedbackCoeffRep, alpha, rationalCoeffRep, rationalTangentAt, rZeroCoeff,
        rOneCoeff, rInfinityCoeff, targetBasis, Pi.basisFun] <;>
      ring
  rw [hcoeff]
  change targetANFLinear
      (rationalCoeffRep alpha + q 1 • rationalTangentAt 0 0) ∈ _
  rw [map_add, map_smul]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left
      (by
        change rationalANF alpha ∈ rationalLowSpace
        simpa [representedLowFactor, affineANF, linearANF] using
          representedLowFactor_mem 0 0 alpha)
  · exact Submodule.smul_mem _ _ (zero_tangent_mem_feedbackLow 0)

theorem targetRep_mem_zeroFeedbackLow_iff
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) :
    affineANF a ell + targetANF c ∈ zeroFeedbackLowSpace ↔
      c ∈ feedbackCoeffSpace := by
  constructor
  · intro hp
    rcases exists_feedbackLow_rep hp with ⟨b, m, q, hrep⟩
    have hproj := congrArg anfTwoProjection hrep
    rw [map_add, map_add,
      anfTwoProjection_kills_affine (affineANF_mem a ell),
      anfTwoProjection_kills_affine (affineANF_mem b m),
      anfTwoProjection_targetANF, anfTwoProjection_targetANF,
      zero_add, zero_add] at hproj
    have hc : c = feedbackCoeffRep q := targetTwo_injective hproj
    exact (mem_feedbackCoeffSpace_iff_exists_rep c).mpr ⟨q, hc⟩
  · intro hc
    rcases (mem_feedbackCoeffSpace_iff_exists_rep c).mp hc with ⟨q, rfl⟩
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_left (affineANF_mem a ell))
    · exact feedbackTarget_mem_zeroFeedbackLow q

/-- Quartic degree in a right absorption identity is exactly the wedge of
the target coefficient with the feedback coefficient of the factor. -/
theorem target_feedback_absorption_wedge_zero
    (A b : F₂) (ell m : LinearForm) (c : TargetCoeff) (q : FeedbackCoord)
    (habsorb :
      (affineANF A ell + targetANF c) *
          (affineANF b m + targetANF (feedbackCoeffRep q)) =
        affineANF A ell + targetANF c) :
    feedbackQuarticWedgeProbe (targetTwo c)
      (targetTwo (feedbackCoeffRep q)) = 0 := by
  have hprobe := congrArg feedbackQuarticProbeANF habsorb
  simp only [add_mul, mul_add, map_add] at hprobe
  have haa : feedbackQuarticProbeANF
      (affineANF A ell * affineANF b m) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      (((degreeLE_one_affineANF A ell).mul
        (degreeLE_one_affineANF b m)).mono (by omega))
  have hat : feedbackQuarticProbeANF
      (affineANF A ell * targetANF (feedbackCoeffRep q)) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      (((degreeLE_one_affineANF A ell).mul
        (degreeLE_two_targetANF _)).mono (by omega))
  have hta : feedbackQuarticProbeANF
      (targetANF c * affineANF b m) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      (((degreeLE_two_targetANF c).mul
        (degreeLE_one_affineANF b m)).mono (by omega))
  have hrAffine : feedbackQuarticProbeANF (affineANF A ell) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((degreeLE_one_affineANF A ell).mono (by omega))
  have hrTarget : feedbackQuarticProbeANF (targetANF c) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((degreeLE_two_targetANF c).mono (by omega))
  rw [haa, hat, hta, hrAffine, hrTarget,
    feedbackQuarticProbe_target_mul_target] at hprobe
  simpa using hprobe

/-- Algebraic exclusion of the `G`-using type of second feedback. -/
theorem no_normalizedSeedUsing_feedbackTarget
    {g correction addend factor F : ANF 8}
    {M N : LinearForm} {pa pb ja jb : F₂}
    (hg : DegreeLE 3 g)
    (hcorrection : correction ∈ rationalLowSpace)
    (hseed : g + correction = linearANF M *
      (linearANF N + rationalANF (rationalSingleton 0)))
    (hM : M = normalizedFirstJetVector pa pb ja jb)
    (hjet : ja ≠ 0 ∨ jb ≠ 0)
    (hseedCubic : vectorWedgeTwo M (rationalPlaceTwo 0) ≠ 0)
    (haddend : addend ∈ zeroFeedbackLowSpace)
    (hfactor : factor ∈ zeroFeedbackLowSpace)
    (hFmem : F ∈ targetAmbient 8 (mulTarget 4))
    (hFoutside : F ∉ zeroFeedbackLowSpace)
    (hF : F = (g + addend) * factor) : False := by
  rcases exists_targetAmbient_rep hFmem with ⟨u, c, hu, hFrepU⟩
  rcases exists_affineANF_of_mem hu with ⟨fConst, fLinear, huRep⟩
  have hFrep : F = affineANF fConst fLinear + targetANF c := by
    rw [hFrepU, huRep]
  have hcoutside : c ∉ feedbackCoeffSpace := by
    intro hc
    apply hFoutside
    rw [hFrep]
    exact (targetRep_mem_zeroFeedbackLow_iff fConst fLinear c).mpr hc
  rcases exists_feedbackLow_rep hfactor with
    ⟨factorConst, factorLinear, q, hfactorRep⟩
  rcases absorption_of_eq hF with ⟨hleft, hright⟩
  have hleftRep : (g + addend) *
      (affineANF fConst fLinear + targetANF c) =
        affineANF fConst fLinear + targetANF c := by
    rw [← hFrep]
    exact hleft
  have hhard : hardQuinticWedgeProbe M c = 0 :=
    normalizedSeed_absorption_hardAnnihilator hg
      (degreeLE_two_of_mem_rationalLow hcorrection)
      (degreeLE_two_of_mem_zeroFeedbackLowSpace haddend)
      hseed hleftRep
  rw [hM] at hhard
  rcases hardAnnihilator_outside_feedback_is_secondJet
      pa pb ja jb c hjet hcoutside hhard with ⟨alpha, beta, hcSecond⟩
  have hrightRep :
      (affineANF fConst fLinear + targetANF c) *
          (affineANF factorConst factorLinear +
            targetANF (feedbackCoeffRep q)) =
        affineANF fConst fLinear + targetANF c := by
    rw [← hFrep, ← hfactorRep]
    exact hright
  have hwedge := target_feedback_absorption_wedge_zero
    fConst factorConst fLinear factorLinear c q hrightRep
  rw [hcSecond] at hwedge
  have hrow (u : Fin 6) :
      feedbackQuarticWedgeProbe
        (targetTwo (secondJetFeedbackCoeff alpha beta))
        (targetTwo (feedbackCoeffRep q)) u = 0 := by
    exact congrFun hwedge u
  have hq : q = 0 := secondJet_wedge_feedback_injective_of_rows
    alpha beta q
    (by simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using hrow 0)
    (by simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using hrow 1)
    (by simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using hrow 5)
    (by simpa [feedbackQuarticWedgeProbe, feedbackQuarticCoord] using hrow 4)
  have hfactorAffine : factor = affineANF factorConst factorLinear := by
    rw [hfactorRep, hq]
    have hcoeff : feedbackCoeffRep (0 : FeedbackCoord) = 0 := by
      funext i
      simp [feedbackCoeffRep]
    rw [hcoeff]
    change affineANF factorConst factorLinear + targetANFLinear 0 = _
    rw [map_zero, add_zero]
  have hfactorLinearZero : factorLinear = 0 := by
    have hcubic := congrArg anfThreeProjection hright
    rw [hFrep, hfactorAffine,
      anfThreeProjection_targetRep_mul_affine] at hcubic
    have hFzero := anfThreeProjection_eq_zero_of_mem_targetAmbient hFmem
    have hFrepZero : anfThreeProjection
        (affineANF fConst fLinear + targetANF c) = 0 := by
      rw [← hFrep]
      exact hFzero
    have hw : vectorWedgeTwo factorLinear (targetTwo c) = 0 :=
      hcubic.trans hFrepZero
    rw [hcSecond] at hw
    exact secondJet_vector_wedge_injective alpha beta factorLinear hw
  have hfactorConstOne : factorConst = 1 := by
    rcases f2_eq_zero_or_one factorConst with hzero | hone
    · exfalso
      have hfactorZero : factor = 0 := by
        rw [hfactorAffine, hfactorLinearZero, hzero]
        simp [affineANF]
      have hFzero : F = 0 := by
        rw [hF, hfactorZero, mul_zero]
      apply hFoutside
      rw [hFzero]
      exact Submodule.zero_mem _
    · exact hone
  have hfactorOne : factor = 1 := by
    rw [hfactorAffine, hfactorLinearZero, hfactorConstOne]
    simp [affineANF]
  have hFseed : F = g + addend := by
    rw [hF, hfactorOne, mul_one]
  have hcorrectionCubic := anfThreeProjection_eq_zero_of_degreeLE_two
    (degreeLE_two_of_mem_rationalLow hcorrection)
  have haddendCubic := anfThreeProjection_eq_zero_of_degreeLE_two
    (degreeLE_two_of_mem_zeroFeedbackLowSpace haddend)
  have hseedProjection := congrArg anfThreeProjection hseed
  rw [map_add, hcorrectionCubic, add_zero, mul_add, map_add,
    anfThreeProjection_linear_mul_linear,
    anfThreeProjection_linear_mul_rational, zero_add,
    rationalTwo_singleton_zero] at hseedProjection
  have hFzero := anfThreeProjection_eq_zero_of_mem_targetAmbient hFmem
  rw [hFseed, map_add, haddendCubic, add_zero,
    hseedProjection] at hFzero
  apply hseedCubic
  rw [rationalPlaceTwo_zero_eq]
  exact hFzero

end

end N4
end UnrestrictedBooleanMul
