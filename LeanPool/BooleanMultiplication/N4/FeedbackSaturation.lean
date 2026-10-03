/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SecondFeedbackHigh

/-!
# Saturation after the first feedback

This file returns from the homogeneous algebra to the normalized circuit.
Every input of gate six is a feedback-low wire plus one Boolean multiple of
the normalized seed.  Boolean idempotence reduces their product, modulo that
state, to exactly the two algebraic types excluded in
`SecondFeedbackUsing` and `SecondFeedbackHigh`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The zero-place feedback space enlarged by one seed ANF. -/
def normalizedFeedbackState (g : ANF 8) : Submodule F₂ (ANF 8) :=
  zeroFeedbackLowSpace ⊔ Submodule.span F₂ {g}

/-- A product of two ANFs in the zero-place feedback space. -/
def IsFeedbackLowLowProduct (f : ANF 8) : Prop :=
  ∃ p q : ANF 8,
    p ∈ zeroFeedbackLowSpace ∧ q ∈ zeroFeedbackLowSpace ∧ f = p * q

/-- A product of a seed plus a feedback-low term with another feedback-low term. -/
def IsNormalizedSeedUsingProduct (g f : ANF 8) : Prop :=
  ∃ a c : ANF 8,
    a ∈ zeroFeedbackLowSpace ∧ c ∈ zeroFeedbackLowSpace ∧
      f = (g + a) * c

private theorem one_mem_zeroFeedbackLowSpace :
    (1 : ANF 8) ∈ zeroFeedbackLowSpace :=
  Submodule.mem_sup_left (Submodule.mem_sup_left (one_mem_affine 8))

theorem exists_feedback_add_seed_of_mem_normalizedFeedbackState
    {g w : ANF 8} (hw : w ∈ normalizedFeedbackState g) :
    ∃ (low : ANF 8) (e : F₂),
      low ∈ zeroFeedbackLowSpace ∧ w = low + e • g := by
  rcases Submodule.mem_sup.mp hw with ⟨low, hlow, seed, hseed, rfl⟩
  rcases Submodule.mem_span_singleton.mp hseed with ⟨e, rfl⟩
  exact ⟨low, e, hlow, rfl⟩

/-- Product normalization inside the post-jet state.  This is the same
four-case Boolean identity as the seed-state normalization, now over the
larger feedback-low subspace. -/
theorem normalize_feedback_state_product
    {g l r : ANF 8}
    (hl : l ∈ normalizedFeedbackState g)
    (hr : r ∈ normalizedFeedbackState g) :
    ∃ (f s : ANF 8),
      s ∈ normalizedFeedbackState g ∧
      l * r = s + f ∧
      (IsFeedbackLowLowProduct f ∨
        IsNormalizedSeedUsingProduct g f) := by
  rcases exists_feedback_add_seed_of_mem_normalizedFeedbackState hl with
    ⟨p, ep, hp, rfl⟩
  rcases exists_feedback_add_seed_of_mem_normalizedFeedbackState hr with
    ⟨q, eq, hq, rfl⟩
  rcases f2_eq_zero_or_one ep with rfl | rfl <;>
    rcases f2_eq_zero_or_one eq with rfl | rfl
  · refine ⟨p * q, 0, Submodule.zero_mem _, ?_,
      Or.inl ⟨p, q, hp, hq, rfl⟩⟩
    simp
  · refine ⟨(g + q) * p, 0, Submodule.zero_mem _, ?_,
      Or.inr ⟨q, p, hq, hp, rfl⟩⟩
    simp only [zero_smul, one_smul, add_zero, zero_add]
    rw [mul_comm p]
    congr 1
    exact add_comm _ _
  · refine ⟨(g + p) * q, 0, Submodule.zero_mem _, ?_,
      Or.inr ⟨p, q, hp, hq, rfl⟩⟩
    simp [add_comm]
  · let u : ANF 8 := g + p
    let c : ANF 8 := p + q
    refine ⟨u * c, u, ?_, ?_, Or.inr ⟨p, c, hp, ?_, rfl⟩⟩
    · exact Submodule.add_mem _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self g))
        (Submodule.mem_sup_left hp)
    · simp only [one_smul]
      have hl' : p + g = u := by simp [u, add_comm]
      have hr' : q + g = u + c := by
        change q + g = (g + p) + (p + q)
        symm
        calc
          (g + p) + (p + q) = g + (p + p) + q := by ac_rfl
          _ = g + q := by simp
          _ = q + g := by ac_rfl
      rw [hl', hr', mul_add, anf_mul_self]
    · exact Submodule.add_mem _ hp hq

/-- A zero-place feedback-low vector pulled back by the involutive place
change is already present before gate six. -/
theorem normalizedFeedbackLow_pullback_mem_five
    {C : Circuit 8 8} (h : NormalizedEight C)
    {theta : Fin 3} {eps : F₂}
    (hflag : circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)})
    {p : ANF 8} (hp : p ∈ zeroFeedbackLowSpace) :
    anfPlaceNormalize theta p ∈ circuitFlag C 5 := by
  rcases Submodule.mem_sup.mp hp with ⟨rational, hrational, tangent,
    htangent, rfl⟩
  rw [map_add]
  apply Submodule.add_mem
  · have hrational' : anfPlaceNormalize theta rational ∈ rationalLowSpace :=
      anfPlaceNormalize_mem_rationalLow theta hrational
    rw [hflag]
    exact Submodule.mem_sup_left (by
      rw [h.wireSpace_four_eq]
      exact Submodule.mem_sup_left hrational')
  · rcases Submodule.mem_span_singleton.mp htangent with ⟨b, rfl⟩
    rw [map_smul]
    apply Submodule.smul_mem
    have hnormalize :
        anfPlaceNormalize theta
            (targetANF (rationalTangentAt 0 0)) =
          targetANF (rationalTangentAt theta 0) := by
      have hself := congrArg (anfPlaceNormalize theta)
        (anfPlaceNormalize_tangent_self theta 0)
      simpa [anfPlaceNormalize_involutive] using hself.symm
    rw [hnormalize]
    have hcoeff : rationalTangentAt theta 0 =
        eps • rationalPlaceCoeff theta + rationalTangentAt theta eps := by
      funext i
      fin_cases theta <;> fin_cases i <;>
        simp [rationalTangentAt, rationalPlaceCoeff, rZeroCoeff, rOneCoeff, rInfinityCoeff
          ] <;> ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2]
    change targetANFLinear (rationalTangentAt theta 0) ∈ circuitFlag C 5
    rw [hcoeff, map_add, map_smul]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      rw [hflag]
      apply Submodule.mem_sup_left
      rw [h.wireSpace_four_eq]
      apply Submodule.mem_sup_left
      apply Submodule.mem_sup_right
      apply (mem_rationalTargetSpace_iff _).mpr
      exact ⟨rationalSingleton theta, by
        change targetANFLinear (rationalPlaceCoeff theta) =
          targetANFLinear (rationalCoeffRep (rationalSingleton theta))
        congr 1
        funext i
        fin_cases theta <;> fin_cases i <;>
          simp [rationalPlaceCoeff, rationalCoeffRep, rationalSingleton, rZeroCoeff,
            rOneCoeff, rInfinityCoeff]⟩
    · rw [hflag]
      exact Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self _)

theorem normalized_targetWitness_not_feedbackLow
    {C : Circuit 8 8} (h : NormalizedEight C)
    {theta : Fin 3} {eps : F₂}
    (hflag : circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)})
    {t : ANF 8} (ht : t ∉ circuitFlag C 5) :
    anfPlaceNormalize theta t ∉ zeroFeedbackLowSpace := by
  intro hlow
  apply ht
  have hpull := normalizedFeedbackLow_pullback_mem_five h hflag hlow
  simpa [anfPlaceNormalize_involutive] using hpull

theorem zeroFeedbackLow_mem_targetAmbient {p : ANF 8}
    (hp : p ∈ zeroFeedbackLowSpace) :
    p ∈ targetAmbient 8 (mulTarget 4) := by
  rcases exists_feedbackLow_rep hp with ⟨a, ell, q, rfl⟩
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (affineANF_mem a ell)
  · exact Submodule.mem_sup_right (targetANF_mem_mulTarget _)

/-- Gate six cannot be useful after the normalized first feedback.  The
proof contains no circuit enumeration: it uses the flag decomposition once,
then the two algebraic second-feedback exclusions. -/
theorem NormalizedEight.gateSix_not_useful
    {C : Circuit 8 8} (h : NormalizedEight C) :
    ¬ UsefulAt C (mulTarget 4) 5 := by
  intro huse
  rcases h.zeroNormalizedFirstJetState with
    ⟨theta, eps, M, companion, correction, pa, pb, ja, jb,
      hcorrection, hseedRaw, hseedCubic, hM, hjet, hflag⟩
  let g : ANF 8 := anfPlaceNormalize theta (C.gate 3)
  have hseed : g + correction = linearANF M *
      (linearANF companion + rationalANF (rationalSingleton 0)) := by
    simpa [g] using hseedRaw
  have hMDegree : DegreeLE 1 (linearANF M) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 M
  have hcompanionDegree : DegreeLE 1 (linearANF companion) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 companion
  have hmodelDegree : DegreeLE 3
      (linearANF M *
        (linearANF companion + rationalANF (rationalSingleton 0))) :=
    hMDegree.mul
      ((hcompanionDegree.mono (by omega)).add
        (degreeLE_two_rationalANF (rationalSingleton 0)))
  have hg : DegreeLE 3 g := by
    have hcorrectionDegree : DegreeLE 3 correction :=
      (degreeLE_two_of_mem_rationalLow hcorrection).mono (by omega)
    have hgeq : g = correction +
        linearANF M *
          (linearANF companion + rationalANF (rationalSingleton 0)) := by
      calc
        g = correction + (g + correction) := by
          symm
          calc
            correction + (g + correction) =
                (correction + correction) + g := by ac_rfl
            _ = g := by simp
        _ = correction + linearANF M *
            (linearANF companion + rationalANF (rationalSingleton 0)) := by
          rw [hseed]
    rw [hgeq]
    exact hcorrectionDegree.add hmodelDegree
  rcases exists_targetWitness_eq_state_add_gate_of_useful
      C (mulTarget 4) (5 : Fin 8) huse with
    ⟨t, v, htAmbient, htOld, _htNew, hv, htv⟩
  let F : ANF 8 := anfPlaceNormalize theta t
  have hFmem : F ∈ targetAmbient 8 (mulTarget 4) := by
    exact anfPlaceNormalize_mem_targetAmbient theta htAmbient
  have hFoutside : F ∉ zeroFeedbackLowSpace := by
    exact normalized_targetWitness_not_feedbackLow h hflag htOld
  rcases exists_normalized_feedback_add_seed_of_mem_five h hflag hv with
    ⟨vLow, ev, hvLow, hvRep⟩
  rcases exists_normalized_feedback_add_seed_of_mem_five h hflag
      (C.left_mem 5) with ⟨leftLow, el, hleftLow, hleftRep⟩
  rcases exists_normalized_feedback_add_seed_of_mem_five h hflag
      (C.right_mem 5) with ⟨rightLow, er, hrightLow, hrightRep⟩
  have hvState : anfPlaceNormalize theta v ∈ normalizedFeedbackState g := by
    rw [hvRep]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hvLow)
      (Submodule.smul_mem _ _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self g)))
  have hleftState : anfPlaceNormalize theta (C.left 5) ∈
      normalizedFeedbackState g := by
    rw [hleftRep]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hleftLow)
      (Submodule.smul_mem _ _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self g)))
  have hrightState : anfPlaceNormalize theta (C.right 5) ∈
      normalizedFeedbackState g := by
    rw [hrightRep]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hrightLow)
      (Submodule.smul_mem _ _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self g)))
  rcases normalize_feedback_state_product hleftState hrightState with
    ⟨f, s, hs, hproduct, hshape⟩
  have hFgate : F = anfPlaceNormalize theta v +
      anfPlaceNormalize theta (C.left 5) *
        anfPlaceNormalize theta (C.right 5) := by
    dsimp [F]
    rw [htv, map_add, C.gate_eq 5, map_mul]
  have hstate : anfPlaceNormalize theta v + s ∈
      normalizedFeedbackState g := Submodule.add_mem _ hvState hs
  rcases exists_feedback_add_seed_of_mem_normalizedFeedbackState hstate with
    ⟨shift, e, hshift, hstateRep⟩
  have hFshape : F = shift + e • g + f := by
    rw [hFgate, hproduct]
    calc
      anfPlaceNormalize theta v + (s + f) =
          (anfPlaceNormalize theta v + s) + f := by ac_rfl
      _ = (shift + e • g) + f := by rw [hstateRep]
  rcases hshape with hlowLow | hseedUsing
  · rcases hlowLow with ⟨p, q, hp, hq, hf⟩
    rcases f2_eq_zero_or_one e with rfl | rfl
    · have hFzero : F = shift + p * q := by
        simpa [hf] using hFshape
      have hpqAmbient : p * q ∈ targetAmbient 8 (mulTarget 4) := by
        have hadd := Submodule.add_mem _ hFmem
          (zeroFeedbackLow_mem_targetAmbient hshift)
        have heq : F + shift = p * q := by
          rw [hFzero]
          calc
            (shift + p * q) + shift =
                (shift + shift) + p * q := by ac_rfl
            _ = p * q := by simp
        rwa [heq] at hadd
      have hpqLow := feedbackLow_mul_mem_of_mem_targetAmbient hp hq hpqAmbient
      apply hFoutside
      rw [hFzero]
      exact Submodule.add_mem _ hshift hpqLow
    · have hFone : F = shift + g + p * q := by
        simpa [hf] using hFshape
      exact no_normalizedLowLow_feedbackTarget hg hcorrection hseed hM hjet
        hseedCubic hshift hp hq hFmem hFoutside hFone
  · rcases hseedUsing with ⟨a, c, ha, hc, hf⟩
    rcases f2_eq_zero_or_one e with rfl | rfl
    · have hFzero : F = shift + (g + a) * c := by
        simpa [hf] using hFshape
      let F' : ANF 8 := (g + a) * c
      have hF'mem : F' ∈ targetAmbient 8 (mulTarget 4) := by
        have hadd := Submodule.add_mem _ hFmem
          (zeroFeedbackLow_mem_targetAmbient hshift)
        have heq : F + shift = F' := by
          dsimp [F']
          rw [hFzero]
          calc
            (shift + (g + a) * c) + shift =
                (shift + shift) + (g + a) * c := by ac_rfl
            _ = (g + a) * c := by simp
        rwa [heq] at hadd
      have hF'outside : F' ∉ zeroFeedbackLowSpace := by
        intro hF'low
        apply hFoutside
        rw [hFzero]
        exact Submodule.add_mem _ hshift hF'low
      exact no_normalizedSeedUsing_feedbackTarget hg hcorrection hseed hM
        hjet hseedCubic ha hc hF'mem hF'outside rfl
    · have hFone : F = shift + g + (g + a) * c := by
        simpa [hf] using hFshape
      let c' : ANF 8 := c + 1
      let F' : ANF 8 := (g + a) * c'
      have hc' : c' ∈ zeroFeedbackLowSpace :=
        Submodule.add_mem _ hc one_mem_zeroFeedbackLowSpace
      have hF'split : F = (shift + a) + F' := by
        dsimp [F', c']
        rw [mul_add, mul_one, hFone]
        symm
        calc
          (shift + a) + ((g + a) * c + (g + a)) =
              (a + a) + (shift + (g + a) * c + g) := by ac_rfl
          _ = shift + (g + a) * c + g := by simp
          _ = shift + g + (g + a) * c := by ac_rfl
      have hshiftA : shift + a ∈ zeroFeedbackLowSpace :=
        Submodule.add_mem _ hshift ha
      have hF'mem : F' ∈ targetAmbient 8 (mulTarget 4) := by
        have hadd := Submodule.add_mem _ hFmem
          (zeroFeedbackLow_mem_targetAmbient hshiftA)
        have heq : F + (shift + a) = F' := by
          rw [hF'split]
          calc
            ((shift + a) + F') + (shift + a) =
                ((shift + a) + (shift + a)) + F' := by ac_rfl
            _ = F' := by simp
        rwa [heq] at hadd
      have hF'outside : F' ∉ zeroFeedbackLowSpace := by
        intro hF'low
        apply hFoutside
        rw [hF'split]
        exact Submodule.add_mem _ hshiftA hF'low
      exact no_normalizedSeedUsing_feedbackTarget hg hcorrection hseed hM
        hjet hseedCubic ha hc' hF'mem hF'outside rfl

end

end N4
end UnrestrictedBooleanMul
