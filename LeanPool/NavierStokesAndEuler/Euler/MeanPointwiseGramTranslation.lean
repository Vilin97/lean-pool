/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse

/-!
# Ordinary spatial covariance of the mean Gram inverse

These identities act at one actual time slice in ordinary solenoidal L².
They identify the continuous acceleration family with translation of the
original acceleration, including endpoint time values.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPointwiseGramTranslation

open InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerTransverseGramInverse

private theorem eq_of_translated_inner (a : Space) (x y : solenoidalSpace)
    (h : ∀ v, ⟪x, solenoidalTranslation a v⟫_ℝ = ⟪y, solenoidalTranslation a v⟫_ℝ) : x = y := by
  apply ext_inner_right ℝ
  intro v
  simpa only [solenoidalTranslation_add, add_neg_cancel, solenoidalTranslation_zero] using
    h (solenoidalTranslation (-a) v)

theorem frame_translation (a : Space) (F : L2 →L[ℝ] L2) (v : solenoidalSpace) :
    ((translateOperator a F).comp solenoidalSpace.subtypeL) (solenoidalTranslation a v) =
      translation a ((F.comp solenoidalSpace.subtypeL) v) :=
  translateOperator_translation a F (v : L2)

theorem frameAdjoint_translation (a : Space) (F : L2 →L[ℝ] L2) (f : L2) :
    ((translateOperator a F).comp solenoidalSpace.subtypeL).adjoint (translation a f) =
      solenoidalTranslation a ((F.comp solenoidalSpace.subtypeL).adjoint f) := by
  apply eq_of_translated_inner a
  intro v
  exact (adjoint_inner_left ((translateOperator a F).comp solenoidalSpace.subtypeL)
      (solenoidalTranslation a v) (translation a f)).trans
    ((congrArg (fun z : L2 => ⟪translation a f,z⟫_ℝ) (frame_translation a F v)).trans
      (((translation a).inner_map_map f ((F.comp solenoidalSpace.subtypeL) v)).trans
        ((adjoint_inner_left (F.comp solenoidalSpace.subtypeL) v f).symm.trans
          ((solenoidalTranslation a).inner_map_map ((F.comp solenoidalSpace.subtypeL).adjoint f)
              v).symm)))

theorem gram_translation (a : Space) (F : L2 →L[ℝ] L2) (v : solenoidalSpace) :
    gram ((translateOperator a F).comp solenoidalSpace.subtypeL) (solenoidalTranslation a v) =
      solenoidalTranslation a (gram (F.comp solenoidalSpace.subtypeL) v) :=
  (congrArg ((translateOperator a F).comp solenoidalSpace.subtypeL).adjoint
    (frame_translation a F v)).trans
      (frameAdjoint_translation a F ((F.comp solenoidalSpace.subtypeL) v))

theorem translated_lower (a : Space) (F : L2 →L[ℝ] L2) (c : ℝ)
    (hF : ∀ v : solenoidalSpace, c*‖v‖^2 ≤ ‖(F.comp solenoidalSpace.subtypeL) v‖^2)
    (v : solenoidalSpace) :
    c*‖v‖^2 ≤ ‖((translateOperator a F).comp solenoidalSpace.subtypeL) v‖^2 := by
  have h := hF (solenoidalTranslation (-a) v)
  change c*‖solenoidalTranslation (-a) v‖^2 ≤ ‖F (translation (-a) (v : L2))‖^2 at h
  change c*‖v‖^2 ≤ ‖translation a (F (translation (-a) (v : L2)))‖^2
  simpa only [LinearIsometry.norm_map] using h

theorem gramInverse_translation (a : Space) (F : L2 →L[ℝ] L2) (c : ℝ) (hc : 0 < c)
    (hF : ∀ v : solenoidalSpace, c*‖v‖^2 ≤ ‖(F.comp solenoidalSpace.subtypeL) v‖^2)
    (g : solenoidalSpace) :
    gramInverse ((translateOperator a F).comp solenoidalSpace.subtypeL) c hc
        (translated_lower a F c hF) (solenoidalTranslation a g) =
      solenoidalTranslation a (gramInverse (F.comp solenoidalSpace.subtypeL) c hc hF g) := by
  have he := (gram_translation a F (gramInverse (F.comp solenoidalSpace.subtypeL) c hc hF g)).trans
    (congrArg (solenoidalTranslation a) (gram_inverse_apply (F.comp solenoidalSpace.subtypeL) c hc
        hF g))
  have hi := congrArg (gramInverse ((translateOperator a F).comp solenoidalSpace.subtypeL)
    c hc (translated_lower a F c hF)) he
  exact hi.symm.trans (inverse_gram_apply ((translateOperator a F).comp solenoidalSpace.subtypeL)
    c hc (translated_lower a F c hF)
    (solenoidalTranslation a (gramInverse (F.comp solenoidalSpace.subtypeL) c hc hF g)))

/-- The actual one-time acceleration operator from the strong mean equation. -/
def acceleration (F F₁ : L2 →L[ℝ] L2) (c : ℝ) (hc : 0 < c)
    (hF : ∀ v : solenoidalSpace, c*‖v‖^2 ≤ ‖(F.comp solenoidalSpace.subtypeL) v‖^2)
    (v : solenoidalSpace) (f : L2) : solenoidalSpace :=
  gramInverse (F.comp solenoidalSpace.subtypeL) c hc hF
    ((F.comp solenoidalSpace.subtypeL).adjoint (f-(2 : ℝ) • F₁ (v : L2)))

/-- Simultaneously translating all data gives the actual translated acceleration. -/
theorem acceleration_translation (a : Space) (F F₁ : L2 →L[ℝ] L2) (c : ℝ) (hc : 0 < c)
    (hF : ∀ v : solenoidalSpace, c*‖v‖^2 ≤ ‖(F.comp solenoidalSpace.subtypeL) v‖^2)
    (v : solenoidalSpace) (f : L2) :
    acceleration (translateOperator a F) (translateOperator a F₁) c hc
        (translated_lower a F c hF) (solenoidalTranslation a v) (translation a f) =
      solenoidalTranslation a (acceleration F F₁ c hc hF v f) := by
  have hr : translation a f-(2 : ℝ) • translateOperator a F₁ (solenoidalTranslation a v : L2) =
      translation a (f-(2 : ℝ) • F₁ (v : L2)) := by
    exact (congrArg (fun z : L2 => translation a f-(2 : ℝ) • z)
      (translateOperator_translation a F₁ (v : L2))).trans
        (((translation a).map_sub f ((2 : ℝ) • F₁ (v : L2))).trans
          (congrArg (fun z : L2 => translation a f-z) ((translation a).map_smul (2 : ℝ) _))).symm
  have hg := (congrArg ((translateOperator a F).comp solenoidalSpace.subtypeL).adjoint hr).trans
    (frameAdjoint_translation a F (f-(2 : ℝ) • F₁ (v : L2)))
  exact (congrArg (gramInverse ((translateOperator a F).comp solenoidalSpace.subtypeL)
      c hc (translated_lower a F c hF)) hg).trans
    (gramInverse_translation a F c hc hF ((F.comp solenoidalSpace.subtypeL).adjoint (f-(2 : ℝ) • F₁
        (v : L2))))

end EulerMeanPointwiseGramTranslation
