/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousSpatialFamily
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation

@[expose] public section

/-!
# Actual forcing derivatives in the uniform time norm

Continuous paths of the literal ordinary spatial L² jets give genuine
smoothness of the forcing translation orbit in C(time,L²). The derivative
norm is bounded by the original uniform-time spatial jet norm, with no loss.
-/

noncomputable section

namespace EulerContinuousForcing

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpDerivative EulerContinuousSpatialFamily
open scoped ContDiff

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Ordinary translation applied to every value of an actual continuous L² path. -/
def translate (a : Space) (f : C(K,L2Space V)) : C(K,L2Space V) :=
  (EulerLpTranslation.translation a).toContinuousLinearMap.compLeftContinuous ℝ K f

omit [CompactSpace K] in
@[simp] theorem translate_apply (a : Space) (f : C(K,L2Space V)) (t : K) :
    translate a f t = EulerLpTranslation.translation a (f t) := rfl

variable (A : K → SmoothL2Field V)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (f : C(K,L2Space V)) (hf : ∀ t, f t = (A t).toLp)

/-- The original ordinary spatial jet, as a genuine continuous L² path. -/
def spatialJetPath (n : ℕ) : C(K,L2Space (Space [×n]→L[ℝ] V)) :=
  ⟨fun t => (A t).jetLp n, hA n⟩

/-- The actual translation jets form a continuous path because they are
bounded linear images of the original ordinary L² spatial jets. -/
def orbitJetPath (n : ℕ) (a : Space) : C(K,Space [×n]→L[ℝ] L2Space V) :=
  (multilinearBundling (P := Space) (V := V) volume n).compLeftContinuous ℝ K
    (translate a (spatialJetPath A hA n))

include hf in
omit [CompactSpace K] in
theorem orbitJetPath_eq (n : ℕ) (a : Space) (t : K) :
    orbitJetPath A hA n a t = iteratedFDeriv ℝ n (fun b : Space => translate b f t) a := by
  change multilinearBundling (P := Space) (V := V) volume n
      (EulerLpTranslation.translation a ((A t).jetLp n)) =
    iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b (f t)) a
  rw [hf t]
  exact ((A t).iteratedFDeriv_translation_eq n a).symm

/-- This package contains only actual pointwise spatial derivatives and their
original uniform-time L² bounds. -/
def forcingFamily : SpatialFamily K (L2Space V) where
  field a := translate a f
  smooth t := by
    change ContDiff ℝ ∞ (fun a : Space => EulerLpTranslation.translation a (f t))
    rw [hf t]
    exact (A t).translation_contDiff
  jet := orbitJetPath A hA
  jet_eq := orbitJetPath_eq A hA f hf
  bound n := ‖spatialJetPath A hA n‖
  bound_nonneg n := norm_nonneg _
  bounded n a t := by
    change ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b (f t)) a‖ ≤ _
    rw [hf t]
    exact ((A t).norm_iteratedFDeriv_translation_le n a).trans
      ((spatialJetPath A hA n).norm_coe_le_norm t)

include hA hf

/-- Literal smooth forcing slices with continuous spatial L² jets have a
genuinely smooth translation orbit in the uniform time norm. -/
theorem forcing_translation_contDiff : ContDiff ℝ ∞ (fun a : Space => translate a f) :=
  (forcingFamily A hA f hf).contDiff_field

/-- Every actual orbit derivative is controlled by the original uniform-time
ordinary L² spatial derivative with constant one. -/
theorem forcing_translation_jet_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translate b f) a‖ ≤ ‖spatialJetPath A hA n‖ :=
  (forcingFamily A hA f hf).norm_iteratedFDeriv_field_le n a

end EulerContinuousForcing
