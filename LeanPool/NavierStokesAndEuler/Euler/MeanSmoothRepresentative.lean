/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOrdinaryLift
public import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus

@[expose] public section

/-! Genuine smooth ordinary-space representatives reconstructed from smooth L² translation orbits.
  -/

noncomputable section


namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerPressureSpatialRegularity
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Smoothness is required only of the actual ordinary L² translation orbit. -/
abbrev SmoothOrbit (u : EulerMeanSolenoidal.L2) : Prop :=
  ContDiff ℝ ∞ (fun a : Space => EulerMeanSolenoidal.translation a u)

def orbitDerivative (u : EulerMeanSolenoidal.L2) (v : Space) : EulerMeanSolenoidal.L2 :=
  fderiv ℝ (fun a : Space => EulerMeanSolenoidal.translation a u) 0 v

/-- An orbit derivative is itself an actual translated field, at every base point. -/
theorem orbitDerivative_translation (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u)
    (v a : Space) :
    EulerMeanSolenoidal.translation a (orbitDerivative u v) =
      fderiv ℝ (fun b : Space => EulerMeanSolenoidal.translation b u) a v := by
  have H := EulerIsometricAction.hasFDerivAt_all EulerMeanSolenoidal.translation
    EulerMeanSolenoidal.translation_add u
    (fderiv ℝ (fun b : Space => EulerMeanSolenoidal.translation b u) 0)
    ((hu.differentiable (by simp) (0 : Space)).hasFDerivAt) a
  exact (congrArg (fun D : Space →L[ℝ] EulerMeanSolenoidal.L2 => D v) H.fderiv).symm

theorem orbitDerivative_smooth (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v : Space) :
    SmoothOrbit (orbitDerivative u v) := by
  have heq : (fun a : Space => EulerMeanSolenoidal.translation a (orbitDerivative u v)) =
      fun a : Space => fderiv ℝ (fun b : Space => EulerMeanSolenoidal.translation b u) a v :=
    funext fun a => orbitDerivative_translation u hu v a
  change ContDiff ℝ ∞ _
  rw [heq]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem orbitDerivative_hasDerivAt (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v : Space) :
    HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • v) u) (orbitDerivative u v) 0 :=
      by
  have H := (hu.differentiable (by simp) (0 : Space)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  simpa only [Function.comp_def, orbitDerivative] using H.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)

/-- The cylinder jet uses the actual spatial derivative, with zero angular derivative automatically. -/
theorem ordinaryLift_hasDerivAt (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (a : LiftTangent)
  :
    HasDerivAt
      (fun t : ℝ => EulerLiftedGradientSpace.translation 1 (translationPath 1 a t) (ordinaryLift u))
      (ordinaryLift (orbitDerivative u a.1)) 0 := by
  have H := ordinaryLift.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (orbitDerivative_hasDerivAt u hu a.1)
  have heq :
      (fun t : ℝ => EulerLiftedGradientSpace.translation 1 (translationPath 1 a t) (ordinaryLift
        u)) =
      fun t : ℝ => ordinaryLift (EulerMeanSolenoidal.translation (t • a.1) u) := by
    funext t
    exact ordinaryLift_translation (translationPath 1 a t) u
  rw [heq]
  exact H

/-- Every finite cylinder derivative tree is constructed from genuine ordinary L² derivatives. -/
def ordinarySpatialJet (s : ℕ) (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    SpatialJet 1 standardDirection s (ordinaryLift u) :=
  match s with
  | 0 => .zero (ordinaryLift u)
  | n+1 => .succ
      (fun i => ordinaryLift (orbitDerivative u (standardDirection i).1))
      (fun i => ordinarySpatialJet n (orbitDerivative u (standardDirection i).1)
        (orbitDerivative_smooth u hu (standardDirection i).1))
      (fun i => ordinaryLift_hasDerivAt u hu (standardDirection i))

/-- A smooth genuine L² translation orbit has a genuine C∞ representative on ordinary R³. -/
theorem exists_smooth_representative (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    ∃ f : Space → Space, ContDiff ℝ ∞ f ∧ (u : Space → Space) =ᵐ[volume] f := by
  obtain ⟨g, hg, hrep⟩ := EulerSmoothPressureRepresentative.exists_smooth_representative
    1 (ordinaryLift u) (fun s => ordinarySpatialJet s u hu)
  exact exists_smooth_of_lift u g hg hrep

/-- The reconstructed representative is independent of all choices, by continuous uniqueness. -/
def representative (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) : Space → Space :=
  Classical.choose (exists_smooth_representative u hu)

theorem representative_smooth (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    ContDiff ℝ ∞ (representative u hu) :=
  (Classical.choose_spec (exists_smooth_representative u hu)).1

theorem representative_ae (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    (u : Space → Space) =ᵐ[volume] representative u hu :=
  (Classical.choose_spec (exists_smooth_representative u hu)).2

theorem representative_unique (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : Continuous f) (hrep : (u : Space → Space) =ᵐ[volume] f) :
    representative u hu = f :=
  Measure.eq_of_ae_eq ((representative_ae u hu).symm.trans hrep)
    (representative_smooth u hu).continuous hf

end EulerMeanSmoothRepresentative
