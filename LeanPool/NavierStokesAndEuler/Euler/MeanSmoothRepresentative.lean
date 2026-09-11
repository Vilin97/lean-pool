/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Genuine smooth ordinary-space representatives reconstructed from smooth L² translation orbits.
-/

section

/-! An isometric embedding of ordinary R³ L² into the angle-independent part of the unit cylinder.
-/

@[expose] public section

noncomputable section

namespace EulerMeanOrdinaryLift

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerLiftedGradientSpace
  EulerMetricTransport
open scoped ContDiff

local instance instMeanOrdinaryLift1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance instMeanOrdinaryLift2 : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ)))
    := by
  constructor
  simp only [AddCircle.measure_univ, ENNReal.ofReal_one]

theorem ordinaryProjection_measurePreserving :
    MeasurePreserving (Prod.fst : LiftDomain 1 → Space) (liftMeasure 1) volume :=
  measurePreserving_fst

/-- The added angle has mass one, so this is a genuine L² isometry. -/
def ordinaryLift : EulerMeanSolenoidal.L2 →ₗᵢ[ℝ] LiftL2 1 :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst ordinaryProjection_measurePreserving

theorem ordinaryLift_ae (u : EulerMeanSolenoidal.L2) :
    ordinaryLift u =ᵐ[liftMeasure 1] fun x : LiftDomain 1 => u x.1 :=
  Lp.coeFn_compMeasurePreserving u ordinaryProjection_measurePreserving

/-- Every cylinder translation acts through its actual spatial component on this embedding. -/
theorem ordinaryLift_translation (a : LiftDomain 1) (u : EulerMeanSolenoidal.L2) :
    EulerLiftedGradientSpace.translation 1 a (ordinaryLift u) =
      ordinaryLift (EulerMeanSolenoidal.translation a.1 u) := by
  apply Lp.ext
  filter_upwards [EulerLiftedGradientSpace.translation_ae 1 a (ordinaryLift u),
    (measurePreserving_translation 1 a).quasiMeasurePreserving.ae (ordinaryLift_ae u),
    ordinaryLift_ae (EulerMeanSolenoidal.translation a.1 u),
    ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae
      (EulerMeanSolenoidal.translation_ae a.1 u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  rfl

/-- A smooth cylinder field restricts to a smooth ordinary field at every fixed angle. -/
theorem smooth_angle_slice (g : LiftDomain 1 → Space)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 g x)) (θ : AddCircle (1 : ℝ)) :
    ContDiff ℝ ∞ (fun x : Space => g (x, θ)) := by
  have hi : ContDiff ℝ ∞ (fun x : Space => (x, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  simpa [Function.comp_def, localFieldLift] using (hg (0, θ)).comp hi

/-- Fubini selects a genuine spatial representative from a smooth representative of the lift. -/
theorem exists_smooth_of_lift (u : EulerMeanSolenoidal.L2) (g : LiftDomain 1 → Space)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 g x))
    (hrep : (ordinaryLift u : LiftDomain 1 → Space) =ᵐ[liftMeasure 1] g) :
    ∃ f : Space → Space, ContDiff ℝ ∞ f ∧ (u : Space → Space) =ᵐ[volume] f := by
  have heq : (fun x : LiftDomain 1 => u x.1) =ᵐ[liftMeasure 1] g :=
    (ordinaryLift_ae u).symm.trans hrep
  have hswap : ∀ᵐ z : AddCircle (1 : ℝ) × Space
      ∂(volume : Measure (AddCircle (1 : ℝ))).prod (volume : Measure Space),
      u z.2 = g (z.2, z.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq
  have hsections : ∀ᵐ θ : AddCircle (1 : ℝ) ∂volume,
      (u : Space → Space) =ᵐ[volume] fun x => g (x, θ) :=
    Measure.ae_ae_of_ae_prod hswap
  obtain ⟨θ, hθ⟩ := hsections.exists
  exact ⟨fun x => g (x, θ), smooth_angle_slice g hg θ, hθ⟩

end EulerMeanOrdinaryLift

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerPressureSpatialRegularity
open scoped ContDiff

local instance instMeanSmoothRepresentative1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Smoothness is required only of the actual ordinary L² translation orbit. -/
abbrev SmoothOrbit (u : EulerMeanSolenoidal.L2) : Prop :=
  ContDiff ℝ ∞ (fun a : Space => EulerMeanSolenoidal.translation a u)

/-- Orbit derivative, given by `fderiv ℝ (fun a : Space => EulerMeanSolenoidal.translation a u)
0 v`. -/
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

/-- The cylinder jet uses the actual spatial derivative, with zero angular derivative automatically.
-/
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
