/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
import Mathlib.Analysis.Calculus.ContDiff.Comp

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
