/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderRegularity
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient

@[expose] public section

/-!
# The actual scalar pressure source on cylinder L²

The normal functional is constructed from the positive one-column Gram
matrix. Applying it to f−2MA gives a genuine scalar L² path, with the literal
normal residual as representative and genuine smooth mixed translation orbit.
-/

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
    EulerLpCylinderRectangular
  EulerSourceNormalCoefficient
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported period Space S hS)) (a₀ : Supported period U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)

/-- A genuine supported scalar path representing the right side of ∂θπ in (11). -/
def pressureSource : C(Icc (0 : ℝ) T,Supported period ℝ S hS) :=
  supportedMultiplierMap period S hS (normalFunctional m cm hcm hm)
    (f - (2 : ℝ) • supportedMultiplierMap period S hS M.field
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀))

/-- The pressure source is precisely the manuscript's scalar quotient. -/
theorem pressureSource_ae (t : Icc (0 : ℝ) T) :
    (pressureSource period S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 period ℝ)
      =ᵐ[liftMeasure period]
      fun x => (⟪m.field t x.1,(f t : CylinderL2 period Space) x⟫_ℝ -
        2*⟪m.field t x.1,M.field t x.1
          ((velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space) x)⟫_ℝ) /
            ‖m.field t x.1‖^2 := by
  let v := velocity period S hS T hT Q Q₁ c hc hQ f a₀ t
  let w := supportedOperatorMap period S hS (M.field t) v
  let r : Supported period Space S hS := f t - (2 : ℝ) • w
  let N := normalFunctional m cm hcm hm t
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period N) (r :
    CylinderL2 period Space),
    EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (M.field t)) (v :
      CylinderL2 period Space),
    Lp.coeFn_sub (f t : CylinderL2 period Space) ((2 : ℝ) • (w : CylinderL2 period Space)),
    Lp.coeFn_smul (2 : ℝ) (w : CylinderL2 period Space)] with x hn hM hr hs
  change (EulerLpOperatorField.full (liftMeasure period) (fieldLift period N) (r : CylinderL2
    period Space)) x = _
  rw [hn]
  change normalFunctional m cm hcm hm t x.1 ((r : CylinderL2 period Space) x) = _
  rw [normalFunctional_apply]
  change (⟪m.field t x.1,((f t : CylinderL2 period Space) - (2 : ℝ) • (w : CylinderL2 period
    Space)) x⟫_ℝ) / _ = _
  rw [hr]
  simp only [Pi.sub_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  change (⟪m.field t x.1,(f t : CylinderL2 period Space) x - (2 : ℝ) •
    (EulerLpOperatorField.full (liftMeasure period) (fieldLift period (M.field t)) (v : CylinderL2
      period Space)) x⟫_ℝ) / _ = _
  rw [hM,inner_sub_right,inner_smul_right]
  rfl

/-- The actual scalar pressure source inherits genuine mixed regularity from the solve. -/
theorem pressureSource_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (pressureSource period S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm))) := by
  let v := velocity period S hS T hT Q Q₁ c hc hQ f a₀
  let w := supportedMultiplierMap period S hS M.field v
  have hv := velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have hw := supported_product_orbit_contDiff period M.field M.translation_contDiff S hS v hv
  have hr : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (f - (2 : ℝ) • w))) := by
    simpa only [map_sub,map_smul] using hf.sub (hw.const_smul (2 : ℝ))
  exact supported_product_orbit_contDiff period (normalFunctional m cm hcm hm)
    (normalFunctional_translation_contDiff m cm hcm hm) S hS (f - (2 : ℝ) • w) hr

end EulerSourceCylinderEquation
