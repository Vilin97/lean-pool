/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LocalizedMaximal.Estimate
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.OneDimSecondDerivative.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# One-dimensional second-derivative controls
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The second-derivative measure has finite source mass bounded by twice the oscillation. -/
def HasOneDimSecondDerivativeSourceMassBound (μ : Measure ℝ) (osc : ℝ) : Prop :=
  μ sourceMaximalDomain < ⊤ ∧ μ.real sourceMaximalDomain ≤ 2 * osc

/-- Source endpoint estimate supplied by the one-dimensional convex second-derivative measure.

The variables are centered at an arbitrary `x ∈ (-1,1)` because coordinate slices in the cube
proof are centered at the coordinate `x i`, not necessarily at `0`. The later proof should obtain
this from the distributional derivative of the monotone one-sided derivative. -/
def HasOneDimSecondDerivativeEndpointControl
    (v : ℝ → ℝ) (μ : Measure ℝ) (ρ K : ℝ) : Prop :=
  ∀ ⦃x p t : ℝ⦄,
    x ∈ sourceMaximalWindow →
      SubgradientOn (Set.Ioo (-3 : ℝ) 3) v x p →
        ¬ sourceLocalizedMaximalBadPredicate μ x t →
          ∀ ⦃h : ℝ⦄, 0 < h → h < ρ →
            affineRemainder v x p (x + h) ≤ K * t * h ^ 2 ∧
              affineRemainder v x p (x - h) ≤ K * t * h ^ 2

/-- Symmetric interval-mass control of the one-dimensional affine remainder.

For the Stieltjes measure of a convex right derivative, this is the analytic integration step
still to be proved: the affine remainder at `x ± h` is bounded by `h` times the measure of the
symmetric interval `(x-h,x+h)`. -/
def HasOneDimSecondDerivativeSymmetricRemainderBound
    (v : ℝ → ℝ) (μ : Measure ℝ) (ρ : ℝ) : Prop :=
  ∀ ⦃x p h : ℝ⦄,
    x ∈ sourceMaximalWindow →
      SubgradientOn (Set.Ioo (-3 : ℝ) 3) v x p →
        0 < h →
          h < ρ →
            affineRemainder v x p (x + h) ≤
                h * μ.real (Set.Ioo (x - h) (x + h)) ∧
              affineRemainder v x p (x - h) ≤
                h * μ.real (Set.Ioo (x - h) (x + h))

/-- Open-interval derivative-gap control by a one-dimensional second-derivative measure.

For the clamped Stieltjes measure of the convex right derivative, this should follow from the
`Ioo` interval formula and the endpoint identities
`leftLim (rightDeriv v) (x+h) = leftDeriv v (x+h)` and
`rightLim (rightDeriv v) (x-h) = rightDeriv v (x-h)`. -/
def HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound
    (v : ℝ → ℝ) (μ : Measure ℝ) (ρ : ℝ) : Prop :=
  ∀ ⦃x h : ℝ⦄,
    x ∈ sourceMaximalWindow →
      0 < h →
        h < ρ →
          leftDeriv v (x + h) - rightDeriv v (x - h) ≤
            μ.real (Set.Ioo (x - h) (x + h))

/-- Convexity turns open-interval derivative-gap control into symmetric affine-remainder
control. -/
theorem HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound.symmetricRemainderBound_of_convex
    {v : ℝ → ℝ} {μ : Measure ℝ} {ρ : ℝ}
    (hgap : HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound v μ ρ)
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) (hρ_le_one : ρ ≤ 1) :
    HasOneDimSecondDerivativeSymmetricRemainderBound v μ ρ := by
  intro x p h hx hp hh_pos hhρ
  have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
  have hx_int : x ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show x ∈ Set.Ioo (-3 : ℝ) 3 by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith)
  have hxmh : x - h ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show x - h ∈ Set.Ioo (-3 : ℝ) 3 by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith)
  have hxph : x + h ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show x + h ∈ Set.Ioo (-3 : ℝ) 3 by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith)
  rcases hp.affineRemainder_pm_le_mul_leftDeriv_sub_rightDeriv
      hv hx_int hxmh hxph hh_pos.le with ⟨hright, hleft⟩
  have hgap' :
      leftDeriv v (x + h) - rightDeriv v (x - h) ≤
        μ.real (Set.Ioo (x - h) (x + h)) :=
    hgap hx hh_pos hhρ
  have hscaled :
      h * (leftDeriv v (x + h) - rightDeriv v (x - h)) ≤
        h * μ.real (Set.Ioo (x - h) (x + h)) :=
    mul_le_mul_of_nonneg_left hgap' hh_pos.le
  exact ⟨hright.trans hscaled, hleft.trans hscaled⟩

namespace HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound

/-- Endpoint comparisons for the source-local Stieltjes representative imply the open-interval
derivative-gap bound.

The remaining convex-analysis endpoint work is now isolated in the hypothesis `hendpoints`: inside
the source window, the left derivative at the right endpoint must be bounded by the left limit of
the Stieltjes representative, while the representative at the left endpoint must be bounded by the
right derivative there. -/
theorem of_sourceRightDerivStieltjes_endpointBounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)} {ρ : ℝ}
    (hendpoints :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              leftDeriv v (x + h) ≤
                  Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono)
                    (x + h) ∧
                sourceRightDerivStieltjesSecondDerivativeFunction v hmono (x - h) ≤
                  rightDeriv v (x - h)) :
    HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound v
      (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) ρ := by
  intro x h hx hh_pos hhρ
  rcases hendpoints hx hh_pos hhρ with ⟨hleft, hright⟩
  have hlt : x - h < x + h := by linarith
  rw [sourceRightDerivStieltjesSecondDerivativeMeasure_real_Ioo hmono hlt]
  linarith

end HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound

/-- Symmetric interval-mass control plus maximal non-badness gives the source endpoint-control
estimate, with the explicit constant `2`. -/
theorem HasOneDimSecondDerivativeSymmetricRemainderBound.endpointControl
    {v : ℝ → ℝ} {μ : Measure ℝ} {ρ : ℝ}
    (hrem : HasOneDimSecondDerivativeSymmetricRemainderBound v μ ρ)
    (hρ_le_one : ρ ≤ 1) :
    HasOneDimSecondDerivativeEndpointControl v μ ρ 2 := by
  intro x p t hx hp hnot h hh_pos hhρ
  rcases hrem hx hp hh_pos hhρ with ⟨hright, hleft⟩
  have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
  have hmass :
      μ.real (Set.Ioo (x - h) (x + h)) ≤ t * (2 * h) :=
    measureReal_Ioo_symm_le_two_mul_of_not_sourceLocalizedMaximalBadPredicate
      hnot hx hh_pos hh_one
  have hmass_scaled :
      h * μ.real (Set.Ioo (x - h) (x + h)) ≤ h * (t * (2 * h)) :=
    mul_le_mul_of_nonneg_left hmass hh_pos.le
  constructor
  · calc
      affineRemainder v x p (x + h)
          ≤ h * μ.real (Set.Ioo (x - h) (x + h)) := hright
      _ ≤ h * (t * (2 * h)) := hmass_scaled
      _ = 2 * t * h ^ 2 := by ring
  · calc
      affineRemainder v x p (x - h)
          ≤ h * μ.real (Set.Ioo (x - h) (x + h)) := hleft
      _ ≤ h * (t * (2 * h)) := hmass_scaled
      _ = 2 * t * h ^ 2 := by ring

/-- Source mass estimate specialized to the Stieltjes measure of a globally monotone right
derivative. This is a target interface: the source proof later supplies the estimate from
boundedness/oscillation of the underlying convex function on `(-3,3)`. -/
def HasRightDerivStieltjesSourceMassBound
    (v : ℝ → ℝ) (hmono : Monotone (rightDeriv v)) (osc : ℝ) : Prop :=
  HasOneDimSecondDerivativeSourceMassBound
    (rightDerivStieltjesSecondDerivativeMeasure v hmono) osc

/-- Source endpoint estimate specialized to the Stieltjes measure of a globally monotone right
derivative. -/
def HasRightDerivStieltjesEndpointControl
    (v : ℝ → ℝ) (hmono : Monotone (rightDeriv v)) (ρ K : ℝ) : Prop :=
  HasOneDimSecondDerivativeEndpointControl v
    (rightDerivStieltjesSecondDerivativeMeasure v hmono) ρ K

/-- Source mass estimate specialized to the clamped source-local right-derivative Stieltjes
measure. -/
def HasSourceRightDerivStieltjesSourceMassBound
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (osc : ℝ) : Prop :=
  HasOneDimSecondDerivativeSourceMassBound
    (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) osc

/-- A bound on the Stieltjes source jump gives the source mass estimate required by the
localized maximal argument. -/
theorem HasSourceRightDerivStieltjesSourceMassBound.of_sourceJump_le
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)} {osc : ℝ}
    (hjump : sourceRightDerivStieltjesSourceJump v hmono ≤ 2 * osc) :
    HasSourceRightDerivStieltjesSourceMassBound v hmono osc := by
  constructor
  · exact sourceRightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain_lt_top hmono
  · rwa [sourceRightDerivStieltjesSecondDerivativeMeasure_real_sourceMaximalDomain]

theorem HasSourceRightDerivStieltjesSourceMassBound.of_function_bounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {lower upper osc : ℝ}
    (hlower :
      lower ≤ sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ))
    (hupper :
      Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) ≤
        upper)
    (hwidth : upper - lower ≤ 2 * osc) :
    HasSourceRightDerivStieltjesSourceMassBound v hmono osc :=
  HasSourceRightDerivStieltjesSourceMassBound.of_sourceJump_le
    (sourceRightDerivStieltjesSourceJump_le_of_function_bounds hlower hupper hwidth)

theorem HasSourceRightDerivStieltjesSourceMassBound.of_abs_function_bound
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower :
      -osc ≤ sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ))
    (hupper :
      Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) ≤
        osc) :
    HasSourceRightDerivStieltjesSourceMassBound v hmono osc :=
  HasSourceRightDerivStieltjesSourceMassBound.of_sourceJump_le
    (sourceRightDerivStieltjesSourceJump_le_of_abs_function_bound hlower hupper)

theorem HasSourceRightDerivStieltjesSourceMassBound.of_rightDeriv_bounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower : -osc ≤ rightDeriv v (-2 : ℝ))
    (hupper : rightDeriv v (2 : ℝ) ≤ osc) :
    HasSourceRightDerivStieltjesSourceMassBound v hmono osc :=
  HasSourceRightDerivStieltjesSourceMassBound.of_sourceJump_le
    (sourceRightDerivStieltjesSourceJump_le_of_rightDeriv_bounds hlower hupper)

theorem HasSourceRightDerivStieltjesSourceMassBound.of_convex_secant_bounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v)
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        ∃ y : ℝ, y ∈ Set.Ioo (-3 : ℝ) (-2) ∧ -osc - ε ≤ slope v y (-2 : ℝ))
    (hright :
      ∀ ε : ℝ, 0 < ε →
        ∃ y : ℝ, y ∈ Set.Ioo (2 : ℝ) 3 ∧ slope v (2 : ℝ) y ≤ osc + ε) :
  HasSourceRightDerivStieltjesSourceMassBound v hmono osc :=
  HasSourceRightDerivStieltjesSourceMassBound.of_rightDeriv_bounds
    (ConvexOn.neg_osc_le_rightDeriv_neg_two_of_forall_exists_secant_add_le hv hleft)
    (ConvexOn.rightDeriv_two_le_of_forall_exists_secant_le_add hv hright)

theorem HasSourceRightDerivStieltjesSourceMassBound.of_convex_pairwise_sub_le
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) (hosc : 0 ≤ osc)
    (hbound :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Ioo (-3 : ℝ) 3 → y ∈ Set.Ioo (-3 : ℝ) 3 →
        v y - v x ≤ osc) :
  HasSourceRightDerivStieltjesSourceMassBound v hmono osc :=
  HasSourceRightDerivStieltjesSourceMassBound.of_convex_secant_bounds hv
    (fun _ hε => exists_neg_add_le_left_secant_neg_two_of_pairwise_sub_le hosc hε hbound)
    (fun _ hε => exists_right_secant_two_le_add_of_pairwise_sub_le hosc hε hbound)

/-- Source endpoint estimate specialized to the clamped source-local right-derivative Stieltjes
measure. -/
def HasSourceRightDerivStieltjesEndpointControl
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (ρ K : ℝ) : Prop :=
  HasOneDimSecondDerivativeEndpointControl v
    (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) ρ K

/-- Exact endpoint identities for the clamped source-local right-derivative Stieltjes
representative.

For a one-dimensional convex function, these should follow from right-continuity of the right
derivative and from identifying the left derivative with the left limit of the right derivative. -/
def HasSourceRightDerivStieltjesEndpointIdentities
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x h : ℝ⦄,
    x ∈ sourceMaximalWindow →
      0 < h →
        h < ρ →
          Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono)
              (x + h) =
              leftDeriv v (x + h) ∧
            sourceRightDerivStieltjesSecondDerivativeFunction v hmono (x - h) =
              rightDeriv v (x - h)

/-- Endpoint comparison hypothesis for the clamped source-local right-derivative Stieltjes
representative.

This is the remaining local convex-analysis input needed to identify the open-interval Stieltjes
mass with the derivative gap used by the affine-remainder estimate. -/
def HasSourceRightDerivStieltjesEndpointBounds
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x h : ℝ⦄,
    x ∈ sourceMaximalWindow →
      0 < h →
        h < ρ →
          leftDeriv v (x + h) ≤
              Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono)
                (x + h) ∧
            sourceRightDerivStieltjesSecondDerivativeFunction v hmono (x - h) ≤
              rightDeriv v (x - h)

/-- Exact endpoint identities imply the endpoint comparison bounds used by the Stieltjes
open-interval argument. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.endpointBounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hident : HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ) :
    HasSourceRightDerivStieltjesEndpointBounds v hmono ρ := by
  intro x h hx hh_pos hhρ
  rcases hident hx hh_pos hhρ with ⟨hleft, hright⟩
  exact ⟨hleft.ge, hright.le⟩

/-- A version of the endpoint-identity interface with the right endpoint written as
right-continuity of the clamped right-derivative extension. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.of_leftLim_eq_leftDeriv_of_extensionRightLim
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hleft :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono)
                  (x + h) =
                leftDeriv v (x + h))
    (hright :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Function.rightLim (sourceRightDerivExtension v) (x - h) =
                rightDeriv v (x - h)) :
    HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ := by
  intro x h hx hh_pos hhρ
  exact ⟨hleft hx hh_pos hhρ, by
    rw [sourceRightDerivStieltjesSecondDerivativeFunction_apply]
    exact hright hx hh_pos hhρ⟩

/-- A version of the endpoint-identity interface stated entirely in terms of the clamped
right-derivative extension before passing to its Stieltjes representative. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.of_extensionEndpointLimits
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hleft :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Function.leftLim (sourceRightDerivExtension v) (x + h) =
                leftDeriv v (x + h))
    (hright :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Function.rightLim (sourceRightDerivExtension v) (x - h) =
                rightDeriv v (x - h)) :
    HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ := by
  refine
    HasSourceRightDerivStieltjesEndpointIdentities.of_leftLim_eq_leftDeriv_of_extensionRightLim
      ?_ hright
  intro x h hx hh_pos hhρ
  rw [sourceRightDerivStieltjesSecondDerivativeFunction_leftLim_eq_extension_leftLim]
  exact hleft hx hh_pos hhρ

/-- Endpoint identities for the clamped Stieltjes representative follow from the ordinary
one-sided endpoint limits of the right derivative, once the endpoints are known to stay in the
source interval. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.of_rightDerivEndpointLimits
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1)
    (hleft :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Tendsto (rightDeriv v) (nhdsWithin (x + h) (Set.Iio (x + h)))
                (nhds (leftDeriv v (x + h))))
    (hright :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Tendsto (rightDeriv v) (nhdsWithin (x - h) (Set.Ioi (x - h)))
                (nhds (rightDeriv v (x - h)))) :
    HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ := by
  refine HasSourceRightDerivStieltjesEndpointIdentities.of_extensionEndpointLimits ?_ ?_
  · intro x h hx hh_pos hhρ
    have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
    have hxph_source : x + h ∈ sourceMaximalDomain := by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith
    exact sourceRightDerivExtension_leftLim_eq_of_tendsto_rightDeriv_nhdsLT
      hxph_source (hleft hx hh_pos hhρ)
  · intro x h hx hh_pos hhρ
    have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
    have hxmh_source : x - h ∈ sourceMaximalDomain := by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith
    exact sourceRightDerivExtension_rightLim_eq_of_tendsto_rightDeriv_nhdsGT
      hxmh_source (hright hx hh_pos hhρ)

/-- Source endpoint identities reduced to the remaining left-limit endpoint theorem for ordinary
right derivatives. The right-continuity endpoint is supplied by convexity. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.of_leftEndpointLimits_of_convex
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1)
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v)
    (hleft :
      ∀ ⦃x h : ℝ⦄,
        x ∈ sourceMaximalWindow →
          0 < h →
            h < ρ →
              Tendsto (rightDeriv v) (nhdsWithin (x + h) (Set.Iio (x + h)))
                (nhds (leftDeriv v (x + h)))) :
    HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ := by
  refine
    HasSourceRightDerivStieltjesEndpointIdentities.of_rightDerivEndpointLimits
      hρ_le_one hleft ?_
  intro x h hx hh_pos hhρ
  have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
  have hxmh_int : x - h ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show x - h ∈ Set.Ioo (-3 : ℝ) 3 by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith)
  exact AleksandrovDifferentiability.ConvexOn.tendsto_rightDeriv_nhdsGT
    (S := Set.Ioo (-3 : ℝ) 3) (f := v) (x := x - h) hv hxmh_int

/-- Convexity supplies both endpoint identities for the clamped source-local right-derivative
Stieltjes representative. -/
theorem HasSourceRightDerivStieltjesEndpointIdentities.of_convex
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1)
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) :
    HasSourceRightDerivStieltjesEndpointIdentities v hmono ρ := by
  refine
    HasSourceRightDerivStieltjesEndpointIdentities.of_leftEndpointLimits_of_convex
      hρ_le_one hv ?_
  intro x h hx hh_pos hhρ
  have hh_one : h < 1 := lt_of_lt_of_le hhρ hρ_le_one
  have hxph_int : x + h ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show x + h ∈ Set.Ioo (-3 : ℝ) 3 by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor <;> linarith)
  exact AleksandrovDifferentiability.ConvexOn.tendsto_rightDeriv_nhdsLT_leftDeriv
    (S := Set.Ioo (-3 : ℝ) 3) (f := v) (x := x + h) hv hxph_int

/-- The remaining analytic symmetric-remainder estimate for the clamped Stieltjes measure implies
the source endpoint-control estimate with constant `2`. -/
theorem HasSourceRightDerivStieltjesEndpointControl.of_symmetricRemainderBound
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hrem :
      HasOneDimSecondDerivativeSymmetricRemainderBound v
        (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) ρ)
    (hρ_le_one : ρ ≤ 1) :
    HasSourceRightDerivStieltjesEndpointControl v hmono ρ 2 :=
  hrem.endpointControl hρ_le_one

/-- The open-interval derivative-gap bound for the clamped Stieltjes measure, together with
convexity, gives source endpoint control with constant `2`. -/
theorem HasSourceRightDerivStieltjesEndpointControl.of_openIntervalDerivativeGapBound
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hgap :
      HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound v
        (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) ρ)
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) (hρ_le_one : ρ ≤ 1) :
    HasSourceRightDerivStieltjesEndpointControl v hmono ρ 2 :=
  HasSourceRightDerivStieltjesEndpointControl.of_symmetricRemainderBound
    (hgap.symmetricRemainderBound_of_convex hv hρ_le_one) hρ_le_one

/-- Endpoint comparisons for the clamped Stieltjes representative, together with convexity, give
source endpoint control with constant `2`. -/
theorem HasSourceRightDerivStieltjesEndpointControl.of_endpointBounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hendpoints : HasSourceRightDerivStieltjesEndpointBounds v hmono ρ)
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) (hρ_le_one : ρ ≤ 1) :
    HasSourceRightDerivStieltjesEndpointControl v hmono ρ 2 :=
  have hgap :
      HasOneDimSecondDerivativeOpenIntervalDerivativeGapBound v
        (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) ρ :=
    by
      intro x h hx hh_pos hhρ
      rcases hendpoints hx hh_pos hhρ with ⟨hleft, hright⟩
      have hlt : x - h < x + h := by linarith
      rw [sourceRightDerivStieltjesSecondDerivativeMeasure_real_Ioo hmono hlt]
      linarith
  HasSourceRightDerivStieltjesEndpointControl.of_openIntervalDerivativeGapBound
    hgap hv hρ_le_one

/-- Convexity supplies the source endpoint-control estimate for the clamped source-local
right-derivative Stieltjes measure, with constant `2`. -/
theorem HasSourceRightDerivStieltjesEndpointControl.of_convex
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) (hρ_le_one : ρ ≤ 1) :
    HasSourceRightDerivStieltjesEndpointControl v hmono ρ 2 :=
  HasSourceRightDerivStieltjesEndpointControl.of_endpointBounds
    (HasSourceRightDerivStieltjesEndpointIdentities.endpointBounds
      (HasSourceRightDerivStieltjesEndpointIdentities.of_convex hρ_le_one hv))
    hv hρ_le_one

/-- At a source non-bad point, the clamped Stieltjes measure of a symmetric short interval is
controlled by the maximal threshold. This is the measure input for the future
one-dimensional endpoint-control estimate. -/
theorem sourceRightDerivStieltjes_measureReal_Ioo_symm_le_two_mul_of_not_bad
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {x t h : ℝ}
    (hnot :
      ¬ sourceLocalizedMaximalBadPredicate
        (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) x t)
    (hx : x ∈ sourceMaximalWindow) (hh_pos : 0 < h) (hh : h < 1) :
    (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono).real
        (Set.Ioo (x - h) (x + h)) ≤
      t * (2 * h) :=
  measureReal_Ioo_symm_le_two_mul_of_not_sourceLocalizedMaximalBadPredicate
    hnot hx hh_pos hh

theorem HasRightDerivStieltjesSourceMassBound.sourceBadSet_measure_le
    {C osc : ℝ} {v : ℝ → ℝ} {hmono : Monotone (rightDeriv v)} {t : ℝ}
    (hmass : HasRightDerivStieltjesSourceMassBound v hmono osc)
    (hmax : LocalizedMaximalEstimateStatement C) (ht : 0 < t) :
    volume (sourceLocalizedMaximalBadSet
      (rightDerivStieltjesSecondDerivativeMeasure v hmono) t) ≤
        ENNReal.ofReal (2 * C * osc / t) :=
  hmax.sourceBadSet_measure_le_of_two_mul_osc ht hmass.1 hmass.2

theorem HasSourceRightDerivStieltjesSourceMassBound.sourceBadSet_measure_le
    {C osc : ℝ} {v : ℝ → ℝ}
    {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)} {t : ℝ}
    (hmass : HasSourceRightDerivStieltjesSourceMassBound v hmono osc)
    (hmax : LocalizedMaximalEstimateStatement C) (ht : 0 < t) :
    volume (sourceLocalizedMaximalBadSet
      (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono) t) ≤
        ENNReal.ofReal (2 * C * osc / t) :=
  hmax.sourceBadSet_measure_le_of_two_mul_osc ht hmass.1 hmass.2

/-- The source bad set estimate obtained by combining the localized maximal weak-type theorem
with the one-dimensional convex mass bound. -/
theorem HasOneDimSecondDerivativeSourceMassBound.sourceBadSet_measure_le
    {C osc : ℝ} {μ : Measure ℝ} {t : ℝ}
    (hmass : HasOneDimSecondDerivativeSourceMassBound μ osc)
    (hmax : LocalizedMaximalEstimateStatement C) (ht : 0 < t) :
    volume (sourceLocalizedMaximalBadSet μ t) ≤
      ENNReal.ofReal (2 * C * osc / t) :=
  hmax.sourceBadSet_measure_le_of_two_mul_osc ht hmass.1 hmass.2

end AleksandrovDifferentiability
