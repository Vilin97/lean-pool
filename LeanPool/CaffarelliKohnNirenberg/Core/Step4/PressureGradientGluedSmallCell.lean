/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTwoRegimeMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellProducerSlice

/-!
# The small-cell regime: the slice estimate at twice the cell radius

The slice estimate of display `eq:pressure-gradient-morrey` produces, on a
backward cylinder of radius `ρ` whose closure lies in the space-time domain, a
weak spatial derivative of the pressure slice on the **half** ball of radius
`ρ / 2`.  To control a cell of radius `r` it must therefore be applied at
`ρ = 2 * r`, and this is possible exactly when the doubled cylinder still lies
in the region the hypotheses control.

That is the margin-safe regime.  For the origin carrier the controlled region is
the closed unit cylinder, so the governing condition is `r ≤ (1 - R₁) / 4`, with
a top time in the backward window of the cylinder of admissible centres; for the
symmetric carrier of the uniform route it is `3 * r ≤ R`.  A cell that misses the
carrier
contributes nothing, because the selected field vanishes there, so only cells
meeting the carrier have to be considered, and for those the margin condition is
what makes the doubled ball fit.

Cells above the margin scale are **not** reached by this argument; they belong to
the other regime and are bounded by the whole-carrier integral.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The explicit Euclidean ball of positive radius is the Euclidean norm ball.
The slice estimate states its carrier with the first, the parabolic geometry
with the second. -/
private theorem euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The slice estimate read at twice the cell radius gives the cell's own ball:
the carrier `euclideanBall x ((2 * r) / 2)` of the estimate is `vec3Ball x r`,
and the cell's time window is contained in the estimate's. -/
theorem ae_slice_bound_on_cell_ball_of_double_radius
    {p : ParabolicPoint → ℝ} {i : Fin 3} {x : Vec3} {t r : ℝ} {N : ℝ → ℝ≥0∞}
    (hr : 0 < r)
    (hslice : ∀ᵐ s ∂(volume.restrict (Ioc (t - (2 * r) ^ 2) t)),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
          (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N s) :
    ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x r) volume ∧
      HasWeakPartialDerivOn (vec3Ball x r) i (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r)) ≤ N s := by
  have hhalf : (2 * r) / 2 = r := by ring
  rw [hhalf, euclideanBall_eq_vec3Ball hr] at hslice
  have hwin : Ioc (t - r ^ 2) t ⊆ Ioc (t - (2 * r) ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (by nlinarith only [hr]) hs.1, hs.2⟩
  exact ae_restrict_of_ae_restrict_of_subset hwin hslice

/-- The cell power integral of the selected field at a margin-safe cell, from
the slice estimate applied at twice the cell radius.  The field is fixed first;
almost-everywhere uniqueness of weak partial derivatives transports the
estimate's bound to it, and Tonelli integrates the slice bounds over the cell's
window. -/
theorem cylinderPowerIntegral_le_of_double_radius_slice_bounds
    {B : Set Vec3} {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    {i : Fin 3} {x : Vec3} {t r : ℝ} {N : ℝ → ℝ≥0∞}
    (hr : 0 < r) (hball : vec3Ball x r ⊆ B)
    (hmeas : AEMeasurable (fun w => Dp w i)
      (volume.restrict (parabolicCylinder x t r)))
    (hfield : ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)),
      LocallyIntegrableOn (fun y => Dp (y, s) i) B volume ∧
        HasWeakPartialDerivOn B i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hslice : ∀ᵐ s ∂(volume.restrict (Ioc (t - (2 * r) ^ 2) t)),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
          (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N s) :
    cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) (x, t) r ≤
      ∫⁻ s in Ioc (t - r ^ 2) t, N s ^ (6 / 5 : ℝ) :=
  cylinderPowerIntegral_le_of_slice_eLpNorm (by norm_num) hmeas
    (ae_eLpNorm_slice_le_of_cell_scale_slice_bounds hball hfield
      (ae_slice_bound_on_cell_ball_of_double_radius hr hslice))

/-- The doubled cylinder of a margin-safe cell of the origin carrier is
admissible for the slice estimate, so the estimate applies at twice the cell
radius.  The margin is measured against the unit ball, which is the region the
domain hypothesis controls, so the scale `(1 - R₁) / 4` is bounded below by
`1/16` on the admissible range and does not degenerate. -/
theorem origin_margin_double_radius_slice
    {Ω : Set Vec3} {I : Set ℝ} {R₁ : ℝ} {p : ParabolicPoint → ℝ}
    {i : Fin 3} {x : Vec3} {t r : ℝ} {N : Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞}
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1)
    (hr : 0 < r) (hmargin : r ≤ (1 - R₁) / 4)
    (hx : vec3EuclideanNorm (x - 0) < R₁ + r)
    (ht : t ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ))
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N c t₀ ρ s) :
    ∀ᵐ s ∂(volume.restrict (Ioc (t - (2 * r) ^ 2) t)), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
      HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
        (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N x t (2 * r) s := by
  have htriple : 3 * r ≤ 1 - R₁ := by linarith only [hmargin, hR₁unit]
  have hrq : r < 1 / 4 := by linarith only [hmargin, hR₁]
  have hdouble : (2 * r) ^ 2 ≤ 1 / 4 := by nlinarith only [hr, hrq]
  refine hslice x t (2 * r) (by linarith only [hr]) ?_
  refine (closure_mono (parabolicCylinder_double_subset_unit_of_margin
    (R₀ := 1) (R₁ := R₁) le_rfl (by linarith only [htriple]) hx ht.2 ?_)).trans
    hdom
  linarith only [ht.1, hdouble]

/-- The doubled cylinder of a margin-safe cell of the symmetric carrier is
admissible for the slice estimate, so the estimate applies at twice the cell
radius. -/
theorem symmetric_margin_double_radius_slice
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {R : ℝ}
    {p : ParabolicPoint → ℝ} {i : Fin 3} {x : Vec3} {t r : ℝ}
    {N : Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞}
    (hdom : Metric.ball z₀ (2 * R) ⊆ CKN.spaceTimeSet Ω I)
    (hR : 0 < R) (hr : 0 < r) (hmargin : 3 * r ≤ R)
    (hmeet : (parabolicCylinder x t r ∩ Metric.ball z₀ (R / 2)).Nonempty)
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N c t₀ ρ s) :
    ∀ᵐ s ∂(volume.restrict (Ioc (t - (2 * r) ^ 2) t)), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
      HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
        (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N x t (2 * r) s := by
  obtain ⟨hx, hlow, hhigh⟩ := symmetric_margin_premises_of_meet hr hmeet
  exact hslice x t (2 * r) (by linarith only [hr])
    ((closure_parabolicCylinder_double_subset_metricBall_of_margin hR hr hmargin
      hx hlow hhigh).trans hdom)

/-- **The small-cell regime of the origin carrier.**  A cell that meets the
carrier ball, at a radius at most a quarter of the margin `1 - R₁` between the
carrier and the unit ball and with a top time in the backward window of the
cylinder of admissible centres, has its power integral bounded by the time
integral of the slice majorant taken at twice the cell radius. -/
theorem origin_margin_cylinderPowerIntegral_le
    {Ω : Set Vec3} {I : Set ℝ} {R₁ : ℝ} {Bf : Set Vec3} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {i : Fin 3} {x : Vec3} {t r : ℝ}
    {N : Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞}
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1)
    (hr : 0 < r) (hmargin : r ≤ (1 - R₁) / 4)
    (hmeet : (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁).Nonempty)
    (ht : t ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ))
    (hball : vec3Ball x r ⊆ Bf)
    (hmeas : AEMeasurable (fun w => Dp w i)
      (volume.restrict (parabolicCylinder x t r)))
    (hfield : ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)),
      LocallyIntegrableOn (fun y => Dp (y, s) i) Bf volume ∧
        HasWeakPartialDerivOn Bf i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N c t₀ ρ s) :
    cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) (x, t) r ≤
      ∫⁻ s in Ioc (t - r ^ 2) t, N x t (2 * r) s ^ (6 / 5 : ℝ) := by
  have hx : vec3EuclideanNorm (x - 0) < R₁ + r :=
    vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty hmeet
  exact cylinderPowerIntegral_le_of_double_radius_slice_bounds hr hball hmeas
    hfield (origin_margin_double_radius_slice hdom hR₁ hR₁unit hr hmargin hx ht
      hslice)

/-- **The small-cell regime of the symmetric carrier.**  A cell of radius at most
a third of `R` has the power integral of the field restricted to the inner ball
bounded by the time integral of the slice majorant taken at twice the cell
radius.  A cell disjoint from the inner ball carries no mass at all, so no
geometric hypothesis is needed for it. -/
theorem symmetric_margin_indicator_cylinderPowerIntegral_le
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {R : ℝ} {B : Set Vec3}
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    {z : ParabolicPoint} {r : ℝ} {N : Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞}
    (hdom : Metric.ball z₀ (2 * R) ⊆ CKN.spaceTimeSet Ω I)
    (hR : 0 < R) (hr : 0 < r) (hmargin : 3 * r ≤ R)
    (hball : vec3Ball z.1 r ⊆ B)
    (hmeas : AEMeasurable (fun w => Dp w i)
      (volume.restrict (parabolicCylinder z.1 z.2 r)))
    (hfield : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - r ^ 2) z.2)),
      LocallyIntegrableOn (fun y => Dp (y, s) i) B volume ∧
        HasWeakPartialDerivOn B i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N c t₀ ρ s) :
    cylinderPowerIntegral (6 / 5 : ℝ)
        ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r ≤
      ∫⁻ s in Ioc (z.2 - r ^ 2) z.2, N z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ) := by
  have hP : (0 : ℝ) < 6 / 5 := by norm_num
  by_cases hmeet : (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty
  · refine le_trans (cylinderPowerIntegral_indicator_le hP _ z r) ?_
    exact cylinderPowerIntegral_le_of_double_radius_slice_bounds hr hball hmeas
      hfield (symmetric_margin_double_radius_slice hdom hR hr hmargin hmeet
        hslice)
  · rw [cylinderPowerIntegral_indicator_eq_zero_of_disjoint hP
      (Set.not_nonempty_iff_eq_empty.mp hmeet)]
    exact bot_le


end CKN.Core.Step4
