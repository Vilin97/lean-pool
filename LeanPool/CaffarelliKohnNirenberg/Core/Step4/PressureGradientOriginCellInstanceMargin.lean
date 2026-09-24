/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSmallCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedOriginClause

/-!
# The local pressure-gradient estimate on origin margin cells

At the scale `(1 - R₁) / 4`, cells meeting the origin carrier lie in a fixed
larger interior ball. The doubled source cylinder is admissible, and the
slice estimate in `eq:pressure-gradient-morrey` bounds the power integral of
one fixed measurable gradient, as used in `prop:bootstrap`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- A cell meeting the carrier at the origin margin scale lies in the
intermediate ball of radius `(1 + R₁) / 2`. -/
theorem origin_margin_cell_subset_intermediate_ball
    {R₁ r : ℝ} {x : Vec3}
    (hmargin : r ≤ (1 - R₁) / 4)
    (hmeet : (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁).Nonempty) :
    vec3Ball x r ⊆ vec3Ball (0 : Vec3) ((1 + R₁) / 2) := by
  have hx := vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty hmeet
  intro y hy
  have htri : vec3EuclideanNorm (y - 0) ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - 0) := by
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
    simpa only [dist_eq_norm] using
      dist_triangle (WithLp.toLp 2 y) (WithLp.toLp 2 x) (WithLp.toLp 2 (0 : Vec3))
  change vec3EuclideanNorm (y - x) < r at hy
  change vec3EuclideanNorm (y - 0) < (1 + R₁) / 2
  linarith only [htri, hx, hy, hmargin]

/-- Suitability and the actual slice estimate bound each margin-cell power
integral of a fixed measurable weak gradient by the explicit time majorant. -/
theorem origin_margin_cell_integral_le_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1)
    {Dp : ParabolicPoint → Vec3} (hmeas : Measurable Dp)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k)
        (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) k
        (fun y => p (y, s)) (fun y => Dp (y, s) k))
    {x : Vec3} {t r : ℝ} (hr : 0 < r) (hmargin : r ≤ (1 - R₁) / 4)
    (hmeet : (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁).Nonempty)
    (ht : t ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ)) (i : Fin 3) :
    cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) (x, t) r ≤
      ∫⁻ s in Ioc (t - r ^ 2) t,
        originSliceGradientMajorant u Du p f (x, t)
          (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ) := by
  have hdouble : 0 < 2 * r := by positivity
  have hsub : closure (parabolicCylinder x t (2 * r)) ⊆ spaceTimeSet Ω I := by
    apply closure_parabolicCylinder_double_subset_spaceTimeSet_of_origin_margin
      (R₀ := 1) (R₁ := R₁) hdom le_rfl
      (originMarginScale_triple_le hR₁unit hmargin)
      (vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty hmeet) ht.2
    have hsq := originMarginScale_double_sq_le hR₁ hr hmargin
    linarith only [ht.1, hsq]
  have htime : Ioc (t - r ^ 2) t ⊆ I := by
    intro s hs
    have hlow : t - (2 * r) ^ 2 < s := by nlinarith only [hs.1, sq_nonneg r]
    have hx : x ∈ vec3Ball x (2 * r) := by
      change vec3EuclideanNorm (x - x) < 2 * r
      simpa only [sub_self, vec3EuclideanNorm_zero] using hdouble
    exact (hsub (subset_closure (show (x, s) ∈ parabolicCylinder x t (2 * r) from ⟨hx, hlow,
      hs.2⟩))).2
  apply cylinderPowerIntegral_le_of_double_radius_slice_bounds hr
    (origin_margin_cell_subset_intermediate_ball hmargin hmeet)
    ((measurable_pi_apply i).comp hmeas).aemeasurable.restrict
    ((ae_restrict_of_ae_restrict_of_subset htime hfield).mono (fun _ hs => hs i))
  filter_upwards [origin_local_slice_gradient_bound_ae_of_sws
    (z := (x, t)) hsol hdouble hsub] with s hs
  obtain ⟨D, hloc, _, hweak, hbound⟩ := hs
  exact ⟨fun y => D y i, hloc i, hweak i, hbound i⟩

/-- One measurable field supplied from suitability obeys the explicit
slice-majorant bound on every origin margin cell meeting the carrier. -/
theorem origin_measurable_gradient_margin_bounds_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) k)
          (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) k
          (fun y => p (y, s)) (fun y => Dp (y, s) k)) ∧
      (∀ (x : Vec3) (t r : ℝ) (hr : 0 < r), r ≤ (1 - R₁) / 4 →
        (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁).Nonempty →
        t ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ) → ∀ i : Fin 3,
        cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) (x, t) r ≤
          ∫⁻ s in Ioc (t - r ^ 2) t,
            originSliceGradientMajorant u Du p f (x, t)
              (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ)) := by
  obtain ⟨Dp, hmeas, hfield⟩ := origin_measurable_weak_gradient_of_sws hsol hdom
    (show 0 < (1 + R₁) / 2 by linarith only [hR₁])
    (show (1 + R₁) / 2 < 1 by linarith only [hR₁unit])
  have hweak : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k)
        (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) ((1 + R₁) / 2)) k
        (fun y => p (y, s)) (fun y => Dp (y, s) k) :=
    hfield.mono (fun _ hs k => ⟨(hs k).1, (hs k).2.1⟩)
  refine ⟨Dp, hmeas, hweak, ?_⟩
  intro x t r hr hmargin hmeet ht i
  exact origin_margin_cell_integral_le_of_sws hsol hdom hR₁ hR₁unit
    hmeas hweak hr hmargin hmeet ht i

end CKN.Core.Step4
