/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSmallCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeasurable

/-!
# Doubled source cylinders for clipped origin cells

The pressure slice estimate on a cylinder of radius `2 * r` controls its
half-ball of radius `r`. Weak derivative uniqueness on the intersection with
the origin carrier transfers that bound to a field defined only on the
carrier ball. The resulting time integral uses the clipped cell window.
For centres in the closed origin cylinder, this construction is admissible
through radius `(1 - R₁) / 2`, twice the origin margin scale.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The doubled-radius slice bound transfers to a weak gradient on the carrier
ball by uniqueness on the intersection of the two spatial balls. -/
theorem originClause_slice_bound_of_double_radius
    {I : Set ℝ} {R₁ : ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {i : Fin 3} {x : Vec3} {t r : ℝ}
    {N : ℝ → ℝ≥0∞} (hr : 0 < r)
    (hwindow : Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0 ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
          (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N s) :
    ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0),
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball 0 R₁)) ≤ N s := by
  have hlocal := ae_slice_bound_on_cell_ball_of_double_radius hr hslice
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hwindow hfield,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hlocal] with s hf hs
  obtain ⟨g, hloc, hweak, hnorm⟩ := hs
  have hopen : IsOpen (vec3Ball x r ∩ vec3Ball 0 R₁) :=
    (isOpen_vec3Ball _ _).inter (isOpen_vec3Ball _ _)
  have heq := HasWeakPartialDerivOn.ae_eq hopen
    (hf.1.mono_set inter_subset_right) (hloc.mono_set inter_subset_left)
    (hf.2.restrict hopen inter_subset_right) (hweak.restrict hopen inter_subset_left)
  rw [eLpNorm_congr_ae heq]
  exact (eLpNorm_mono_measure g
    (Measure.restrict_mono_set volume inter_subset_left)).trans hnorm

/-- The carrier-cell integral consumer applied to the actual norm of the fixed
field, followed by its doubled-radius bound on the clipped time window. -/
theorem originClauseCarrierCellIntegral_le_of_double_radius
    {I : Set ℝ} {R₁ : ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {i : Fin 3} {x : Vec3} {t r : ℝ}
    {N : ℝ → ℝ≥0∞}
    (hR₁ : 0 ≤ R₁) (hR₁one : R₁ ≤ 1) (hI : Icc (-1 : ℝ) 0 ⊆ I)
    (hr : 0 < r)
    (hDmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall x ((2 * r) / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) i
          (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ N s) :
    (∫⁻ w in parabolicCylinder x t r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0, N s ^ (6 / 5 : ℝ) := by
  let M : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun y => Dp (y, s) i)
    (ENNReal.ofReal (6 / 5 : ℝ))
    (volume.restrict (vec3Ball x r ∩ vec3Ball 0 R₁))
  have hid : ∀ᵐ s ∂volume.restrict I, ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball 0 R₁) volume →
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i (fun y => p (y, s)) g →
      (fun y => Dp (y, s) i) =ᵐ[volume.restrict (vec3Ball 0 R₁)] g := by
    filter_upwards [hfield] with s hs g hg hw
    exact HasWeakPartialDerivOn.ae_eq (isOpen_vec3Ball _ _) hs.1 hg hs.2 hw
  have hnorm : ∀ᵐ s ∂volume.restrict I, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball 0 R₁)) ≤ M s := by
    filter_upwards [hfield] with s hs
    exact ⟨fun y => Dp (y, s) i, hs.1, hs.2, le_rfl⟩
  refine (originClauseCarrierCellIntegral_le_of_slice_bounds
    hR₁ hR₁one hI hDmeas hid hnorm).trans ?_
  apply lintegral_mono_ae
  have hb := originClause_slice_bound_of_double_radius hr
    (originClauseWindow_subset_of_unitTime hR₁ hR₁one hI t r) hfield hslice
  filter_upwards [hb] with s hs
  exact ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 6 / 5)

/-- Centres in the closed origin cylinder admit doubled source cylinders
through twice the margin scale, including the endpoint radius. -/
theorem originClause_doubleRadius_subset_unit
    {R₁ r : ℝ} {z : ParabolicPoint}
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1) (hr : 0 < r)
    (hmargin : r ≤ (1 - R₁) / 2)
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆
      closure (parabolicCylinder (0 : Vec3) 0 1) := by
  rw [closure_parabolicCylinder hR₁] at hz
  rw [closure_parabolicCylinder (by positivity : 0 < 2 * r),
    closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
  intro w hw
  change vec3EuclideanNorm (z.1 - 0) ≤ R₁ ∧ 0 - R₁ ^ 2 ≤ z.2 ∧ z.2 ≤ 0 at hz
  change vec3EuclideanNorm (w.1 - z.1) ≤ 2 * r ∧
    z.2 - (2 * r) ^ 2 ≤ w.2 ∧ w.2 ≤ z.2 at hw
  change vec3EuclideanNorm (w.1 - 0) ≤ 1 ∧ 0 - (1 : ℝ) ^ 2 ≤ w.2 ∧ w.2 ≤ 0
  have htri : vec3EuclideanNorm (w.1 - 0) ≤
      vec3EuclideanNorm (w.1 - z.1) + vec3EuclideanNorm (z.1 - 0) := by
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
    simpa only [dist_eq_norm] using
      dist_triangle (WithLp.toLp 2 w.1) (WithLp.toLp 2 z.1) (WithLp.toLp 2 (0 : Vec3))
  have hr2 : 2 * r ≤ 1 - R₁ := by linarith only [hmargin]
  have hsq : (2 * r) ^ 2 ≤ (1 - R₁) ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ 2 * r) (sub_pos.mpr hR₁one).le).mpr hr2
  have hproduct : 0 ≤ R₁ * (1 - R₁) := mul_nonneg hR₁.le (sub_pos.mpr hR₁one).le
  exact ⟨by linarith only [htri, hw.1, hz.1, hr2],
    by nlinarith only [hw.2.1, hz.2.1, hsq, hproduct], hw.2.2.trans hz.2.2⟩

/-- Suitability supplies the doubled-radius slice estimate for a clipped
origin cell, while the fixed derivative is required only on the carrier ball. -/
theorem originClauseCarrierCellIntegral_le_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hmargin : r ≤ 2 * ((1 - R₁) / 4))
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
        originSliceGradientMajorant u Du p f z
          (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ) := by
  have hsub := (originClause_doubleRadius_subset_unit hR₁ hR₁one hr
    (by linarith only [hmargin]) hz).trans hdom
  apply originClauseCarrierCellIntegral_le_of_double_radius hR₁.le hR₁one.le
    (OriginInstance.originUnitBall_subset_of_dom hdom).2 hr hDmeas hfield
  filter_upwards [origin_local_slice_gradient_bound_ae_of_sws
    hsol (show 0 < 2 * r by positivity) hsub] with s hs
  obtain ⟨D, hloc, _hmem, hweak, hbound⟩ := hs
  exact ⟨fun y => D y i, hloc i, hweak i, hbound i⟩

/-- One measurable carrier gradient, obtained from suitability, satisfies all
clipped cell estimates through twice the origin margin scale. -/
theorem originClause_exists_doubled_cell_bounds_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
      (∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ (r : ℝ) (hr : 0 < r), r ≤ 2 * ((1 - R₁) / 4) → ∀ i : Fin 3,
          (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
            ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
            ∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
              originSliceGradientMajorant u Du p f z
                (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ)) := by
  obtain ⟨Dp, hmeas, hweak⟩ :=
    origin_measurable_weak_gradient_of_sws hsol hdom hR₁ hR₁one
  have hfield : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i) :=
    hweak.mono (fun _ hs i => ⟨(hs i).1, (hs i).2.1⟩)
  refine ⟨Dp, hmeas, hfield, ?_⟩
  intro z hz r hr hmargin i
  exact originClauseCarrierCellIntegral_le_of_sws hsol hdom hR₁ hR₁one
    ((measurable_pi_apply i).comp hmeas).aemeasurable.restrict
    (hfield.mono (fun _ hs => hs i)) hr hmargin hz

end CKN.Core.Step4
