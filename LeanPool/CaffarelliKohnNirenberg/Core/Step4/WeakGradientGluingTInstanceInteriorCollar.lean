/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTActualPressureIdentification

/-! # Interior collars for the origin pressure decomposition

The half-gap collar stays inside the outer data cylinder for every centre
in the closed inner carrier, so the actual pressure gradient admits the
raw-source decomposition on that collar.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean
noncomputable section
namespace CKN.Core.Step4

/-- The closed half-gap collar lies in the outer open-backward cylinder. -/
theorem half_gap_collar_closure_subset_outer
    {R₀ R₁ : ℝ} (hR₁ : 0 < R₁) (hgap : R₁ < R₀)
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    closure (parabolicCylinder z.1 z.2 ((R₀-R₁)/2)) ⊆
      parabolicCylinder (0 : Vec3) 0 R₀ := by
  have ha : 0 < (R₀-R₁)/2 := by linarith only [hgap]
  rw [closure_parabolicCylinder hR₁] at hz
  have hzx : vec3EuclideanNorm z.1 ≤ R₁ := by
    simpa only [Set.mem_ofPred_eq, sub_zero] using hz.1
  have htime : R₁^2 + ((R₀-R₁)/2)^2 < R₀^2 := by
    have hp := mul_pos (sub_pos.mpr hgap) hR₁
    nlinarith only [hp, sq_nonneg (R₀-R₁)]
  rw [closure_parabolicCylinder ha]
  intro w hw
  constructor
  · change vec3EuclideanNorm (w.1-0) < R₀
    have ht : vec3EuclideanNorm w.1 ≤ vec3EuclideanNorm (w.1-z.1) + vec3EuclideanNorm z.1 := by
      calc
        _ = vec3EuclideanNorm ((w.1-z.1)+z.1) := by rw [sub_add_cancel]
        _ ≤ _ := vec3EuclideanNorm_add_le _ _
    have hx : vec3EuclideanNorm (w.1-z.1) ≤ (R₀-R₁)/2 := hw.1
    rw [sub_zero]
    linarith only [ht,hx,hzx,hgap]
  · constructor
    · have hzt : 0-R₁^2 ≤ z.2 := hz.2.1
      have hwt : z.2-((R₀-R₁)/2)^2 ≤ w.2 := hw.2.1
      linarith only [hzt,hwt,htime]
    · exact hw.2.2.trans hz.2.2

/-- The spatial half-gap ball stays inside the outer data ball. -/
theorem half_gap_ball_subset_outer
    {R₀ R₁ : ℝ} (hR₁ : 0 < R₁) (hgap : R₁ < R₀)
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    vec3Ball z.1 ((R₀-R₁)/2) ⊆ vec3Ball (0 : Vec3) R₀ := by
  intro x hx
  have ha : 0 < (R₀-R₁)/2 := by linarith only [hgap]
  have hw : ((x,z.2) : ParabolicPoint) ∈ parabolicCylinder z.1 z.2 ((R₀-R₁)/2) :=
    ⟨hx, by constructor <;> nlinarith only [sq_pos_of_pos ha]⟩
  exact (half_gap_collar_closure_subset_outer hR₁ hgap hz (subset_closure hw)).1

/-- The actual pressure gradient has the raw-source decomposition using the interior half-gap
  collar. -/
theorem ae_actual_pressure_eq_raw_riesz_half_gap_collar
    (R₀ R₁ : ℝ) (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀one : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (T : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hT : ∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun w => (∑ k, Du w j k * u w k) - f w j) (y,s)))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hcell : r ≤ (R₀-R₁)/4)
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), ∀ i : Fin 3,
      (fun y => Dp (y,s) i) =ᵐ[volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)]
      fun x => -(∑ j, T j i (x,s)) + rawCorrectedPressureRemainder R₀ z (show 0 < (R₀-R₁)/2 by
        linarith only [hgap]) u Du p f i (x,s) := by
  have ha : 0 < (R₀-R₁)/2 := by linarith only [hgap]
  have hsub : closure (parabolicCylinder z.1 z.2 ((R₀-R₁)/2)) ⊆ spaceTimeSet Ω I :=
    (half_gap_collar_closure_subset_outer hR₁ hgap hz).trans
      ((subset_closure.trans (closure_mono (parabolicCylinder_mono
        (hR₁.trans hgap).le hR₀one))).trans hdom)
  have hid := ae_actual_pressure_eq_raw_riesz_corrected_on_clipped_cell
    R₀ R₁ hR₁ hgap.le hR₀one hsol hdom hDp T hT ha hsub
  have hrhalf : r ≤ ((R₀-R₁)/2)/2 := by linarith only [hcell]
  have htime : Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0 ⊆
      Ioc (z.2-(((R₀-R₁)/2)/2)^2) z.2 ∩ Ioc (-(R₁^2)) 0 := by
    intro s hs
    exact ⟨⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hrhalf 2) _) hs.1.1,
      hs.1.2⟩, hs.2⟩
  have hspace : vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁ ⊆
      vec3Ball z.1 (((R₀-R₁)/2)/2) ∩ vec3Ball (0 : Vec3) R₁ := by
    intro x hx
    exact ⟨lt_of_lt_of_le hx.1 hrhalf,hx.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hid] with s hs
  exact fun i => ae_restrict_of_ae_restrict_of_subset hspace (hs i)

end CKN.Core.Step4
