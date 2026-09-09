/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation

@[expose] public section

/-!
Actual spatial reflection on ordinary R³ L².  Reflection preserves the
closed gradient and solenoidal spaces and commutes with the genuine Helmholtz
projection.  The scalar test is reflected with a minus sign so its gradient
has the same pullback as an ordinary vector field.
-/

noncomputable section

namespace EulerMeanSolenoidal

open MeasureTheory InnerProductSpace EulerSmoothLimit
open scoped ContDiff

theorem measurePreserving_reflection :
    MeasurePreserving (fun x : Space => -x) (volume : Measure Space) volume :=
  Measure.measurePreserving_neg volume

def reflection : L2 →ₗᵢ[ℝ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => -x) measurePreserving_reflection

theorem reflection_ae (u : L2) : reflection u =ᵐ[volume] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_reflection

@[simp] theorem reflection_involutive (u : L2) : reflection (reflection u) = u := by
  apply Lp.ext
  filter_upwards [reflection_ae (reflection u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (reflection_ae u)] with x hx hy
  rw [hx, hy, neg_neg]

theorem reflection_norm (u : L2) : ‖reflection u‖ = ‖u‖ := reflection.norm_map u

theorem reflection_inner_shift (u v : L2) : ⟪reflection u, v⟫_ℝ = ⟪u, reflection v⟫_ℝ := by
  calc
    _ = ⟪reflection u, reflection (reflection v)⟫_ℝ := by rw [reflection_involutive]
    _ = _ := reflection.inner_map_map u (reflection v)

/-- The two signs in the derivative of `-f(-x)` cancel. -/
theorem fderiv_neg_reflect {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : Differentiable ℝ f) (x : Space) :
    fderiv ℝ (fun y => -f (-y)) x = fderiv ℝ f (-x) := by
  have hd : HasFDerivAt f (fderiv ℝ f (-x)) ((-id) x) := (hf (-x)).hasFDerivAt
  have hh := (hd.comp x (hasFDerivAt_id (𝕜 := ℝ) x).neg).neg
  have he : -((fderiv ℝ f (-x)).comp (-(ContinuousLinearMap.id ℝ Space))) =
      fderiv ℝ f (-x) := by
    ext v
    simp
  rw [he] at hh
  exact hh.fderiv

theorem gradient_neg_reflect (φ : Space → ℝ) (hφ : Differentiable ℝ φ) (x : Space) :
    gradient (fun y => -φ (-y)) x = gradient φ (-x) := by
  simp only [gradient, fderiv_neg_reflect φ hφ]

theorem reflected_generator {g : L2} (hg : g ∈ gradientGenerators) :
    reflection g ∈ gradientGenerators := by
  obtain ⟨φ, hc, hs, hg⟩ := hg
  refine ⟨fun x => -φ (-x), (hc.comp_homeomorph (Homeomorph.neg Space)).neg,
    (hs.comp contDiff_id.neg).neg, ?_⟩
  filter_upwards [reflection_ae g,
    measurePreserving_reflection.quasiMeasurePreserving.ae hg] with x hx hy
  rw [hx, hy, gradient_neg_reflect φ (hs.differentiable (by simp))]

theorem reflection_gradient_mem {g : L2} (hg : g ∈ gradientSpace) :
    reflection g ∈ gradientSpace := by
  let ρ := reflection.toContinuousLinearMap
  have hspan : Submodule.span ℝ gradientGenerators ≤ gradientSpace.comap ρ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact (Submodule.span ℝ gradientGenerators).le_topologicalClosure
      (Submodule.subset_span (reflected_generator hf))
  exact (Submodule.span ℝ gradientGenerators).topologicalClosure_minimal hspan
    (gradientSpace_closed.preimage ρ.continuous) hg

theorem reflection_solenoidal_mem {u : L2} (hu : u ∈ solenoidalSpace) :
    reflection u ∈ solenoidalSpace := by
  intro g hg
  calc
    ⟪g, reflection u⟫_ℝ = ⟪reflection (reflection g), reflection u⟫_ℝ := by
      rw [reflection_involutive]
    _ = ⟪reflection g, u⟫_ℝ := reflection.inner_map_map _ _
    _ = 0 := hu _ (reflection_gradient_mem hg)

theorem solenoidalSpace_map_reflection :
    solenoidalSpace.map reflection.toLinearMap = solenoidalSpace := by
  apply le_antisymm
  · rintro u ⟨v, hv, rfl⟩
    exact reflection_solenoidal_mem hv
  · intro u hu
    exact ⟨reflection u, reflection_solenoidal_mem hu, reflection_involutive u⟩

/-- The actual ordinary Helmholtz projection commutes with reflection. -/
theorem solenoidalProjection_reflection (u : L2) :
    reflection (solenoidalProjection u) = solenoidalProjection (reflection u) := by
  have hmap := solenoidalSpace_map_reflection
  let : (solenoidalSpace.map reflection.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  simpa only [solenoidalProjection, hmap] using reflection.map_starProjection solenoidalSpace u

theorem reflection_translation (a : Space) (u : L2) :
    reflection (translation a u) = translation (-a) (reflection u) := by
  apply Lp.ext
  filter_upwards [reflection_ae (translation a u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (translation_ae a u),
    translation_ae (-a) (reflection u),
    (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae
      (reflection_ae u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  congr 1
  abel

end EulerMeanSolenoidal
