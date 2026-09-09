/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace

@[expose] public section

/-!
# Translation invariance of the ordinary solenoidal projection

The nonoscillating inverse uses spatial difference quotients. These act on the
actual R³ L² space, preserve its weak divergence constraint, and commute with
the orthogonal solenoidal projection.
-/

noncomputable section

namespace EulerMeanSolenoidal

open MeasureTheory InnerProductSpace EulerSmoothLimit
open scoped ContDiff

def translation (a : Space) : L2 →ₗᵢ[ℝ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => x + a)
    (measurePreserving_add_right (volume : Measure Space) a)

theorem translation_ae (a : Space) (u : L2) :
    translation a u =ᵐ[volume] fun x => u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

theorem translation_add (a b : Space) (u : L2) :
    translation a (translation b u) = translation (a + b) u := by
  apply Lp.ext
  filter_upwards [translation_ae a (translation b u),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (translation_ae b u), translation_ae (a + b) u] with x hx hy hz
  rw [hx, hy, hz, add_assoc]

@[simp] theorem translation_zero (u : L2) : translation 0 u = u := by
  apply Lp.ext
  filter_upwards [translation_ae 0 u] with x hx
  simpa only [add_zero] using hx

theorem gradient_translated (a : Space) (φ : Space → ℝ) (x : Space) :
    gradient (fun y => φ (y + a)) x = gradient φ (x + a) := by
  simp only [gradient, fderiv_comp_add_right]

theorem translated_generator (a : Space) {g : L2} (hg : g ∈ gradientGenerators) :
    translation a g ∈ gradientGenerators := by
  obtain ⟨φ, hc, hs, hg⟩ := hg
  refine ⟨fun x => φ (x + a), hc.comp_homeomorph (Homeomorph.addRight a),
    hs.comp (contDiff_id.add contDiff_const), ?_⟩
  filter_upwards [translation_ae a g,
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae hg]
    with x hx hy
  rw [hx, hy, gradient_translated]

theorem translation_gradient_mem (a : Space) {g : L2} (hg : g ∈ gradientSpace) :
    translation a g ∈ gradientSpace := by
  let τ := (translation a).toContinuousLinearMap
  have hspan : Submodule.span ℝ gradientGenerators ≤ gradientSpace.comap τ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact (Submodule.span ℝ gradientGenerators).le_topologicalClosure
      (Submodule.subset_span (translated_generator a hf))
  exact (Submodule.span ℝ gradientGenerators).topologicalClosure_minimal hspan
    (gradientSpace_closed.preimage τ.continuous) hg

theorem translation_solenoidal_mem (a : Space) {u : L2} (hu : u ∈ solenoidalSpace) :
    translation a u ∈ solenoidalSpace := by
  intro g hg
  calc
    ⟪g, translation a u⟫_ℝ =
        ⟪translation a (translation (-a) g), translation a u⟫_ℝ := by
      rw [translation_add, add_neg_cancel, translation_zero]
    _ = ⟪translation (-a) g, u⟫_ℝ := (translation a).inner_map_map _ _
    _ = 0 := hu _ (translation_gradient_mem (-a) hg)

theorem solenoidalSpace_map_translation (a : Space) :
    solenoidalSpace.map (translation a).toLinearMap = solenoidalSpace := by
  apply le_antisymm
  · rintro u ⟨v, hv, rfl⟩
    exact translation_solenoidal_mem a hv
  · intro u hu
    refine ⟨translation (-a) u, translation_solenoidal_mem (-a) hu, ?_⟩
    change translation a (translation (-a) u) = u
    rw [translation_add, add_neg_cancel, translation_zero]

/-- Ordinary Helmholtz projection commutes with every spatial translation. -/
theorem solenoidalProjection_translation (a : Space) (u : L2) :
    translation a (solenoidalProjection u) = solenoidalProjection (translation a u) := by
  have hmap := solenoidalSpace_map_translation a
  let : (solenoidalSpace.map (translation a).toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  simpa only [solenoidalProjection, hmap] using
    (translation a).map_starProjection solenoidalSpace u

end EulerMeanSolenoidal
