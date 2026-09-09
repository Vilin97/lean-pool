/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! Joint smoothness in the reference bounds spatial derivatives on every fixed
compact spatial set and closed finite time interval, including time zero. -/

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

theorem spatial_fderiv_eq_within (x : ℝ³) (t : ℝ) (ht : 0 ≤ t) :
    fderiv ℝ (v · t) x =
      (fderivWithin ℝ (Function.uncurry v) (univ ×ˢ Ici 0) (x, t)).comp
        (inl ℝ ℝ³ ℝ) := by
  have hd := (h.velocity_smooth.differentiableOn (by simp) (x, t)
    ⟨mem_univ x, ht⟩).hasFDerivWithinAt
  exact (hd.comp_hasFDerivAt (f := fun y : ℝ³ => (y, t)) x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    (Eventually.of_forall (fun y => ⟨mem_univ y, ht⟩))).fderiv

theorem spatial_fderiv_continuousOn :
    ContinuousOn (fun z : ℝ³ × ℝ => fderiv ℝ (v · z.2) z.1)
      (univ ×ˢ Ici 0) := by
  have hc := h.velocity_smooth.continuousOn_fderivWithin
    (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)) (by simp)
  apply (hc.clm_comp (continuousOn_const (c := inl ℝ ℝ³ ℝ))).congr
  intro z hz
  exact h.spatial_fderiv_eq_within z.1 z.2 hz.2

theorem spatial_fderiv_bounded_on_compact (K : Set ℝ³) (hK : IsCompact K)
    (T : ℝ) : ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (v · t) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (h.spatial_fderiv_continuousOn.mono
      (show K ×ˢ Icc (0 : ℝ) T ⊆ univ ×ˢ Ici 0 from
        fun _ hz => ⟨mem_univ _, hz.2.1⟩))
  exact ⟨C, fun x hx t ht => hC (x, t) ⟨hx, ht⟩⟩

end Euler.EulerExistenceAndSmoothnessR3
