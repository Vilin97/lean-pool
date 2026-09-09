/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-! Time translation preserves the independent whole-space Euler class,
including its one-sided initial-time equation and uniform energy bound. -/

noncomputable section


open Set MeasureTheory
open scoped ContDiff

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}

theorem shiftTime (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (a : ℝ) (ha : 0 ≤ a) :
    EulerExistenceAndSmoothnessR3 (v · a)
      (fun x t => v x (a + t)) (fun x t => p x (a + t)) := by
  have hv (x : ℝ³) : ContDiffOn ℝ ∞ (v x ·) (Ici 0) :=
    h.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun r hr => ⟨mem_univ x, hr⟩)
  refine {
    euler := ?_
    div_free := fun x t ht => h.div_free x (a + t) (add_nonneg ha ht)
    initial_condition := fun x => by simp
    velocity_smooth := ?_
    pressure_smooth := ?_
    integrable := fun t ht => h.integrable (a + t) (add_nonneg ha ht)
    globally_bounded_energy := ?_ }
  · intro x t ht
    have hd := ((hv x).differentiableOn (by simp) (a + t)
      (add_nonneg ha ht)).hasDerivWithinAt
    have hi : HasDerivWithinAt (fun r : ℝ => a + r) 1 (Ici 0) t := by
      simpa only [zero_add, id_eq] using ((hasDerivAt_id t).const_add a).hasDerivWithinAt
    have hc := hd.scomp t hi (fun r hr => add_nonneg ha hr)
    have he : derivWithin (fun r => v x (a + r)) (Ici 0) t =
        derivWithin (v x ·) (Ici 0) (a + t) := by
      simpa only [Function.comp_def, one_smul] using
        hc.derivWithin (uniqueDiffOn_Ici 0 t ht)
    rw [he]
    exact h.euler x (a + t) (add_nonneg ha ht)
  · exact h.velocity_smooth.comp
      (contDiff_fst.prodMk (contDiff_const.add contDiff_snd)).contDiffOn
      (fun z hz => ⟨mem_univ z.1, add_nonneg ha hz.2⟩)
  · exact h.pressure_smooth.comp
      (contDiff_fst.prodMk (contDiff_const.add contDiff_snd)).contDiffOn
      (fun z hz => ⟨mem_univ z.1, add_nonneg ha hz.2⟩)
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    exact ⟨E, fun t ht => hE (a + t) (add_nonneg ha ht)⟩

end Euler.EulerExistenceAndSmoothnessR3
