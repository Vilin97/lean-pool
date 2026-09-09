/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Ordinary spatial smoothness, finite energy, and the pointwise time equation
follow from the independent Comparator solution class. -/

@[expose] public section


noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

theorem velocity_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (v · t) := by
  exact h.velocity_smooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
    (fun x => ⟨mem_univ x, ht⟩)

theorem pressure_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (p · t) := by
  exact h.pressure_smooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
    (fun x => ⟨mem_univ x, ht⟩)

theorem velocity_memLp (t : ℝ) (ht : 0 ≤ t) : MemLp (v · t) 2 volume := by
  exact (memLp_norm_iff (h.velocity_contDiff t ht).continuous.aestronglyMeasurable).mp
    (h.integrable t ht)

theorem pointwise_euler (x : ℝ³) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (v x ·)
      (-fderiv ℝ (v · t) x (v x t) - gradient (p · t) x) t := by
  have hs : ContDiffOn ℝ ∞ (v x ·) (Ici 0) :=
    h.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun r hr => ⟨mem_univ x, hr⟩)
  have hd : DifferentiableAt ℝ (v x ·) t :=
    (hs.differentiableOn (by simp) t ht.le).differentiableAt (Ici_mem_nhds ht)
  have he := h.euler x t ht.le
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he
  have he' : deriv (v x ·) t =
      -fderiv ℝ (v · t) x (v x t) - gradient (p · t) x := by
    simpa only [sub_eq_add_neg, add_comm] using eq_sub_of_add_eq he
  rw [← he']
  exact hd.hasDerivAt

end Euler.EulerExistenceAndSmoothnessR3
