/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DriftCommutatorTerms

/-! Exact finite-product expansion of the spatial drift correction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVenhance.Infra.Section4

theorem DriftCommutatorExpansion.amnrDriftTerms_derivative_sum {b : AmnrSpace → Vec 2} {f :
    AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 2) (T : List AmnrDriftTerm) :
    amnrOp b (some i) ((T.map (amnrDriftTermValue b f)).sum) =
      ((T.flatMap (amnrDriftDerivativeTerms i)).map (amnrDriftTermValue b f)).sum := by
  have hh := amnrWord_list_sum_global hb (T.map (amnrDriftTermValue b f))
    (fun g hg => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
      exact amnrDriftTermValue_contDiff hb hf q) [some i]
  change amnrOp b (some i) ((T.map (amnrDriftTermValue b f)).sum) = _ at hh
  rw [hh]
  simp only [List.map_map]
  clear hh
  induction T with
  | nil => rfl
  | cons q T ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    simp only [Function.comp_apply, amnrWord] at ih ⊢
    rw [amnrDriftDerivativeTerms_value hb hf i q, ih]

end AVenhance.Infra.Section4
