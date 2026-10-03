/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ChangedAdvectionTerms

/-! Finite, ordered correction expansions for actual material powers. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The coarse term is separate; every listed term contains fast advection. -/
def amnrMaterialErrorTerms : ℕ → List AmnrAdvectionTerm
  | 0 => []
  | n + 1 => (amnrMaterialErrorTerms n).flatMap amnrChangedAdvectionDerivativeTerms ++
      [⟨[(0, [])], some 0 :: List.replicate n none⟩,
       ⟨[(1, [])], some 1 :: List.replicate n none⟩]

/-- Sum of the advection terms representing the iterated material error. -/
def amnrMaterialErrorValue (b c : AmnrSpace → Vec 2) (f : AmnrSpace → ℝ)
    (n : ℕ) : AmnrSpace → ℝ :=
  ((amnrMaterialErrorTerms n).map
    (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f)).sum

theorem amnrMaterialErrorValue_contDiff {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrMaterialErrorValue b c f n) := by
  apply amnr_list_sum_contDiff
  intro g hg
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
  exact amnrAdvectionTermValue_contDiff hc (amnrAdvectionVelocity_contDiff hb hc) hf t

/-- Exact correction recurrence, with the pure coarse material term absent
from the differentiated error list. -/
theorem amnrMaterialErrorValue_succ {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (z : AmnrSpace) :
    amnrMaterialErrorValue b c f (n + 1) z =
      amnrOp b none (amnrMaterialErrorValue b c f n) z +
      ∑ p : Fin 2, amnrAdvectionVelocity b c p z *
        amnrOp c (some p) (amnrWord c (List.replicate n none) f) z := by
  unfold amnrMaterialErrorValue
  rw [amnr_list_sum_apply]
  simp only [amnrMaterialErrorTerms, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map,
        Function.comp_def]
  rw [← amnrChangedAdvectionDerivativeTerms_list_value hb hc hf]
  rw [Fin.sum_univ_two]
  dsimp [amnrAdvectionTermValue, amnrAdvectionProduct, amnrWord]
  ring

/-- All actual material powers equal one pure coarse power plus the finite
ordered correction. No higher derivative estimate is assumed. -/
theorem amnr_material_power_expansion {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    amnrWord b (List.replicate n none) f =
      amnrWord c (List.replicate n none) f + amnrMaterialErrorValue b c f n := by
  induction n with
  | zero => simp [amnrWord, amnrMaterialErrorValue, amnrMaterialErrorTerms]
  | succ n ih =>
    have hcf := contDiffOn_univ.mp
      (amnrWord_contDiffOn_infty isOpen_univ hc.contDiffOn hf.contDiffOn
        (List.replicate n none))
    have he := amnrMaterialErrorValue_contDiff hb hc hf n
    funext z
    simp only [List.replicate_succ, amnrWord]
    rw [ih]
    change amnrWord b [none] (_ + _) z = _
    rw [amnrWord_add_global hb hcf he [none]]
    simp only [amnrWord, Pi.add_apply]
    rw [amnrMaterialErrorValue_succ hb hc hf]
    have hh := amnr_material_operator_change b c
      (amnrWord c (List.replicate n none) f) z
    dsimp [amnrAdvectionVelocity] at *
    linarith only [hh]

end AVenhance.Infra.Section4
