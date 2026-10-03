/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteWordSums

/-! Actual differentiated correction monomials for changing material velocity. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The actual difference of the two advecting velocities. -/
def amnrAdvectionVelocity (b c : AmnrSpace → Vec 2) (p : Fin 2) : AmnrSpace → ℝ :=
  fun z => b z p - c z p

theorem amnrAdvectionVelocity_contDiff {b c : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (p : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrAdvectionVelocity b c p) :=
  ((contDiff_apply ℝ ℝ p).comp hb).sub ((contDiff_apply ℝ ℝ p).comp hc)

/-- Every new-velocity material derivative is its coarse material part plus
two actual fast-advection derivatives. Each new factor records its coordinate. -/
def amnrChangedAdvectionDerivativeTerms (t : AmnrAdvectionTerm) : List AmnrAdvectionTerm :=
  amnrAdvectionDerivativeTerms none t.factors t.scalarWord ++
    (amnrAdvectionDerivativeTerms (some 0) t.factors t.scalarWord).map
      (amnrAdvectionTermPrepend (0, [])) ++
    (amnrAdvectionDerivativeTerms (some 1) t.factors t.scalarWord).map
      (amnrAdvectionTermPrepend (1, []))

/-- The full differentiated list evaluates to the actual new material
operator. Its two advection terms are retained, without commuting operators. -/
theorem amnrChangedAdvectionDerivativeTerms_value {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : AmnrAdvectionTerm) (z : AmnrSpace) :
    amnrOp b none (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t) z =
      ((amnrChangedAdvectionDerivativeTerms t).map
        (fun a => amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f a z)).sum := by
  have hv := amnrAdvectionVelocity_contDiff hb hc
  have hh := amnr_material_operator_change b c
    (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t) z
  rw [Fin.sum_univ_two] at hh
  dsimp [amnrChangedAdvectionDerivativeTerms]
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
    amnrAdvectionTermValue_sum_prepend, amnrAdvectionTermValue_sum_prepend]
  rw [← amnrAdvectionDerivativeTerms_value hc hv hf none,
    ← amnrAdvectionDerivativeTerms_value hc hv hf (some 0),
    ← amnrAdvectionDerivativeTerms_value hc hv hf (some 1)]
  simp only [amnrWord]
  change _ = amnrOp c none (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t) z +
    amnrAdvectionVelocity b c 0 z *
      amnrOp c (some 0) (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t) z +
    amnrAdvectionVelocity b c 1 z *
      amnrOp c (some 1) (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t) z
  dsimp [amnrAdvectionVelocity] at *
  linarith only [hh]

/-- The actual changed material operator differentiates a finite correction
sum into the concatenated derivative lists. -/
theorem amnrChangedAdvectionDerivativeTerms_list_value {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (T : List AmnrAdvectionTerm) (z : AmnrSpace) :
    amnrOp b none ((T.map (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f)).sum) z =
      ((T.flatMap amnrChangedAdvectionDerivativeTerms).map
        (fun a => amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f a z)).sum := by
  have hv := amnrAdvectionVelocity_contDiff hb hc
  induction T with
  | nil => simp [amnrOp]
  | cons t T ih =>
    have ht := amnrAdvectionTermValue_contDiff hc hv hf t
    have hT : ContDiff ℝ (⊤ : ℕ∞)
        ((T.map (amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f)).sum) := by
      apply amnr_list_sum_contDiff
      intro g hg
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
      exact amnrAdvectionTermValue_contDiff hc hv hf a
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    change amnrWord b [none] (_ + _) z = _
    rw [amnrWord_add_global hb ht hT [none]]
    simp only [amnrWord, Pi.add_apply]
    rw [amnrChangedAdvectionDerivativeTerms_value hb hc hf t z, ih]

end AVenhance.Infra.Section4
