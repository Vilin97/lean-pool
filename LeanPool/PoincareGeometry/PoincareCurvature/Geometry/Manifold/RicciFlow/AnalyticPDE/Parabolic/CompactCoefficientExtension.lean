/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.NormalizedCutoff

/-!
# Compactly supported coefficient extensions

A `C¹` coefficient field defined on an open chart neighborhood is multiplied
by a cutoff equal to one near a prescribed compact core.  The resulting
all-space field agrees with the original near that core and comes with
explicit global boundedness and Lipschitz witnesses.
-/

noncomputable section
open Set
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

/-- An all-space, bounded, Lipschitz extension of a coefficient field which
agrees with the original field near a compact core. -/
structure CompactCoefficientExtension
    (X V : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : X → V) (K U : Set X) where
  extension : X → V
  bound : ℝ
  lipschitzBound : ℝ
  contDiff_one : ContDiff ℝ 1 extension
  compactSupport : HasCompactSupport extension
  support_subset : tsupport extension ⊆ U
  bound_nonneg : 0 ≤ bound
  lipschitzBound_nonneg : 0 ≤ lipschitzBound
  norm_le : ∀ x, ‖extension x‖ ≤ bound
  norm_sub_le : ∀ x y,
    ‖extension x - extension y‖ ≤ lipschitzBound * dist x y
  eventuallyEq_original : ∀ᶠ x in nhdsSet K, extension x = F x

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cut off a chart-local `C¹` field to obtain a compactly supported global
bounded Lipschitz extension which is unchanged near a compact core. -/
theorem exists_compactCoefficientExtension_of_contDiffOn
    {F : X → V} {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ 1 F U) :
    Nonempty (CompactCoefficientExtension X V F K U) := by
  obtain ⟨χ, hχsupp, hχOne, _hχIcc⟩ :=
    exists_normalizedCutoffControl_one_nhdsSet_of_isCompact hK hU hKU
  let G : X → V := fun x => χ.cutoff x • F x
  have hχ1 : ContDiff ℝ 1 χ.cutoff := χ.contDiff_three.of_le (by norm_num)
  have hG : ContDiff ℝ 1 G ∧ HasCompactSupport G :=
    SmoothDependenceCk.contDiff_and_hasCompactSupport_cutoff_smul
      hU hF hχ1 χ.compactSupport hχsupp
  have hGsupp : tsupport G ⊆ U := by
    calc
      tsupport G = closure (Function.support G) := rfl
      _ ⊆ closure (Function.support χ.cutoff) := closure_mono (by
        intro x hx
        rw [Function.mem_support] at hx ⊢
        intro hχx
        exact hx (by simp [G, hχx]))
      _ = tsupport χ.cutoff := rfl
      _ ⊆ U := hχsupp
  obtain ⟨B, hB⟩ :=
    hG.1.continuous.bounded_above_of_compact_support hG.2
  have hB0 : 0 ≤ B := (norm_nonneg (G 0)).trans (hB 0)
  obtain ⟨L, hL0, hL⟩ :=
    exists_nonneg_lipschitz_bound_of_contDiff_one_hasCompactSupport hG.1 hG.2
  have hGeq : ∀ᶠ x in nhdsSet K, G x = F x := by
    filter_upwards [hχOne] with x hx
    simp [G, hx]
  exact ⟨⟨G, B, L, hG.1, hG.2, hGsupp, hB0, hL0, hB, hL, hGeq⟩⟩

end AnalyticPDE
end RicciFlow
