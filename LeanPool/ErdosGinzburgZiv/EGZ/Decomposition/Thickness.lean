/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass

namespace EGZ

theorem natMassOn_mono_set {α : Type*} [Fintype α] (w : α → ℕ)
    {S T : Set α} (h : S ⊆ T) : natMassOn w S ≤ natMassOn w T := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ S
  · simp only [ite_eq_left ha, ite_eq_left (h ha)]
    exact le_rfl
  · simp only [ite_eq_right ha]
    exact Nat.zero_le _

theorem slab_mono {p d K T : ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (h : K ≤ T) : slab ξ K ⊆ slab ξ T := by
  rintro v ⟨z, hz, hmod⟩
  exact ⟨z, hz.trans h, hmod⟩

theorem IsThinAlong.mono_width {p d K T : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ : ℝ}
    (hw : IsThinAlong w ξ K δ) (h : K ≤ T) : IsThinAlong w ξ T δ := by
  rw [isThinAlong_iff_natMass] at hw ⊢
  exact hw.trans (by exact_mod_cast natMassOn_mono_set w (slab_mono h))

theorem IsThickAlong.mono_width {p d K T : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ : ℝ}
    (hw : IsThickAlong w ξ T δ) (h : K ≤ T) : IsThickAlong w ξ K δ :=
  fun hthin ↦ hw (hthin.mono_width h)

theorem IsThinAlong.mono_error {p d K : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ δ' : ℝ}
    (hw : IsThinAlong w ξ K δ) (h : δ ≤ δ') : IsThinAlong w ξ K δ' := by
  rw [isThinAlong_iff_natMass] at hw ⊢
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left h 1) (Nat.cast_nonneg _)).trans hw

theorem FlagDecomposition.IsCompleteElement.mono_width {p d K T : ℕ} [NeZero p]
    {f : FpCoord p d → ℕ} {Φ : FlagDecomposition p d f} {x : Φ.flag.Node} {δ : ℝ}
    (hw : Φ.IsCompleteElement x T δ) (h : K ≤ T) : Φ.IsCompleteElement x K δ :=
  fun ξ hξ ↦ (hw ξ hξ).mono_width h

end EGZ
