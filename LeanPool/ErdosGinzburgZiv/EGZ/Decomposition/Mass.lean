/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic

/-!
# Mass estimates for decomposition cleanup

The cleanup operations delete local atoms. These finite-sum estimates keep
track of the lost mass and of the resulting deterioration of thickness.
-/

open scoped BigOperators

namespace EGZ

section Mass

variable {α : Type*} [Fintype α]

theorem natMass_mono {w w' : α → ℕ} (h : w' ≤ w) : natMass w' ≤ natMass w :=
  Finset.sum_le_sum fun a _ ↦ h a

theorem natMassOn_mono_weight {w w' : α → ℕ} (h : w' ≤ w) (S : Set α) :
    natMassOn w' S ≤ natMassOn w S := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ S <;> simp [ha, h a]

theorem natMassOn_le (w : α → ℕ) (S : Set α) : natMassOn w S ≤ natMass w := by
  classical
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

theorem natMassOn_add_compl (w : α → ℕ) (S : Set α) :
    natMassOn w S + natMassOn w Sᶜ = natMass w := by
  classical
  rw [natMassOn, natMassOn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem natMass_sub {w w' : α → ℕ} (h : w' ≤ w) :
    natMass (fun a ↦ w a - w' a) = natMass w - natMass w' := by
  exact Finset.sum_tsub_distrib _ (fun a _ ↦ h a)

theorem natMassOn_sub {w w' : α → ℕ} (h : w' ≤ w) (S : Set α) :
    natMassOn (fun a ↦ w a - w' a) S = natMassOn w S - natMassOn w' S := by
  classical
  unfold natMassOn
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ S <;> simp [ha]
  · intro a _
    by_cases ha : a ∈ S <;> simp [ha, h a]

theorem natMassOn_loss_le {w w' : α → ℕ} (h : w' ≤ w) (S : Set α) :
    natMassOn w S - natMassOn w' S ≤ natMass w - natMass w' := by
  rw [← natMassOn_sub h, ← natMass_sub h]
  exact natMassOn_le _ _

theorem natMassOn_loss_le_real {w w' : α → ℕ} (h : w' ≤ w) (S : Set α) :
    (natMassOn w S : ℝ) - natMassOn w' S ≤ (natMass w : ℝ) - natMass w' := by
  have h' : ((natMassOn w S - natMassOn w' S : ℕ) : ℝ) ≤
      ((natMass w - natMass w' : ℕ) : ℝ) := by
    exact_mod_cast natMassOn_loss_le h S
  simpa only [Nat.cast_sub (natMassOn_mono_weight h S),
    Nat.cast_sub (natMass_mono h)] using h'

theorem nnrealMass_natCast (w : α → ℕ) :
    nnrealMass (fun a ↦ (w a : NNReal)) = (natMass w : NNReal) := by
  simp [nnrealMass, natMass]

theorem nnrealMassOn_natCast (w : α → ℕ) (S : Set α) :
    nnrealMassOn (fun a ↦ (w a : NNReal)) S = (natMassOn w S : NNReal) := by
  classical
  simp only [nnrealMassOn, natMassOn, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

end Mass

theorem isThinAlong_iff_natMass {p d : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (K : ℕ) (ε : ℝ) :
    IsThinAlong w ξ K ε ↔
      (1 - ε) * (natMass w : ℝ) ≤ (natMassOn w (slab ξ K) : ℝ) := by
  unfold IsThinAlong IsThinAlongNNReal
  rw [nnrealMass_natCast, nnrealMassOn_natCast]
  simp

theorem isThickAlong_iff_compl {p d : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (K : ℕ) (δ : ℝ) :
    IsThickAlong w ξ K δ ↔
      δ * (natMass w : ℝ) < (natMassOn w (slab ξ K)ᶜ : ℝ) := by
  rw [IsThickAlong, isThinAlong_iff_natMass, not_le]
  have h := natMassOn_add_compl w (slab ξ K)
  have hreal : (natMassOn w (slab ξ K) : ℝ) + natMassOn w (slab ξ K)ᶜ =
      natMass w := by exact_mod_cast h
  constructor <;> intro hlt <;> nlinarith

/-- Deleting at most `α M` mass from a weight of mass at least `ε M`
degrades thickness by at most `α / ε`. The strict inequality agrees with
the definition of thickness as the negation of thinness. -/
theorem IsThickAlong.of_pruning {p d : ℕ} [NeZero p]
    {w w' : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    {K : ℕ} {δ α ε M : ℝ}
    (hthick : IsThickAlong w ξ K δ) (hle : w' ≤ w)
    (hε : 0 < ε) (hα : 0 ≤ α)
    (hlarge : ε * M ≤ (natMass w : ℝ))
    (hloss : (natMass w : ℝ) - natMass w' ≤ α * M)
    (hδ : 0 ≤ δ - α / ε) :
    IsThickAlong w' ξ K (δ - α / ε) := by
  rw [isThickAlong_iff_compl] at hthick ⊢
  have hset := natMassOn_loss_le_real hle (slab ξ K)ᶜ
  have htotal : (natMass w' : ℝ) ≤ natMass w := by
    exact_mod_cast natMass_mono hle
  have hratio : α * M ≤ (α / ε) * (natMass w : ℝ) := by
    have hcancel : α / ε * ε = α := div_mul_cancel₀ _ (ne_of_gt hε)
    have hm := mul_le_mul_of_nonneg_left hlarge (div_nonneg hα hε.le)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left htotal hδ
  nlinarith

end EGZ
