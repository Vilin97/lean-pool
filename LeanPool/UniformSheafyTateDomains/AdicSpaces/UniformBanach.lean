/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Norm-Power-Bounded Elements and Uniform Banach Rings

We define norm-power-bounded elements of a normed ring and the notion of a *uniform*
Banach ring, where the set of norm-power-bounded elements is metrically bounded.

## Main definitions

* `IsNormPowerBounded a` : An element `a` of a normed ring is norm-power-bounded if the
  set `{aⁿ | n ∈ ℕ}` is metrically bounded.
* `normPowerBoundedSet K` : The set of all norm-power-bounded elements of `K` (the normed
  analogue of `A°`).
* `IsUniformBanach K` : A normed ring `K` is uniform if `normPowerBoundedSet K` is bounded.

## Main results

* `isNormPowerBounded_iff` : Characterization via an explicit bound `C` on `‖aⁿ‖`.
* `isNormPowerBounded_zero` : Zero is norm-power-bounded.
* `isNormPowerBounded_one` : One is norm-power-bounded.
* `isUniformBanach_iff` : Characterization via a uniform bound on power-bounded elements.
-/

@[expose] public section

open Bornology

/-! ### Norm-power-bounded elements -/

/-- An element `a` of a normed ring is **norm-power-bounded** if the set `{aⁿ | n ∈ ℕ}` is
metrically bounded, i.e., `sup_n ‖aⁿ‖ < ∞`. This is the normed-ring analogue of
`TopologicalRing.IsPowerBounded` from `Bounded.lean`. -/
def IsNormPowerBounded {K : Type*} [SeminormedRing K] (a : K) : Prop :=
  IsBounded (Set.range (fun n : ℕ => a ^ n))

/-- The set of all norm-power-bounded elements of a normed ring (the analogue of `A°`
in the normed setting). -/
def normPowerBoundedSet (K : Type*) [SeminormedRing K] : Set K :=
  {a : K | IsNormPowerBounded a}

/-- Equivalent characterization: `a` is norm-power-bounded iff there exists `C` with
`‖aⁿ‖ ≤ C` for all `n`. -/
theorem isNormPowerBounded_iff {K : Type*} [SeminormedRing K] {a : K} :
    IsNormPowerBounded a ↔ ∃ C : ℝ, ∀ n : ℕ, ‖a ^ n‖ ≤ C := by
  simp only [IsNormPowerBounded, isBounded_iff_forall_norm_le]
  constructor
  · rintro ⟨C, hC⟩; exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  · rintro ⟨C, hC⟩; exact ⟨C, fun _ ⟨n, hn⟩ => hn ▸ hC n⟩

/-- Zero is norm-power-bounded. -/
theorem isNormPowerBounded_zero (K : Type*) [SeminormedRing K] :
    IsNormPowerBounded (0 : K) := by
  rw [isNormPowerBounded_iff]
  refine ⟨max ‖(1 : K)‖ 0, fun n => ?_⟩
  rcases n with _ | n
  · simp
  · rw [zero_pow n.succ_ne_zero, norm_zero]; exact le_max_right _ _

/-- One is norm-power-bounded. -/
theorem isNormPowerBounded_one (K : Type*) [SeminormedRing K] :
    IsNormPowerBounded (1 : K) := by
  rw [isNormPowerBounded_iff]; exact ⟨‖(1 : K)‖, fun n => by simp⟩

/-! ### Uniform Banach rings -/

/-- A normed ring is **uniform** if the set of norm-power-bounded elements is metrically
bounded. Equivalently, there exists `C > 0` such that `‖a‖ ≤ C` for every `a` with
`sup_n ‖aⁿ‖ < ∞`.

In the nonarchimedean Banach ring setting, this is equivalent to saying the spectral
seminorm is equivalent to the given norm. -/
class IsUniformBanach (K : Type*) [SeminormedRing K] : Prop where
  /-- The set of norm-power-bounded elements is metrically bounded. -/
  isBounded_normPowerBounded : IsBounded (normPowerBoundedSet K)

/-- Equivalent characterization of uniform: there exists a constant `C` bounding the norm
of every power-bounded element. -/
theorem isUniformBanach_iff {K : Type*} [SeminormedRing K] :
    IsUniformBanach K ↔ ∃ C : ℝ, ∀ a : K, IsNormPowerBounded a → ‖a‖ ≤ C := by
  constructor
  · intro ⟨h⟩; rw [isBounded_iff_forall_norm_le] at h; exact h
  · intro ⟨C, hC⟩; exact ⟨isBounded_iff_forall_norm_le.mpr ⟨C, fun _ ha => hC _ ha⟩⟩
