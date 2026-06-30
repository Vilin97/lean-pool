/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.EuclideanAngle
import LeanPool.ThreeGap.EuclideanPacking
import LeanPool.ThreeGap.EuclideanGrowth

/-!
# The Euclidean growth inequality `2 qₙ ≤ qₙ₊₅` (`K = 5`) via the planar packing count

This is the core of the Euclidean route to `g₂ ≤ 6`: the best-simultaneous-approximation
denominators
in the **Euclidean (`L²`) norm** on `𝕋²` at least double every **5** steps. Combined with
Chevallier's
count this gives the Euclidean five-distance bound `g₂ ≤ 6` (the sharp `g₂ ≤ 5` needs Romanov's `K =
4`).

The mechanism (Lagarias/Ermakov, with the contact number `6` replaced by the strict planar packing
count `5`): if the denominators failed to double in a window of length 5, the six remainder vectors
`r(qₙ), …, r(qₙ₊₅)` would all have Euclidean norm `≤ δₙ` and be pairwise `≥ δₙ` apart (the
best-approximation separation: their index differences lie in `(0, qₙ)`, so `hbest` forces the
defect
up). The metric→angle crux (`EuclideanAngle`) turns that into pairwise angles **strictly** `> π/3`
(strict because the defects strictly decrease, so all but the first vector is shorter than `δₙ`),
and
the planar packing count (`EuclideanPacking.not_six_separated`) says at most **5** such vectors fit
—
contradiction.

Stated, like `EuclideanGrowth.euclidean_growth_additive`, over an abstract best-approximation
sequence
`(q, p)` with the defining hypotheses; discharging those for the actual record denominators is the
remaining instantiation step. Axiom-clean.
-/

namespace ThreeGap.SimApprox

open scoped Real
open ThreeGap.EuclideanPacking

variable {n : ℕ}

/-- `rem` negates under simultaneous negation of denominator and translate. -/
theorem rem_neg_neg' (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) :
    rem α (-q) (-p) = -(rem α q p) := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  push_cast; ring

/-- The defect for a **symmetric** norm is even in the denominator: `δ_{−q} = δ_q`. -/
theorem deltaN_neg (N : (Fin n → ℝ) → ℝ) (hN0 : ∀ x, 0 ≤ N x) (hNneg : ∀ x, N (-x) = N x)
    (α : Fin n → ℝ) (q : ℤ) : deltaN N α (-q) = deltaN N α q := by
  have key : ∀ r : ℤ, deltaN N α (-r) ≤ deltaN N α r := by
    intro r
    refine le_ciInf (fun p => ?_)
    calc deltaN N α (-r) ≤ N (rem α (-r) (-p)) := deltaN_le N hN0 α (-r) (-p)
      _ = N (rem α r p) := by rw [rem_neg_neg', hNneg]
  exact le_antisymm (key q) (by have := key (-q); rwa [neg_neg] at this)

/-- The Euclidean norm is symmetric. -/
theorem euclNorm_neg (x : Fin n → ℝ) : euclNorm n (-x) = euclNorm n x := by
  rw [show -x = (-1 : ℝ) • x by simp, euclNorm_smul]; simp

/-- **The Euclidean growth inequality, `K = 5` (planar packing).** For a best-`L²`-approximation
sequence `(q, p)` of `α : Fin 2 → ℝ` with the record/monotonicity hypotheses, the denominators
at least double every five steps: `2 qₙ ≤ qₙ₊₅`. -/
theorem euclidean_growth_five (α : Fin 2 → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin 2 → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, euclNorm 2 (rem α (q k) (p k)) ≤ deltaN (euclNorm 2) α (q k))
    (hdec : ∀ i j, i ≤ j → deltaN (euclNorm 2) α (q j) ≤ deltaN (euclNorm 2) α (q i))
    (hdecstrict : ∀ k, deltaN (euclNorm 2) α (q (k + 1)) < deltaN (euclNorm 2) α (q k))
    (hbest : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q k →
      deltaN (euclNorm 2) α (q k) < deltaN (euclNorm 2) α m)
    (hpos : ∀ k, 0 < deltaN (euclNorm 2) α (q k))
    (N : ℕ) : 2 * q N ≤ q (N + 5) := by
  by_contra hcon
  rw [not_le] at hcon
  -- the exact remainder norm equals the defect
  have hnorm_eq : ∀ k, euclNorm 2 (rem α (q k) (p k)) = deltaN (euclNorm 2) α (q k) := fun k =>
    le_antisymm (hattain k) (deltaN_le (euclNorm 2) euclNorm_nonneg α (q k) (p k))
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  -- the six remainder vectors in the Euclidean plane
  set w : Fin 6 → EuclideanSpace ℝ (Fin 2) :=
    fun i => (EuclideanSpace.equiv (Fin 2) ℝ).symm (rem α (q (N + i.val)) (p (N + i.val))) with hw
  have hnorm_w : ∀ i : Fin 6, ‖w i‖ = deltaN (euclNorm 2) α (q (N + i.val)) := by
    intro i; simp only [hw]; exact hnorm_eq _
  have hwne : ∀ i : Fin 6, w i ≠ 0 := by
    intro i hi
    have h0 : ‖w i‖ = 0 := by rw [hi, norm_zero]
    rw [hnorm_w i] at h0
    linarith [hpos (N + i.val)]
  -- index bounds under the doubling failure
  have hlb : ∀ i : Fin 6, q N ≤ q (N + i.val) := fun i => hmono.monotone (by omega)
  have hub : ∀ i : Fin 6, q (N + i.val) < 2 * q N := by
    intro i
    exact lt_of_le_of_lt (hmono.monotone (show N + i.val ≤ N + 5 by omega)) hcon
  -- apply the planar packing count
  refine not_six_separated ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) w hwne ?_
  intro i j hij
  have hwi : 0 < ‖w i‖ := by rw [hnorm_w]; exact hpos _
  have hwj : 0 < ‖w j‖ := by rw [hnorm_w]; exact hpos _
  have hui : ‖w i‖ ≤ deltaN (euclNorm 2) α (q N) := by
    rw [hnorm_w]; exact hdec N (N + i.val) (by omega)
  have huj : ‖w j‖ ≤ deltaN (euclNorm 2) α (q N) := by
    rw [hnorm_w]; exact hdec N (N + j.val) (by omega)
  -- the separation `δₙ ≤ ‖w i − w j‖`
  have hwij : ‖w i - w j‖
      = euclNorm 2 (rem α (q (N + i.val) - q (N + j.val)) (p (N + i.val) - p (N + j.val))) := by
    simp only [hw]
    rw [← map_sub, rem_sub]
    rfl
  have hsep : deltaN (euclNorm 2) α (q N) ≤ ‖w i - w j‖ := by
    rw [hwij]
    set m : ℤ := q (N + i.val) - q (N + j.val) with hm
    have hmne : m ≠ 0 := by
      rw [hm, sub_ne_zero]; exact fun h => hij (by
        have := hmono.injective h; exact Fin.ext (by omega))
    have habs_pos : 0 < |m| := abs_pos.mpr hmne
    have habs_lt : |m| < q N := by
      rw [hm, abs_sub_lt_iff]
      constructor <;> [linarith [hub i, hlb j]; linarith [hub j, hlb i]]
    have hdN_abs : deltaN (euclNorm 2) α (q N) < deltaN (euclNorm 2) α |m| :=
      hbest N |m| habs_pos habs_lt
    have hsym : deltaN (euclNorm 2) α |m| = deltaN (euclNorm 2) α m := by
      rcases abs_choice m with h | h
      · rw [h]
      · rw [h, deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg]
    have hle : deltaN (euclNorm 2) α m
        ≤ euclNorm 2 (rem α m (p (N + i.val) - p (N + j.val))) :=
      deltaN_le (euclNorm 2) euclNorm_nonneg α m _
    rw [hsym] at hdN_abs
    linarith [hdN_abs, hle]
  -- at least one of the two vectors is strictly shorter than `δₙ`
  have hstrict : ‖w i‖ < deltaN (euclNorm 2) α (q N) ∨ ‖w j‖ < deltaN (euclNorm 2) α (q N) := by
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · right
      have hj1 : 1 ≤ j.val := by
        rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
        · exact absurd (Fin.ext (by omega) : i = j) hij
        · exact hjpos
      rw [hnorm_w]
      exact lt_of_le_of_lt (hdec (N + 1) (N + j.val) (by omega)) (hdecstrict N)
    · left
      rw [hnorm_w]
      exact lt_of_le_of_lt (hdec (N + 1) (N + i.val) (by omega)) (hdecstrict N)
  exact EuclideanAngle.angle_gt_pi_div_three hwi hwj hui huj hsep hstrict

end ThreeGap.SimApprox
