/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.StarOrdered

/-!
# LeanPool.Rupert.Convex

Imported Lean Pool material for `LeanPool.Rupert.Convex`.
-/

open Pointwise

namespace Convex

/-- `n`-dimensional Euclidean space over `ℝ`, indexed by `Fin n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-
Lemma:

If a convex set X of a euclidean space contains an open ball around
the origin, then for any ℓ ∈ (0,1), we have ℓ X ⊆ int(X).

Proof:

Let a point y ∈ ℓX be given. Hence there is x ∈ X with y = ℓx.
Suffices to show there's an open ball U ∋ y with U ⊆ X. Choose the
radius of U to be (1 - ℓ)ε. Let any point u ∈ U be given, we must show
u ∈ X. Since X is convex, it suffices to show u is on a line segment
between two points already in X. Choose the segment seg₁ --- seg₂,
where

   seg₁ := x
   seg₂ := (u - ℓx)/(1 - ℓ)

Observe that since ‖u - ℓx‖ < (1-ℓ)ε, we have ‖(u-ℓx)/(1-ℓ)‖ < ε,
hence seg₂ ∈ X by assumption that X contains the ε-ball about the
origin.

Then the claim that u is on the segment follows by computing

    ℓ seg₁ + (1 - ℓ) seg₂
  = ℓ x + u - ℓx
  = u
-/


lemma move_scale {n : ℕ} {s : ℝ} (sgz : s > 0) {v : E n} {Y : Set (E n)} :
     v ∈ s • Y → (1 / s) • v ∈ Y := by
  intro ⟨_, ⟨winy, factor⟩⟩
  rw [← factor, smul_smul]
  rw [one_div_mul_cancel (ne_of_lt sgz).symm, one_smul]
  exact winy

lemma subset_interior_hull' {n : ℕ} {X : Set (E n)} {ε ℓ : ℝ}
    (hε : 0 < ε)
    (hℓ : ℓ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε ⊆ X) :
    ℓ • X ⊆ interior (convexHull ℝ X) := by
  intro ix hix -- "inner x"
  apply Set.mem_sUnion.mpr
  have lnz : ℓ ≠ 0 := ne_of_gt (by simp_all only [Set.mem_Ioo])
  have olgz : 0 < 1 - ℓ := by simp_all only [Set.mem_Ioo, sub_pos]
  -- Here we choose the radius around ix that is fully contained in X.
  use Metric.ball ix ((1 - ℓ) * ε)
  have hb : 0 < (1 - ℓ) * ε := mul_pos olgz hε
  refine ⟨⟨Metric.isOpen_ball, ?_⟩, Metric.mem_ball_self hb⟩
  intro u hu
  let seg1 := (1/ℓ) • ix
  let seg2 := (1/(1-ℓ)) • (u - ix)
  have seg1_in_X : seg1 ∈ X := by -- "outer x" is still in X
      obtain ⟨w, winx, ix_eq_lw⟩ := hix
      simp only [seg1, ← ix_eq_lw]; rw [smul_smul]; field_simp
      simp only [one_smul]
      exact winx
  have seg2_in_X : seg2 ∈ X := by
    refine h0 (move_scale olgz ?_)
    rw [smul_ball (ne_of_gt olgz) 0 ε, smul_zero,
        show (‖1-ℓ‖ = |1-ℓ|) from rfl,
        abs_of_pos olgz]
    simp_all only [Metric.mem_ball, dist_zero_right]
    exact hu
  have pt_in_seg : u ∈ segment ℝ seg1 seg2 := ⟨ ℓ, 1 - ℓ,
        ⟨ le_of_lt (by simp_all only [Set.mem_Ioo]),
          le_of_lt olgz,
          add_sub_cancel _ _,
          by rw [smul_smul, smul_smul]; field_simp; simp ⟩⟩
  exact segment_subset_convexHull seg1_in_X seg2_in_X pt_in_seg

lemma subset_interior_hull {n : ℕ} {X : Set (E n)} {ε₀ ε₁ : ℝ}
    (hε₀ : 0 < ε₀)
    (hε₁ : ε₁ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε₀ ⊆ convexHull ℝ X) :
    convexHull ℝ ((1 - ε₁) • X) ⊆
      interior (convexHull ℝ X) := by
  rw [convexHull_smul]
  have h3 := subset_interior_hull' hε₀ (Set.Ioo.one_sub_mem hε₁) h0
  rw [ClosureOperator.idempotent] at h3
  exact h3

lemma mem_interior_hull {n : ℕ} {X : Set (E n)} {ε₀ ε₁ : ℝ}
    (hε₀ : 0 < ε₀)
    (hε₁ : ε₁ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε₀ ⊆ convexHull ℝ X)
    {p : E n}
    (h : p ∈ convexHull ℝ ((fun v : E n ↦ (1 - ε₁) • v) '' X)) :
    p ∈ interior (convexHull ℝ X) := by
  revert h p
  convert subset_interior_hull hε₀ hε₁ h0

lemma ball_in_hull_of_corners_in_hull {X : Set (E 2)} {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1)
    (h₀ : !₂[ε, ε] ∈ convexHull ℝ X)
    (h₁ : !₂[-ε, ε] ∈ convexHull ℝ X)
    (h₂ : !₂[-ε, -ε] ∈ convexHull ℝ X)
    (h₃ : !₂[ε, -ε] ∈ convexHull ℝ X)
    : Metric.ball 0 ε ⊆ convexHull ℝ X := by
  intro v hv
  rw [Set.mem_Ioo] at hε
  obtain ⟨hε0, hε1⟩ := hε
  rw [mem_ball_zero_iff] at hv
  have hva0 := trans (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 0)) hv
  rw [abs_lt] at hva0
  obtain ⟨hva00, hva01⟩ := hva0
  have hva1 := trans (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 1)) hv
  rw [abs_lt] at hva1
  obtain ⟨hva10, hva11⟩ := hva1
  have hv0 : v 0 / ε < 1 := by bound
  have hv0' : -1 < v 0 / ε := by
    have h1 : -ε / ε < v 0 / ε := (div_lt_div_iff_of_pos_right hε0).mpr hva00
    grind only
  have hv1 : v 1 / ε < 1 := by bound
  have hv1' : -1 < v 1 / ε := by
    have h1 : -ε / ε < v 1 / ε := (div_lt_div_iff_of_pos_right hε0).mpr hva10
    grind only
  rw [←ClosureOperator.idempotent]
  rw [mem_convexHull_iff_exists_fintype]
  use Fin 4, inferInstance
  let cx := (1 + v 0 / ε) / 2
  let cy := (1 + v 1 / ε) / 2
  use ![cx * cy, (1 - cx) * cy, (1 - cx) * (1 - cy), cx * (1 - cy)]
  use ![!₂[ε, ε], !₂[-ε, ε], !₂[-ε, -ε], !₂[ε, -ε]]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> (simp [cx, cy]; nlinarith)
  · simp [Fin.sum_univ_four]; ring
  · intro i
    fin_cases i <;> simp [h₀, h₁, h₂, h₃]
  · rw [Fin.sum_univ_four]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [mul_sub, sub_mul, sub_smul, cx, cy, one_mul, mul_one]
    ext i
    fin_cases i
    · simp; field
    · simp; field

end Convex
