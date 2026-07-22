/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Basic

/-! # Erdős 97 convex-octagon formalization: Equidistant Four -/

namespace Erdos97Octagon

open scoped InnerProductSpace
open Module

/-- Three vectors with the regular-simplex Gram matrix are linearly independent. -/
theorem linearIndependent_of_regular_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v w : E} {s : ℝ} (hs : 0 < s)
    (huu : ⟪u, u⟫_ℝ = s) (hvv : ⟪v, v⟫_ℝ = s) (hww : ⟪w, w⟫_ℝ = s)
    (huv : ⟪u, v⟫_ℝ = s / 2) (huw : ⟪u, w⟫_ℝ = s / 2)
    (hvw : ⟪v, w⟫_ℝ = s / 2) :
    LinearIndependent ℝ ![u, v, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • u + g 1 • v + g 2 • w = 0 := by
    have h := hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h
    simpa [add_assoc] using h
  have e1 : ⟪g 0 • u + g 1 • v + g 2 • w, u⟫_ℝ = 0 := by rw [hsum]; simp
  have e2 : ⟪g 0 • u + g 1 • v + g 2 • w, v⟫_ℝ = 0 := by rw [hsum]; simp
  have e3 : ⟪g 0 • u + g 1 • v + g 2 • w, w⟫_ℝ = 0 := by rw [hsum]; simp
  simp only [inner_add_left, real_inner_smul_left] at e1 e2 e3
  have cvu : ⟪v, u⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact huv
  have cwu : ⟪w, u⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact huw
  have cwv : ⟪w, v⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact hvw
  rw [huu, cvu, cwu] at e1
  rw [huv, hvv, cwv] at e2
  rw [huw, hvw, hww] at e3
  have hg0 : g 0 = 0 := by nlinarith only [e1, e2, e3, hs]
  have hg1 : g 1 = 0 := by nlinarith only [e1, e2, e3, hs]
  have hg2 : g 2 = 0 := by nlinarith only [e1, e2, e3, hs]
  intro i
  fin_cases i <;> assumption

/-- Four distinct planar points cannot have all six distances equal. -/
theorem four_points_not_pairwise_equidistant
    {a b c d : Plane} {r : ℝ}
    (had : a ≠ d)
    (dab : dist a b = r) (dac : dist a c = r) (dad : dist a d = r)
    (dbc : dist b c = r) (dbd : dist b d = r) (dcd : dist c d = r) :
    False := by
  set u : Plane := a - d with hu
  set v : Plane := b - d with hv
  set w : Plane := c - d with hw
  have hr0 : 0 < r := by
    have h : (0 : ℝ) < dist a d := dist_pos.mpr had
    rwa [dad] at h
  set s : ℝ := r ^ 2 with hsdef
  have hs : 0 < s := by positivity
  have nu : ⟪u, u⟫_ℝ = s := by
    rw [real_inner_self_eq_norm_sq, hu, ← dist_eq_norm, dad, hsdef]
  have nv : ⟪v, v⟫_ℝ = s := by
    rw [real_inner_self_eq_norm_sq, hv, ← dist_eq_norm, dbd, hsdef]
  have nw : ⟪w, w⟫_ℝ = s := by
    rw [real_inner_self_eq_norm_sq, hw, ← dist_eq_norm, dcd, hsdef]
  have huv_norm : ‖u - v‖ = r := by
    have h : u - v = a - b := by rw [hu, hv]; abel
    rw [h, ← dist_eq_norm, dab]
  have huw_norm : ‖u - w‖ = r := by
    have h : u - w = a - c := by rw [hu, hw]; abel
    rw [h, ← dist_eq_norm, dac]
  have hvw_norm : ‖v - w‖ = r := by
    have h : v - w = b - c := by rw [hv, hw]; abel
    rw [h, ← dist_eq_norm, dbc]
  have hnu : ‖u‖ ^ 2 = s := by rw [← real_inner_self_eq_norm_sq]; exact nu
  have hnv : ‖v‖ ^ 2 = s := by rw [← real_inner_self_eq_norm_sq]; exact nv
  have hnw : ‖w‖ ^ 2 = s := by rw [← real_inner_self_eq_norm_sq]; exact nw
  have iuv : ⟪u, v⟫_ℝ = s / 2 := by
    have h := norm_sub_sq_real u v
    rw [huv_norm, hnu, hnv] at h
    rw [hsdef]
    linarith
  have iuw : ⟪u, w⟫_ℝ = s / 2 := by
    have h := norm_sub_sq_real u w
    rw [huw_norm, hnu, hnw] at h
    rw [hsdef]
    linarith
  have ivw : ⟪v, w⟫_ℝ = s / 2 := by
    have h := norm_sub_sq_real v w
    rw [hvw_norm, hnv, hnw] at h
    rw [hsdef]
    linarith
  have hli : LinearIndependent ℝ ![u, v, w] :=
    linearIndependent_of_regular_gram hs nu nv nw iuv iuw ivw
  have hcard := hli.fintype_card_le_finrank
  have hfr : finrank ℝ Plane = 2 := by simp [Plane]
  rw [hfr, Fintype.card_fin] at hcard
  omega

end Erdos97Octagon
