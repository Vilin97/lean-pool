/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.GoodScale.ScalarBounds
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.Inputs

/-! # P4 -/

open scoped BigOperators Matrix.Norms.Elementwise
open scoped Matrix.Norms.L2Operator

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.sqrt.tau.absorb`: product estimate obtained from the terminal
tau-drop bound and the linear lower-scale response expectation bound used in
the note.
-/
theorem tau_mul_response_le_sqrt_budget_sq_of_rtau_response_bounds
    {tau response r_m C_response C_sqrt rho delta F_m : ℝ}
    (hr_pos : 0 < r_m)
    (hresponse_nonneg : 0 ≤ response)
    (hrho_nonneg : 0 ≤ rho)
    (hdelta_pos : 0 < delta)
    (hdelta_le_F : delta ≤ F_m)
    (hrt : r_m * tau ≤ (1 / 2 : ℝ) * (rho * F_m))
    (hresponse : response ≤ C_response * r_m)
    (hC_response_nonneg : 0 ≤ C_response)
    (hC_response_le : C_response ≤ C_sqrt ^ 2) :
    tau * response ≤
      (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m) ^ 2 := by
  have hF_pos : 0 < F_m := hdelta_pos.trans_le hdelta_le_F
  have hF_nonneg : 0 ≤ F_m := le_of_lt hF_pos
  have hrhoF_nonneg : 0 ≤ rho * F_m :=
    mul_nonneg hrho_nonneg hF_nonneg
  have htau_bound : tau ≤ ((1 / 2 : ℝ) * (rho * F_m)) / r_m := by
    rw [le_div_iff₀ hr_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrt
  have hhalf_rhoF_nonneg : 0 ≤ (1 / 2 : ℝ) * (rho * F_m) := by
    nlinarith [hrhoF_nonneg]
  have hfactor_nonneg :
      0 ≤ ((1 / 2 : ℝ) * (rho * F_m)) / r_m :=
    div_nonneg hhalf_rhoF_nonneg (le_of_lt hr_pos)
  have hprod_linear : tau * response ≤ C_response * (rho * F_m) := by
    calc
      tau * response
          ≤ (((1 / 2 : ℝ) * (rho * F_m)) / r_m) * response :=
            mul_le_mul_of_nonneg_right htau_bound hresponse_nonneg
      _ ≤ (((1 / 2 : ℝ) * (rho * F_m)) / r_m) *
            (C_response * r_m) :=
            mul_le_mul_of_nonneg_left hresponse hfactor_nonneg
      _ = (C_response / 2) * (rho * F_m) := by
            field_simp [ne_of_gt hr_pos]
      _ ≤ C_response * (rho * F_m) := by
            nlinarith [mul_nonneg hC_response_nonneg hrhoF_nonneg]
  have hdelta_inv_nonneg : 0 ≤ delta⁻¹ :=
    inv_nonneg.mpr (le_of_lt hdelta_pos)
  have hF_le_delta :
      F_m ≤ delta⁻¹ * F_m ^ 2 := by
    have hmul : delta * F_m ≤ F_m * F_m :=
      mul_le_mul_of_nonneg_right hdelta_le_F hF_nonneg
    have hmul' :
        delta⁻¹ * (delta * F_m) ≤ delta⁻¹ * (F_m * F_m) :=
      mul_le_mul_of_nonneg_left hmul hdelta_inv_nonneg
    calc
      F_m = delta⁻¹ * (delta * F_m) := by
        field_simp [ne_of_gt hdelta_pos]
      _ ≤ delta⁻¹ * (F_m * F_m) := hmul'
      _ = delta⁻¹ * F_m ^ 2 := by ring
  have hsquare :
      (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m) ^ 2 =
        C_sqrt ^ 2 * (rho * (delta⁻¹ * F_m ^ 2)) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hrho_nonneg,
      Real.sq_sqrt hdelta_inv_nonneg]
    ring
  have hC_scale :
      C_response * (rho * F_m) ≤ C_sqrt ^ 2 * (rho * F_m) :=
    mul_le_mul_of_nonneg_right hC_response_le hrhoF_nonneg
  have hF_scale : rho * F_m ≤ rho * (delta⁻¹ * F_m ^ 2) :=
    mul_le_mul_of_nonneg_left hF_le_delta hrho_nonneg
  have htail :
      C_sqrt ^ 2 * (rho * F_m) ≤
        C_sqrt ^ 2 * (rho * (delta⁻¹ * F_m ^ 2)) :=
    mul_le_mul_of_nonneg_left hF_scale (sq_nonneg C_sqrt)
  calc
    tau * response
        ≤ C_response * (rho * F_m) := hprod_linear
    _ ≤ C_sqrt ^ 2 * (rho * F_m) := hC_scale
    _ ≤ C_sqrt ^ 2 * (rho * (delta⁻¹ * F_m ^ 2)) := htail
    _ = (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m) ^ 2 :=
        hsquare.symm

/--
Source labels `e.drift.general` and `e.drift.nodrop`: the pointwise square
bound behind the weighted no-drop drift estimate when
`T_m = (1 + F_m)^2 / F_m`.
-/
theorem drift_general_square_bound {D C rho F_m T_m : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hC_nonneg : 0 ≤ C)
    (hrho_nonneg : 0 ≤ rho)
    (hF_pos : 0 < F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m)
    (hD : D ≤ C * (rho * F_m) / (1 + F_m)) :
    D ^ 2 ≤ C ^ 2 * rho ^ 2 * F_m / T_m := by
  have hden_pos : 0 < 1 + F_m := by linarith
  let B : ℝ := C * (rho * F_m) / (1 + F_m)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq : D ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_nonneg (B - D)]
  calc
    D ^ 2 ≤ B ^ 2 := hsq
    _ = C ^ 2 * rho ^ 2 * F_m / T_m := by
      rw [hT]
      dsimp [B]
      field_simp [ne_of_gt hF_pos, ne_of_gt hden_pos]

/--
Source label `l.S.and.J`, equation `e.S.term.bound`: above the small-contrast
threshold, the terminal weight `T_m = (1 + F_m)^2 / F_m` is bounded by a
threshold-dependent multiple of `F_m`.
-/
theorem terminal_weight_le_delta_mul {T_m F_m delta : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_F : delta ≤ F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m) :
    T_m ≤ (1 + delta⁻¹) ^ 2 * F_m := by
  have hF_pos : 0 < F_m := hdelta_pos.trans_le hdelta_le_F
  have hinv_le : F_m⁻¹ ≤ delta⁻¹ := inv_anti₀ hdelta_pos hdelta_le_F
  have hbase : 1 + F_m⁻¹ ≤ 1 + delta⁻¹ := add_le_add (le_refl 1) hinv_le
  have hleft_nonneg : 0 ≤ 1 + F_m⁻¹ := by positivity
  have hright_nonneg : 0 ≤ 1 + delta⁻¹ := by positivity
  have hsquare : (1 + F_m⁻¹) ^ 2 ≤ (1 + delta⁻¹) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hbase
  have hmul :=
    mul_le_mul_of_nonneg_right hsquare (le_of_lt hF_pos)
  rw [hT]
  calc
    (1 + F_m) ^ 2 / F_m = (1 + F_m⁻¹) ^ 2 * F_m := by
      field_simp [ne_of_gt hF_pos]
      ring
    _ ≤ (1 + delta⁻¹) ^ 2 * F_m := hmul

/--
Source label `l.S.and.J`, equation `e.S.term.bound`: constant-form version of
the small-contrast threshold absorption used for the paper's
`C_{\delta_{\rm sc}}`.
-/
theorem terminal_weight_le_const_mul {T_m F_m delta C_delta : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_F : delta ≤ F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m)
    (hC_delta : (1 + delta⁻¹) ^ 2 ≤ C_delta) :
    T_m ≤ C_delta * F_m := by
  have hF_nonneg : 0 ≤ F_m := le_trans (le_of_lt hdelta_pos) hdelta_le_F
  exact (terminal_weight_le_delta_mul hdelta_pos hdelta_le_F hT).trans
    (mul_le_mul_of_nonneg_right hC_delta hF_nonneg)

/--
Source label `l.S.and.J`, equation `e.S.term.bound`: after the terminal
fluctuation sum is made small, the small-contrast threshold converts
`T_m S_{k,m}` into a multiple of `F_m`.
-/
theorem terminal_weight_mul_term_le_const_mul_contrast_of_le
    {T_m F_m delta C_delta term eta : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_F : delta ≤ F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m)
    (hC_delta : (1 + delta⁻¹) ^ 2 ≤ C_delta)
    (hterm_nonneg : 0 ≤ term)
    (hterm_le : term ≤ eta) :
    T_m * term ≤ C_delta * eta * F_m := by
  have hT_le : T_m ≤ C_delta * F_m :=
    terminal_weight_le_const_mul hdelta_pos hdelta_le_F hT hC_delta
  have hC_delta_nonneg : 0 ≤ C_delta := by
    exact (sq_nonneg (1 + delta⁻¹)).trans hC_delta
  have hF_nonneg : 0 ≤ F_m := le_trans (le_of_lt hdelta_pos) hdelta_le_F
  have hright_nonneg : 0 ≤ C_delta * F_m :=
    mul_nonneg hC_delta_nonneg hF_nonneg
  calc
    T_m * term ≤ (C_delta * F_m) * eta :=
      mul_le_mul hT_le hterm_le hterm_nonneg hright_nonneg
    _ = C_delta * eta * F_m := by ring

/--
Source label `l.S.and.J`, equation `e.J.moment.bound`: the terminal weight
dominates the terminal contrast scale `1 + F_m = r_m^2`.
-/
theorem one_add_contrast_le_terminal_weight {T_m F_m : ℝ}
    (hF_pos : 0 < F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m) :
    1 + F_m ≤ T_m := by
  rw [hT]
  have hF_ne : F_m ≠ 0 := ne_of_gt hF_pos
  have hdiff :
      0 ≤ (1 + F_m) ^ 2 / F_m - (1 + F_m) := by
    have hdiff_eq :
        (1 + F_m) ^ 2 / F_m - (1 + F_m) = (1 + F_m) / F_m := by
      field_simp [hF_ne]
      ring
    rw [hdiff_eq]
    positivity
  linarith

/--
Source label `p.HC.CR`: scalar absorption for the raw cutoff geometric tail.
Once the two-beta coefficient has been made at most `decay`, the terminal
weight pays the remaining contrast factor.
-/
theorem cutoff_contrast_geo_le_decay_terminal_weight
    {A geom F_m decay T_m : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hcoeff : A * geom ≤ decay)
    (hgeom_nonneg : 0 ≤ geom)
    (hF_pos : 0 < F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m) :
    A * (geom * F_m) ≤ decay * T_m := by
  have hF_le_T : F_m ≤ T_m := by
    have hle := one_add_contrast_le_terminal_weight hF_pos hT
    linarith
  have hT_nonneg : 0 ≤ T_m := by
    linarith [hF_pos, hF_le_T]
  have hAgeom_nonneg : 0 ≤ A * geom := mul_nonneg hA_nonneg hgeom_nonneg
  calc
    A * (geom * F_m) = (A * geom) * F_m := by ring
    _ ≤ (A * geom) * T_m :=
        mul_le_mul_of_nonneg_left hF_le_T hAgeom_nonneg
    _ ≤ decay * T_m :=
        mul_le_mul_of_nonneg_right hcoeff hT_nonneg

/--
Source label `e.drift.nodrop`: finite weighted-square form of the deterministic
drift estimate on a no-drop window.
-/
theorem weighted_drift_square_bound {ι : Type*} (s : Finset ι)
    {w D : ι → ℝ} {T_m C Cw rho F_m : ℝ}
    (hT_pos : 0 < T_m)
    (hC_nonneg : 0 ≤ C)
    (hF_nonneg : 0 ≤ F_m)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hDsq : ∀ i ∈ s, D i ^ 2 ≤ C * rho ^ 2 * F_m / T_m)
    (hCw : ∑ i ∈ s, w i ≤ Cw) :
    T_m * (∑ i ∈ s, w i * D i ^ 2) ≤ C * Cw * rho ^ 2 * F_m := by
  have hterm_nonneg : 0 ≤ C * rho ^ 2 * F_m / T_m := by
    positivity
  have hsum_bound :
      ∑ i ∈ s, w i * D i ^ 2 ≤
        (∑ i ∈ s, w i) * (C * rho ^ 2 * F_m / T_m) := by
    calc
      ∑ i ∈ s, w i * D i ^ 2
          ≤ ∑ i ∈ s, w i * (C * rho ^ 2 * F_m / T_m) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact mul_le_mul_of_nonneg_left (hDsq i hi) (hw_nonneg i hi)
      _ = (∑ i ∈ s, w i) * (C * rho ^ 2 * F_m / T_m) := by
              rw [Finset.sum_mul]
  have hsum_le_Cw :
      (∑ i ∈ s, w i) * (C * rho ^ 2 * F_m / T_m) ≤
        Cw * (C * rho ^ 2 * F_m / T_m) :=
    mul_le_mul_of_nonneg_right hCw hterm_nonneg
  have hscaled :
      T_m * (∑ i ∈ s, w i * D i ^ 2) ≤
        T_m * (Cw * (C * rho ^ 2 * F_m / T_m)) :=
    mul_le_mul_of_nonneg_left (le_trans hsum_bound hsum_le_Cw) (le_of_lt hT_pos)
  calc
    T_m * (∑ i ∈ s, w i * D i ^ 2)
        ≤ T_m * (Cw * (C * rho ^ 2 * F_m / T_m)) := hscaled
    _ = C * Cw * rho ^ 2 * F_m := by
        field_simp [ne_of_gt hT_pos]

end Homogenization.HighContrast.EntryScale
