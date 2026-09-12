/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedMomentRepair
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The five-row rank repair on an unaltered power-law patch

For `V(R) = C R^(-1 - 2 lam)` and `G = 0`, the five linear rows of
the manuscript are solved by two concrete smooth compactly supported functions.
The three angular and two axial powers are proved distinct when `lam > 0`.
No nonsingularity or preimage is assumed: the profiles use the constructed
localized moment inverse.
-/

@[expose] public section


noncomputable section

open scoped BigOperators ContDiff
open Set Function MeasureTheory

namespace NavierStokes.FiveRowRank

/-- The three debts, in the order `(P, Jθ, Jz)`. -/
abbrev Debt := Fin 3 → ℝ

/-- A positive mesh with unused gaps between the correction intervals. -/
def cellStep (a b : ℝ) (n : ℕ) : ℝ := (b - a) / (2 * (n : ℝ) + 1)

/-- Cell lower, given by `a + (2 * (j.val : ℝ) + 1) * cellStep a b n`. -/
def cellLower {n : ℕ} (a b : ℝ) (j : Fin n) : ℝ :=
  a + (2 * (j.val : ℝ) + 1) * cellStep a b n

/-- Cell upper, given by `a + (2 * (j.val : ℝ) + 2) * cellStep a b n`. -/
def cellUpper {n : ℕ} (a b : ℝ) (j : Fin n) : ℝ :=
  a + (2 * (j.val : ℝ) + 2) * cellStep a b n

theorem cellStep_pos (a b : ℝ) (hab : a < b) (n : ℕ) : 0 < cellStep a b n := by
  apply div_pos (sub_pos.mpr hab)
  positivity

theorem cellStep_mul (a b : ℝ) (n : ℕ) :
    (2 * (n : ℝ) + 1) * cellStep a b n = b - a := by
  unfold cellStep
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem cellLower_gt {n : ℕ} (a b : ℝ) (hab : a < b) (j : Fin n) :
    a < cellLower a b j := by
  have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hd := cellStep_pos a b hab n
  unfold cellLower
  nlinarith

theorem cell_lower_lt_upper {n : ℕ} (a b : ℝ) (hab : a < b) (j : Fin n) :
    cellLower a b j < cellUpper a b j := by
  have hd := cellStep_pos a b hab n
  unfold cellLower cellUpper
  nlinarith

theorem cellUpper_lt {n : ℕ} (a b : ℝ) (hab : a < b) (j : Fin n) :
    cellUpper a b j < b := by
  have hj : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  have hd := cellStep_pos a b hab n
  have hm := cellStep_mul a b n
  unfold cellUpper
  nlinarith

theorem cell_separated {n : ℕ} (a b : ℝ) (hab : a < b)
    (i j : Fin n) (hij : i < j) : cellUpper a b i ≤ cellLower a b j := by
  have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  have hd := cellStep_pos a b hab n
  unfold cellUpper cellLower
  nlinarith

theorem cell_positive {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (j : Fin n) : 0 < cellLower a b j :=
  ha.trans (cellLower_gt a b hab j)

theorem cell_union_subset {n : ℕ} (a b : ℝ) (hab : a < b) :
    (⋃ j : Fin n, Ioo (cellLower a b j) (cellUpper a b j)) ⊆ Ioo a b := by
  intro R hR
  obtain ⟨j, hj⟩ := mem_iUnion.mp hR
  exact ⟨(cellLower_gt a b hab j).trans hj.1, hj.2.trans (cellUpper_lt a b hab j)⟩

/-- Angular powers, given by `![2, -2 - 2 * lam, -2 * lam]`. -/
def angularPowers (lam : ℝ) : Fin 3 → ℝ := ![2, -2 - 2 * lam, -2 * lam]
/-- Axial powers, given by `![1, 1 - 2 * lam]`. -/
def axialPowers (lam : ℝ) : Fin 2 → ℝ := ![1, 1 - 2 * lam]

theorem angularPowers_injective (lam : ℝ) (hlam : 0 < lam) : Injective (angularPowers lam) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [angularPowers] <;> linarith

theorem axialPowers_injective (lam : ℝ) (hlam : 0 < lam) : Injective (axialPowers lam) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [axialPowers]
  linarith

/-- Normalized angular moments, including the signs of the pressure and axial rows. -/
def angularDebt (C : ℝ) (d : Debt) : Fin 3 → ℝ := ![0, -(d 0) / (2 * C), d 2 / C]

/-- Normalized axial moments. -/
def axialDebt (C : ℝ) (d : Debt) : Fin 2 → ℝ := ![0, -(d 1) / C]

/-- The angular increment `∆v_m`, constructed from three separated smooth bumps. -/
def deltaV (lam C a b : ℝ) (d : Debt) : ℝ → ℝ :=
  LocalizedMomentRepair.repair (angularPowers lam) (cellLower a b) (cellUpper a b)
    (angularDebt C d)

/-- The desired axial increment `γ_d`, constructed from two separated smooth bumps. -/
def gamma (lam C a b : ℝ) (d : Debt) : ℝ → ℝ :=
  LocalizedMomentRepair.repair (axialPowers lam) (cellLower a b) (cellUpper a b)
    (axialDebt C d)

/-- The unaltered power-law angular mean on the repair patch. -/
def background (lam C R : ℝ) : ℝ := C * R ^ (-1 - 2 * lam)

theorem deltaV_contDiff (lam C a b : ℝ) (d : Debt) : ContDiff ℝ ∞ (deltaV lam C a b d) :=
  LocalizedMomentRepair.repair_contDiff _ _ _ _

theorem gamma_contDiff (lam C a b : ℝ) (d : Debt) : ContDiff ℝ ∞ (gamma lam C a b d) :=
  LocalizedMomentRepair.repair_contDiff _ _ _ _

theorem deltaV_hasCompactSupport (lam C a b : ℝ) (d : Debt) (hab : a < b) :
    HasCompactSupport (deltaV lam C a b d) :=
  LocalizedMomentRepair.repair_hasCompactSupport _ _ _ _ (cell_lower_lt_upper a b hab)

theorem gamma_hasCompactSupport (lam C a b : ℝ) (d : Debt) (hab : a < b) :
    HasCompactSupport (gamma lam C a b d) :=
  LocalizedMomentRepair.repair_hasCompactSupport _ _ _ _ (cell_lower_lt_upper a b hab)

theorem deltaV_tsupport_subset (lam C a b : ℝ) (d : Debt) (hab : a < b) :
    tsupport (deltaV lam C a b d) ⊆ Ioo a b :=
  (LocalizedMomentRepair.repair_tsupport_subset_open _ _ _ _
    (cell_lower_lt_upper a b hab)).trans (cell_union_subset a b hab)

theorem gamma_tsupport_subset (lam C a b : ℝ) (d : Debt) (hab : a < b) :
    tsupport (gamma lam C a b d) ⊆ Ioo a b :=
  (LocalizedMomentRepair.repair_tsupport_subset_open _ _ _ _
    (cell_lower_lt_upper a b hab)).trans (cell_union_subset a b hab)

theorem deltaV_eq_zero_of_not_mem (lam C a b : ℝ) (d : Debt) (hab : a < b)
    {R : ℝ} (hR : R ∉ Ioo a b) : deltaV lam C a b d R = 0 := by
  by_contra hn
  exact hR (deltaV_tsupport_subset lam C a b d hab (subset_closure hn))

theorem gamma_eq_zero_of_not_mem (lam C a b : ℝ) (d : Debt) (hab : a < b)
    {R : ℝ} (hR : R ∉ Ioo a b) : gamma lam C a b d R = 0 := by
  by_contra hn
  exact hR (gamma_tsupport_subset lam C a b d hab (subset_closure hn))

theorem angular_moments (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) (i : Fin 3) :
    (∫ R, R ^ angularPowers lam i * deltaV lam C a b d R) = angularDebt C d i :=
  LocalizedMomentRepair.repair_exact _ _ _ _ (angularPowers_injective lam hlam)
    (cell_positive a b ha hab) (cell_lower_lt_upper a b hab) (cell_separated a b hab) i

theorem axial_moments (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) (i : Fin 2) :
    (∫ R, R ^ axialPowers lam i * gamma lam C a b d R) = axialDebt C d i :=
  LocalizedMomentRepair.repair_exact _ _ _ _ (axialPowers_injective lam hlam)
    (cell_positive a b ha hab) (cell_lower_lt_upper a b hab) (cell_separated a b hab) i

theorem angular_mass_zero (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) : (∫ R, R ^ (2 : ℕ) * deltaV lam C a b d R) = 0 := by
  simpa [angularPowers, angularDebt, Real.rpow_natCast] using
    angular_moments lam C a b d hlam ha hab 0

theorem axial_mass_zero (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) : (∫ R, R * gamma lam C a b d R) = 0 := by
  simpa [axialPowers, axialDebt] using axial_moments lam C a b d hlam ha hab 0

theorem pressure_weight (lam C R : ℝ) (hR : 0 < R) :
    2 * background lam C R / R = (2 * C) * R ^ (-2 - 2 * lam) := by
  have hp : R ^ (-2 - 2 * lam) = R ^ (-1 - 2 * lam) / R := by
    rw [show -2 - 2 * lam = (-1 - 2 * lam) - 1 by ring, Real.rpow_sub hR, Real.rpow_one]
  rw [hp, background]
  ring

theorem angular_weight (lam C R : ℝ) (hR : 0 < R) :
    R ^ (2 : ℕ) * background lam C R = C * R ^ (1 - 2 * lam) := by
  have hp : R ^ (1 - 2 * lam) = R ^ (2 : ℕ) * R ^ (-1 - 2 * lam) := by
    rw [show 1 - 2 * lam = (2 : ℝ) + (-1 - 2 * lam) by ring, Real.rpow_add hR]
    norm_num
  rw [hp, background]
  ring

theorem axial_weight (lam C R : ℝ) (hR : 0 < R) :
    -(R * background lam C R) = (-C) * R ^ (-2 * lam) := by
  have hp : R ^ (-2 * lam) = R * R ^ (-1 - 2 * lam) := by
    rw [show -2 * lam = (1 : ℝ) + (-1 - 2 * lam) by ring, Real.rpow_add hR, Real.rpow_one]
  rw [hp, background]
  ring

theorem pressure_row (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    (∫ R, (2 * background lam C R / R) * deltaV lam C a b d R) = -(d 0) := by
  have hi : (fun R => (2 * background lam C R / R) * deltaV lam C a b d R) =
      (fun R => (2 * C) * (R ^ (-2 - 2 * lam) * deltaV lam C a b d R)) := by
    funext R
    by_cases hR : 0 < R
    · rw [pressure_weight lam C R hR, mul_assoc]
    · have hz := deltaV_eq_zero_of_not_mem lam C a b d hab
        (show R ∉ Ioo a b from fun h => hR (ha.trans h.1))
      simp only [hz, mul_zero]
  rw [hi, integral_const_mul]
  have hm := angular_moments lam C a b d hlam ha hab 1
  simp only [angularPowers, neg_mul, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      angularDebt] at hm
  rw [hm]
  field_simp

theorem angular_row (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    (∫ R, (R ^ (2 : ℕ) * background lam C R) * gamma lam C a b d R) = -(d 1) := by
  have hi : (fun R => (R ^ (2 : ℕ) * background lam C R) * gamma lam C a b d R) =
      (fun R => C * (R ^ (1 - 2 * lam) * gamma lam C a b d R)) := by
    funext R
    by_cases hR : 0 < R
    · rw [angular_weight lam C R hR, mul_assoc]
    · have hz := gamma_eq_zero_of_not_mem lam C a b d hab
        (show R ∉ Ioo a b from fun h => hR (ha.trans h.1))
      simp only [hz, mul_zero]
  rw [hi, integral_const_mul]
  have hm := axial_moments lam C a b d hlam ha hab 1
  simp only [axialPowers, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, axialDebt]
      at hm
  rw [hm]
  field_simp

theorem axial_row (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    (∫ R, -(R * background lam C R) * deltaV lam C a b d R) = -(d 2) := by
  have hi : (fun R => -(R * background lam C R) * deltaV lam C a b d R) =
      (fun R => (-C) * (R ^ (-2 * lam) * deltaV lam C a b d R)) := by
    funext R
    by_cases hR : 0 < R
    · rw [axial_weight lam C R hR, mul_assoc]
    · have hz := deltaV_eq_zero_of_not_mem lam C a b d hab
        (show R ∉ Ioo a b from fun h => hR (ha.trans h.1))
      simp only [hz, mul_zero]
  rw [hi, integral_const_mul]
  have hm : (∫ R, R ^ (-2 * lam) * deltaV lam C a b d R) = d 2 / C :=
    angular_moments lam C a b d hlam ha hab 2
  rw [hm]
  field_simp

/-- The five linear equations (35), retaining the general background fields. -/
def FiveRows (V G : ℝ → ℝ) (d : Debt) (dv ga : ℝ → ℝ) : Prop :=
  (∫ R, R ^ (2 : ℕ) * dv R) = 0 ∧
  (∫ R, R * ga R) = 0 ∧
  (∫ R, (2 * V R / R) * dv R) = -(d 0) ∧
  (∫ R, R ^ (2 : ℕ) * (G R * dv R + V R * ga R)) = -(d 1) ∧
  (∫ R, 2 * R * G R * ga R - R * V R * dv R) = -(d 2)

/-- Only the values of the background fields on the patch are used. -/
theorem five_rows_on_patch (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) (V G : ℝ → ℝ)
    (hV : ∀ R ∈ Ioo a b, V R = background lam C R)
    (hG : ∀ R ∈ Ioo a b, G R = 0) :
    FiveRows V G d (deltaV lam C a b d) (gamma lam C a b d) := by
  refine ⟨angular_mass_zero lam C a b d hlam ha hab,
    axial_mass_zero lam C a b d hlam ha hab, ?_, ?_, ?_⟩
  · rw [← pressure_row lam C a b d hlam hC ha hab]
    apply integral_congr_ae
    filter_upwards [] with R
    by_cases hR : R ∈ Ioo a b
    · rw [hV R hR]
    · simp only [deltaV_eq_zero_of_not_mem lam C a b d hab hR, mul_zero]
  · rw [← angular_row lam C a b d hlam hC ha hab]
    apply integral_congr_ae
    filter_upwards [] with R
    by_cases hR : R ∈ Ioo a b
    · rw [hV R hR, hG R hR]
      ring
    · simp only [deltaV_eq_zero_of_not_mem lam C a b d hab hR,
        gamma_eq_zero_of_not_mem lam C a b d hab hR, mul_zero, add_zero]
  · rw [← axial_row lam C a b d hlam hC ha hab]
    apply integral_congr_ae
    filter_upwards [] with R
    by_cases hR : R ∈ Ioo a b
    · rw [hV R hR, hG R hR]
      ring
    · simp only [deltaV_eq_zero_of_not_mem lam C a b d hab hR,
        gamma_eq_zero_of_not_mem lam C a b d hab hR, mul_zero, sub_zero]

/-- In particular the concrete unaltered background supports all five rows. -/
theorem five_rows (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    FiveRows (background lam C) (fun _ => 0) d
      (deltaV lam C a b d) (gamma lam C a b d) :=
  five_rows_on_patch lam C a b d hlam hC ha hab _ _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem integrable_power_mul_of_patch (p a b : ℝ) (f : ℝ → ℝ) (ha : 0 < a)
    (hf : Continuous f) (hs : support f ⊆ Ioo a b) :
    Integrable (fun R => R ^ p * f R) := by
  have hprod : support (fun R => R ^ p * f R) ⊆ Icc a b := by
    intro R hR
    have hne : f R ≠ 0 := by intro hz; exact hR (by simp [hz])
    exact Ioo_subset_Icc_self (hs hne)
  apply (integrableOn_iff_integrable_of_support_subset hprod).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ hf.continuousOn
  apply continuousOn_id.rpow_const
  intro R hR
  exact Or.inl (ne_of_gt (lt_of_lt_of_le ha hR.1))

theorem deltaV_power_integrable (lam C a b p : ℝ) (d : Debt)
    (ha : 0 < a) (hab : a < b) : Integrable (fun R => R ^ p * deltaV lam C a b d R) :=
  integrable_power_mul_of_patch p a b _ ha (deltaV_contDiff lam C a b d).continuous
    (subset_closure.trans (deltaV_tsupport_subset lam C a b d hab))

theorem gamma_power_integrable (lam C a b p : ℝ) (d : Debt)
    (ha : 0 < a) (hab : a < b) : Integrable (fun R => R ^ p * gamma lam C a b d R) :=
  integrable_power_mul_of_patch p a b _ ha (gamma_contDiff lam C a b d).continuous
    (subset_closure.trans (gamma_tsupport_subset lam C a b d hab))

/-- The complete existence statement has no moment-rank assumption. -/
theorem exists_five_row_repair (lam C a b : ℝ) (d : Debt) (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) (V G : ℝ → ℝ)
    (hV : ∀ R ∈ Ioo a b, V R = background lam C R)
    (hG : ∀ R ∈ Ioo a b, G R = 0) :
    ∃ dv ga : ℝ → ℝ,
      ContDiff ℝ ∞ dv ∧ ContDiff ℝ ∞ ga ∧
      HasCompactSupport dv ∧ HasCompactSupport ga ∧
      tsupport dv ⊆ Ioo a b ∧ tsupport ga ⊆ Ioo a b ∧ FiveRows V G d dv ga :=
  ⟨deltaV lam C a b d, gamma lam C a b d,
    deltaV_contDiff lam C a b d, gamma_contDiff lam C a b d,
    deltaV_hasCompactSupport lam C a b d hab, gamma_hasCompactSupport lam C a b d hab,
    deltaV_tsupport_subset lam C a b d hab, gamma_tsupport_subset lam C a b d hab,
    five_rows_on_patch lam C a b d hlam hC ha hab V G hV hG⟩

section Linearity

/-- Angular debt linear map, bundling `toFun`, `map_add`, `map_smul`. -/
def angularDebtLinearMap (C : ℝ) : Debt →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := angularDebt C
  map_add' d e := by
    ext i
    fin_cases i <;> simp [angularDebt, Pi.add_apply] <;> ring
  map_smul' r d := by
    ext i
    fin_cases i <;> simp [angularDebt, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Axial debt linear map, bundling `toFun`, `map_add`, `map_smul`. -/
def axialDebtLinearMap (C : ℝ) : Debt →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := axialDebt C
  map_add' d e := by
    ext i
    fin_cases i <;> simp [axialDebt, Pi.add_apply]
    ring
  map_smul' r d := by
    ext i
    fin_cases i <;> simp [axialDebt, Pi.smul_apply, smul_eq_mul]
    ring

/-- The concrete angular correction as a linear map in `(P,Jθ,Jz)`. -/
def deltaVLinearMap (lam C a b : ℝ) : Debt →ₗ[ℝ] (ℝ → ℝ) :=
  (LocalizedMomentRepair.repairLinearMap (angularPowers lam) (cellLower a b) (cellUpper a b)).comp
    (angularDebtLinearMap C)

/-- The concrete axial correction as a linear map in `(P,Jθ,Jz)`. -/
def gammaLinearMap (lam C a b : ℝ) : Debt →ₗ[ℝ] (ℝ → ℝ) :=
  (LocalizedMomentRepair.repairLinearMap (axialPowers lam) (cellLower a b) (cellUpper a b)).comp
    (axialDebtLinearMap C)

@[simp] theorem deltaVLinearMap_apply (lam C a b : ℝ) (d : Debt) :
    deltaVLinearMap lam C a b d = deltaV lam C a b d := rfl

@[simp] theorem gammaLinearMap_apply (lam C a b : ℝ) (d : Debt) :
    gammaLinearMap lam C a b d = gamma lam C a b d := rfl

theorem deltaV_add (lam C a b : ℝ) (d e : Debt) :
    deltaV lam C a b (d + e) = deltaV lam C a b d + deltaV lam C a b e :=
  (deltaVLinearMap lam C a b).map_add d e

theorem gamma_add (lam C a b : ℝ) (d e : Debt) :
    gamma lam C a b (d + e) = gamma lam C a b d + gamma lam C a b e :=
  (gammaLinearMap lam C a b).map_add d e

theorem deltaV_smul (lam C a b r : ℝ) (d : Debt) :
    deltaV lam C a b (r • d) = r • deltaV lam C a b d :=
  (deltaVLinearMap lam C a b).map_smul r d

theorem gamma_smul (lam C a b r : ℝ) (d : Debt) :
    gamma lam C a b (r • d) = r • gamma lam C a b d :=
  (gammaLinearMap lam C a b).map_smul r d

@[simp] theorem deltaV_zero (lam C a b : ℝ) : deltaV lam C a b 0 = 0 :=
  (deltaVLinearMap lam C a b).map_zero

@[simp] theorem gamma_zero (lam C a b : ℝ) : gamma lam C a b 0 = 0 :=
  (gammaLinearMap lam C a b).map_zero

theorem angularDebt_rescale (C : ℝ) (d : Debt) :
    angularDebt C d = C⁻¹ • angularDebt 1 d := by
  ext i
  fin_cases i <;>
    simp [angularDebt, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_inv_rev] <;> ring

theorem axialDebt_rescale (C : ℝ) (d : Debt) : axialDebt C d = C⁻¹ • axialDebt 1 d := by
  ext i
  fin_cases i <;>
    simp [axialDebt, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem deltaV_rescale (lam C a b : ℝ) (d : Debt) :
    deltaV lam C a b d = C⁻¹ • deltaV lam 1 a b d := by
  unfold deltaV
  rw [angularDebt_rescale]
  exact LocalizedMomentRepair.repair_smul _ _ _ _ _

theorem gamma_rescale (lam C a b : ℝ) (d : Debt) :
    gamma lam C a b d = C⁻¹ • gamma lam 1 a b d := by
  unfold gamma
  rw [axialDebt_rescale]
  exact LocalizedMomentRepair.repair_smul _ _ _ _ _

end Linearity

section JetBounds

theorem angularDebt_one_norm (d : Debt) : ‖angularDebt 1 d‖ ≤ ‖d‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
  intro i
  fin_cases i
  · simp [angularDebt]
  · change ‖-(d 0) / (2 * 1 : ℝ)‖ ≤ ‖d‖
    have hd : |d 0| ≤ ‖d‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm d 0
    rw [norm_div, norm_neg]
    norm_num
    nlinarith [abs_nonneg (d 0)]
  · simpa [angularDebt] using norm_le_pi_norm d 2

theorem axialDebt_one_norm (d : Debt) : ‖axialDebt 1 d‖ ≤ ‖d‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
  intro i
  fin_cases i
  · simp [axialDebt]
  · simpa [axialDebt] using norm_le_pi_norm d 1

/-- The normalization loses at most the explicit factor `‖C⁻¹‖`. -/
theorem angularDebt_norm_le (C : ℝ) (d : Debt) : ‖angularDebt C d‖ ≤ ‖C⁻¹‖ * ‖d‖ := by
  rw [angularDebt_rescale, norm_smul]
  exact mul_le_mul_of_nonneg_left (angularDebt_one_norm d) (norm_nonneg _)

theorem axialDebt_norm_le (C : ℝ) (d : Debt) : ‖axialDebt C d‖ ≤ ‖C⁻¹‖ * ‖d‖ := by
  rw [axialDebt_rescale, norm_smul]
  exact mul_le_mul_of_nonneg_left (axialDebt_one_norm d) (norm_nonneg _)

/-- Every prescribed finite spatial jet is bounded linearly in the debt, uniformly in
space. The geometric constant is independent of the nonzero amplitude `C`; all
amplitude dependence is the displayed inverse factor. -/
theorem finite_jet_bound (lam a b : ℝ) (hab : a < b) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (k : ℕ), k ≤ N → ∀ (d e : Debt) (R : ℝ),
      |iteratedDeriv k (deltaV lam C a b d) R - iteratedDeriv k (deltaV lam C a b e) R| +
      |iteratedDeriv k (gamma lam C a b d) R - iteratedDeriv k (gamma lam C a b e) R| ≤
        K * ‖C⁻¹‖ * ‖d - e‖ := by
  obtain ⟨Kv, hKv, hv⟩ := LocalizedMomentRepair.repair_finite_jet_bound
    (angularPowers lam) (cellLower a b) (cellUpper a b) (cell_lower_lt_upper a b hab) N
  obtain ⟨Kg, hKg, hg⟩ := LocalizedMomentRepair.repair_finite_jet_bound
    (axialPowers lam) (cellLower a b) (cellUpper a b) (cell_lower_lt_upper a b hab) N
  refine ⟨Kv + Kg, add_nonneg hKv hKg, ?_⟩
  intro C k hk d e R
  have hvd : ‖angularDebt C d - angularDebt C e‖ ≤ ‖C⁻¹‖ * ‖d - e‖ := by
    have hs : angularDebt C (d - e) = angularDebt C d - angularDebt C e :=
      (angularDebtLinearMap C).map_sub d e
    rw [← hs]
    exact angularDebt_norm_le C (d - e)
  have hgd : ‖axialDebt C d - axialDebt C e‖ ≤ ‖C⁻¹‖ * ‖d - e‖ := by
    have hs : axialDebt C (d - e) = axialDebt C d - axialDebt C e :=
      (axialDebtLinearMap C).map_sub d e
    rw [← hs]
    exact axialDebt_norm_le C (d - e)
  calc
    _ ≤ Kv * ‖angularDebt C d - angularDebt C e‖ + Kg * ‖axialDebt C d - axialDebt C e‖ :=
      add_le_add (hv k hk _ _ R) (hg k hk _ _ R)
    _ ≤ Kv * (‖C⁻¹‖ * ‖d - e‖) + Kg * (‖C⁻¹‖ * ‖d - e‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hvd hKv) (mul_le_mul_of_nonneg_left hgd hKg)
    _ = (Kv + Kg) * ‖C⁻¹‖ * ‖d - e‖ := by ring

/-- If the amplitude stays a positive distance from zero, the finite-jet estimate
has a single constant valid for all amplitudes in that range. -/
theorem uniform_finite_jet_bound (lam a b η : ℝ) (hab : a < b) (hη : 0 < η) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ), η ≤ |C| → ∀ (k : ℕ), k ≤ N →
      ∀ (d e : Debt) (R : ℝ),
      |iteratedDeriv k (deltaV lam C a b d) R - iteratedDeriv k (deltaV lam C a b e) R| +
      |iteratedDeriv k (gamma lam C a b d) R - iteratedDeriv k (gamma lam C a b e) R| ≤
        K * ‖d - e‖ := by
  obtain ⟨K, hK, hbound⟩ := finite_jet_bound lam a b hab N
  refine ⟨K / η, div_nonneg hK hη.le, ?_⟩
  intro C hC k hk d e R
  apply (hbound C k hk d e R).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hinv : ‖C⁻¹‖ ≤ η⁻¹ := by
    rw [norm_inv, Real.norm_eq_abs]
    exact inv_anti₀ hη hC
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hK

end JetBounds

section SmoothParameters

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth debts give joint smoothness of a fixed localized repair in the
parameter and spatial variables. This uses the actual finite coordinate family. -/
theorem repair_joint_contDiffOn {n : ℕ} (a l u : Fin n → ℝ) {S : Set E}
    {d : E → Fin n → ℝ} (hd : ContDiffOn ℝ ∞ d S) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => LocalizedMomentRepair.repair a l u (d z.1) z.2)
      (S ×ˢ univ) := by
  have hfun : (fun z : E × ℝ => LocalizedMomentRepair.repair a l u (d z.1) z.2) =
      (fun z : E × ℝ => ∑ j, d z.1 j *
        LocalizedMomentRepair.repair a l u (Pi.single j 1) z.2) := by
    funext z
    exact congrFun (LocalizedMomentRepair.repair_eq_sum_coordinate a l u (d z.1)) z.2
  rw [hfun]
  apply ContDiffOn.sum
  intro j _
  exact ((contDiffOn_pi.mp hd j).comp contDiffOn_fst (fun _ hz => hz.1)).mul
    ((LocalizedMomentRepair.repair_contDiff a l u (Pi.single j 1)).comp contDiff_snd).contDiffOn

theorem angularDebt_contDiffOn {S : Set E} {C : E → ℝ} {d : E → Debt}
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => angularDebt (C p) (d p)) S := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun p => -(d p 0) / (2 * C p)) S
    exact (contDiffOn_pi.mp hd 0).neg.div (contDiffOn_const.mul hC)
      (fun p hp => mul_ne_zero (by norm_num) (hCn p hp))
  · change ContDiffOn ℝ ∞ (fun p => d p 2 / C p) S
    exact (contDiffOn_pi.mp hd 2).div hC hCn

theorem axialDebt_contDiffOn {S : Set E} {C : E → ℝ} {d : E → Debt}
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => axialDebt (C p) (d p)) S := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const
  · change ContDiffOn ℝ ∞ (fun p => -(d p 1) / C p) S
    exact (contDiffOn_pi.mp hd 1).neg.div hC hCn

/-- Joint smoothness in every auxiliary parameter and the radial coordinate,
for any smooth nonvanishing amplitude and smooth debt vector. -/
theorem deltaV_joint_contDiffOn (lam a b : ℝ) {S : Set E} {C : E → ℝ} {d : E → Debt}
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => deltaV lam (C z.1) a b (d z.1) z.2)
      (S ×ˢ univ) :=
  repair_joint_contDiffOn (E := E) (n := 3)
    (angularPowers lam) (cellLower a b) (cellUpper a b)
    (S := S) (d := fun p => angularDebt (C p) (d p))
    (angularDebt_contDiffOn (E := E) (S := S) (C := C) (d := d) hC hd hCn)

theorem gamma_joint_contDiffOn (lam a b : ℝ) {S : Set E} {C : E → ℝ} {d : E → Debt}
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => gamma lam (C z.1) a b (d z.1) z.2)
      (S ×ˢ univ) :=
  repair_joint_contDiffOn (E := E) (n := 2)
    (axialPowers lam) (cellLower a b) (cellUpper a b)
    (S := S) (d := fun p => axialDebt (C p) (d p))
    (axialDebt_contDiffOn (E := E) (S := S) (C := C) (d := d) hC hd hCn)

theorem repair_pair_joint_contDiffOn (lam a b : ℝ) {S : Set E} {C : E → ℝ} {d : E → Debt}
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ =>
      (deltaV lam (C z.1) a b (d z.1) z.2, gamma lam (C z.1) a b (d z.1) z.2))
      (S ×ˢ univ) :=
  (deltaV_joint_contDiffOn lam a b hC hd hCn).prodMk
    (gamma_joint_contDiffOn lam a b hC hd hCn)

end SmoothParameters

end NavierStokes.FiveRowRank
