/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliStandardScalar

/-! # Coarse Caccioppoli Scale Zero Budget Envelopes -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli budget envelopes

This file contains the dimension-only budget envelopes and explicit
scale-zero bridge constants used by the scalar Caccioppoli envelope.

## Audit tag

Claim: bound all unit-scale boundary and centered-interior alpha/cross/local
budgets by dimension-only envelopes.

Downstream target: `CoarseCaccioppoliScaleZeroScalarBounds.lean`.  This file
should contain scalar envelope arithmetic only, not public package constructors.
-/

noncomputable section

open scoped ENNReal

/-- Dimension-only cross/local budget envelope for the scale-zero boundary
local-patch route. -/
noncomputable def boundaryScaleZeroCrossBudgetEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Clocal : ℝ := coarseCaccioppoliLocalPatchBufferedLocalBudget Q0 Csol
  max 1 ((81 : ℝ) * 9 * Clocal)

/-- Dimension-only cross/local budget envelope for the scale-zero centered
interior route. -/
noncomputable def interiorScaleZeroCrossBudgetEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q0 Csol
  max 1 ((81 : ℝ) * 3 * Clocal)

private theorem localPatchBufferedLocalBudget_unit_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤
      coarseCaccioppoliLocalPatchBufferedLocalBudget (originCube d 0)
        (fullVectorPoincareCubeConstant (originCube d 0)) := by
  unfold coarseCaccioppoliLocalPatchBufferedLocalBudget
  exact le_trans zero_le_one (le_max_left _ _)

private theorem bufferedLocalBudget_unit_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤
      coarseCaccioppoliBufferedLocalBudget (originCube d 0)
        (fullVectorPoincareCubeConstant (originCube d 0)) := by
  unfold coarseCaccioppoliBufferedLocalBudget
  exact le_trans zero_le_one (le_max_left _ _)

private theorem localPatchBufferedCrossBudgetUnit_le_envelope
    {d : ℕ} [NeZero d] {s : ℝ} (hs_le : s ≤ 1) :
    coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s ≤
      boundaryScaleZeroCrossBudgetEnvelope d := by
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Clocal : ℝ := coarseCaccioppoliLocalPatchBufferedLocalBudget Q0 Csol
  have hClocal_nonneg : 0 ≤ Clocal := by
    dsimp [Clocal, Csol, Q0]
    exact localPatchBufferedLocalBudget_unit_nonneg d
  have hpow : Real.rpow (3 : ℝ) (2 * s) ≤ 9 := by
    calc
      Real.rpow (3 : ℝ) (2 * s) ≤ Real.rpow (3 : ℝ) 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by nlinarith)
      _ = 9 := by norm_num
  have hterm :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) * Clocal ≤
        (81 : ℝ) * 9 * Clocal := by
    have hmul := mul_le_mul_of_nonneg_right hpow hClocal_nonneg
    have hmul' :=
      mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 81)
    simpa [mul_assoc] using hmul'
  unfold coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit
    coarseCaccioppoliLocalPatchBufferedCrossBudget
    boundaryScaleZeroCrossBudgetEnvelope
  dsimp [Q0, Csol, Clocal]
  exact max_le (le_max_left _ _) (hterm.trans (le_max_right _ _))

private theorem bufferedCrossBudgetUnit_le_envelope
    {d : ℕ} [NeZero d] {s : ℝ} (hs_le : s ≤ 1) :
    coarseCaccioppoliBufferedCrossBudgetUnit d s ≤
      interiorScaleZeroCrossBudgetEnvelope d := by
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q0 Csol
  have hClocal_nonneg : 0 ≤ Clocal := by
    dsimp [Clocal, Csol, Q0]
    exact bufferedLocalBudget_unit_nonneg d
  have hpow : Real.rpow (3 : ℝ) s ≤ 3 := by
    calc
      Real.rpow (3 : ℝ) s ≤ Real.rpow (3 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          hs_le
      _ = 3 := by norm_num
  have hterm :
      (81 : ℝ) * Real.rpow (3 : ℝ) s * Clocal ≤
        (81 : ℝ) * 3 * Clocal := by
    have hmul := mul_le_mul_of_nonneg_right hpow hClocal_nonneg
    have hmul' :=
      mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 81)
    simpa [mul_assoc] using hmul'
  unfold coarseCaccioppoliBufferedCrossBudgetUnit
    coarseCaccioppoliBufferedCrossBudget
    interiorScaleZeroCrossBudgetEnvelope
  dsimp [Q0, Csol, Clocal]
  exact max_le (le_max_left _ _) (hterm.trans (le_max_right _ _))

private theorem old_inv_geometricDiscount_le_five_inv {s p : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) :
    (Homogenization.geometricDiscount s p)⁻¹ ≤ 5 * s⁻¹ := by
  have h := Ch02.inv_geometricDiscount_le_five_inv
    (s := s) (p := p) hs hs_le hp
  simpa [Ch02.geometricDiscount_eq_old] using h

private theorem sqrt_inv_one_sub_rpow_three_two_mul_sub_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) ≤
      5 * (1 - s)⁻¹ := by
  let u : ℝ := 1 - s
  let R : ℝ := 5 * u⁻¹
  have hu_pos : 0 < u := by
    dsimp [u]
    linarith
  have hu_le : u ≤ 1 := by
    dsimp [u]
    linarith
  have hdisc_inv :
      (Homogenization.geometricDiscount u 2)⁻¹ ≤ R := by
    dsimp [R]
    exact old_inv_geometricDiscount_le_five_inv hu_pos hu_le
      (by norm_num : (1 : ℝ) ≤ 2)
  have hgeom_eq :
      Homogenization.geometricDiscount u 2 =
        1 - Real.rpow (3 : ℝ) (2 * (s - 1)) := by
    unfold Homogenization.geometricDiscount
    dsimp [u]
    congr 1
    ring_nf
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hR_ge_one : 1 ≤ R := by
    have hinv_ge_one : 1 ≤ u⁻¹ := (one_le_inv₀ hu_pos).2 hu_le
    dsimp [R]
    nlinarith
  have hR_le_sq : R ≤ R ^ (2 : ℕ) := by
    nlinarith [sq_nonneg R, hR_ge_one]
  rw [Real.sqrt_le_iff]
  constructor
  · simpa [R, u] using hR_nonneg
  · calc
      (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹
          = (Homogenization.geometricDiscount u 2)⁻¹ := by rw [hgeom_eq]
      _ ≤ R := hdisc_inv
      _ ≤ R ^ (2 : ℕ) := hR_le_sq
      _ = (5 * (1 - s)⁻¹) ^ (2 : ℕ) := by rfl

private theorem rpow_three_d_add_s_le_d_add_one
    (d : ℕ) {s : ℝ} (hs_le : s ≤ 1) :
    Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
      Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) (by linarith)

private theorem inv_mul_self_one_sub_le_one {s : ℝ}
    (hs : 0 < s) (_hs_le : s ≤ 1) :
    s⁻¹ * (s * (1 - s)) ≤ 1 := by
  have hs_ne : s ≠ 0 := hs.ne'
  calc
    s⁻¹ * (s * (1 - s)) = 1 - s := by
      field_simp [hs_ne]
    _ ≤ 1 := by linarith

private theorem inv_mul_self_one_sub_le_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    s⁻¹ * (s * (1 - s)) ≤ s⁻¹ := by
  have hone_le_inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  exact (inv_mul_self_one_sub_le_one hs hs_le).trans hone_le_inv

private theorem two_endpoint_inv_mul_self_one_sub_le_inv {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    s⁻¹ * ((1 - s)⁻¹ * (s * (1 - s))) ≤ s⁻¹ := by
  have hs_ne : s ≠ 0 := hs.ne'
  have hs1_pos : 0 < 1 - s := by linarith
  have hs1_ne : 1 - s ≠ 0 := hs1_pos.ne'
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hone_le_inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  calc
    s⁻¹ * ((1 - s)⁻¹ * (s * (1 - s))) = 1 := by
      field_simp [hs_ne, hs1_ne]
    _ ≤ s⁻¹ := hone_le_inv

private noncomputable def centeredAverageFrontEnvelope
    (d : ℕ) (C : ℝ) : ℝ :=
  (d : ℝ) * (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
    ((5 : ℝ) * (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)) *
    (2 * quantitativeCubeCutoffGradientConst d)

private theorem centeredAverageFrontEnvelope_nonneg
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ centeredAverageFrontEnvelope d C := by
  have hdisc_one_pos : 0 < Homogenization.geometricDiscount (1 : ℝ) 1 := by
    exact Homogenization.geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hbase_nonneg :
      0 ≤ (3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hC) hpow_nonneg
  have hdisc_inv_nonneg :
      0 ≤ (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹ :=
    inv_nonneg.mpr hdisc_one_pos.le
  have hfactor_nonneg :
      0 ≤ (5 : ℝ) * (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹ :=
    mul_nonneg (by norm_num) hdisc_inv_nonneg
  have hcut_nonneg : 0 ≤ 2 * quantitativeCubeCutoffGradientConst d :=
    mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d)
  unfold centeredAverageFrontEnvelope
  exact mul_nonneg (mul_nonneg hd_nonneg
    (mul_nonneg hbase_nonneg hfactor_nonneg)) hcut_nonneg

private theorem centeredAverageFront_le_envelope_mul_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs_le : s ≤ 1) :
    coarseCaccioppoliCenteredAverageFront d s C ≤
      centeredAverageFrontEnvelope d C * s⁻¹ := by
  have hdisc_one_pos : 0 < Homogenization.geometricDiscount (1 : ℝ) 1 := by
    exact Homogenization.geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hdisc_s_inv :
      (Homogenization.geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
    old_inv_geometricDiscount_le_five_inv hs hs_le (by norm_num : (1 : ℝ) ≤ 1)
  have hdisc_s_pos : 0 < Homogenization.geometricDiscount s 1 := by
    exact Homogenization.geometricDiscount_pos (by simpa using hs)
  have hbase_nonneg :
      0 ≤ (3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hcut_nonneg : 0 ≤ 2 * quantitativeCubeCutoffGradientConst d := by
    exact mul_nonneg (by norm_num)
      (quantitativeCubeCutoffGradientConst_nonneg d)
  unfold coarseCaccioppoliCenteredAverageFront centeredAverageFrontEnvelope
  calc
    (d : ℝ) * (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          ((Homogenization.geometricDiscount s 1)⁻¹ *
            (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)) *
        (2 * quantitativeCubeCutoffGradientConst d)
        ≤
      (d : ℝ) * (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          ((5 * s⁻¹) *
            (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)) *
        (2 * quantitativeCubeCutoffGradientConst d) := by
          gcongr
    _ =
      ((d : ℝ) * (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          ((5 : ℝ) * (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)) *
        (2 * quantitativeCubeCutoffGradientConst d)) * s⁻¹ := by
          ring_nf

private theorem centeredAverageFront_mul_den_le_envelope_mul_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliCenteredAverageFront d s C * (s * (1 - s)) ≤
      centeredAverageFrontEnvelope d C * s⁻¹ := by
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    exact mul_nonneg hs.le (by linarith)
  have hfront :=
    centeredAverageFront_le_envelope_mul_inv d hC hs hs_le
  have hscaled :=
    mul_le_mul_of_nonneg_right hfront hden_nonneg
  have henv_nonneg : 0 ≤ centeredAverageFrontEnvelope d C :=
    centeredAverageFrontEnvelope_nonneg d hC
  calc
    coarseCaccioppoliCenteredAverageFront d s C * (s * (1 - s))
        ≤ (centeredAverageFrontEnvelope d C * s⁻¹) * (s * (1 - s)) :=
          hscaled
    _ = centeredAverageFrontEnvelope d C * (s⁻¹ * (s * (1 - s))) := by
          ring
    _ ≤ centeredAverageFrontEnvelope d C * s⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (inv_mul_self_one_sub_le_inv hs hs_le) henv_nonneg

private noncomputable def centeredHessianFrontEnvelope
    (d : ℕ) (C : ℝ) : ℝ :=
  (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
    ((5 : ℝ) *
      (2 * ((5 : ℝ) *
        (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)))) *
    (4 * quantitativeCubeCutoffHessianConst d)

private theorem centeredHessianFrontEnvelope_nonneg
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ centeredHessianFrontEnvelope d C := by
  have hdisc_one_pos : 0 < Homogenization.geometricDiscount (1 : ℝ) 1 := by
    exact Homogenization.geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hnote_nonneg :
      0 ≤ (3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hC) hpow_nonneg
  have hnote_with_disc_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹ :=
    mul_nonneg hnote_nonneg (inv_nonneg.mpr hdisc_one_pos.le)
  have hfront_nonneg :
      0 ≤ (5 : ℝ) *
        (2 * ((5 : ℝ) *
          (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
            (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹))) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num)
        (mul_nonneg (by norm_num) hnote_with_disc_nonneg))
  have hcut_nonneg : 0 ≤ 4 * quantitativeCubeCutoffHessianConst d :=
    mul_nonneg (by norm_num) (quantitativeCubeCutoffHessianConst_nonneg d)
  unfold centeredHessianFrontEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg hd_nonneg hpow_nonneg)
    hfront_nonneg) hcut_nonneg

private theorem centeredHessianFront_le_envelope_mul_endpoint_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliCenteredBesovHessianFront d s C ≤
      centeredHessianFrontEnvelope d C * (s⁻¹ * (1 - s)⁻¹) := by
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hdisc_s_inv :
      (Homogenization.geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
    old_inv_geometricDiscount_le_five_inv hs hs_le (by norm_num : (1 : ℝ) ≤ 1)
  have hdisc_s_pos : 0 < Homogenization.geometricDiscount s 1 := by
    exact Homogenization.geometricDiscount_pos (by simpa using hs)
  have hsqrt :
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) ≤
        5 * (1 - s)⁻¹ :=
    sqrt_inv_one_sub_rpow_three_two_mul_sub_le_five_inv hs hs1
  have hpow :
      Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
        Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    rpow_three_d_add_s_le_d_add_one d hs_le
  have hnote_nonneg :
      0 ≤ (3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hdisc_one_pos : 0 < Homogenization.geometricDiscount (1 : ℝ) 1 := by
    exact Homogenization.geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hnote_with_disc_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹ :=
    mul_nonneg hnote_nonneg (inv_nonneg.mpr hdisc_one_pos.le)
  have hcut_nonneg : 0 ≤ 4 * quantitativeCubeCutoffHessianConst d := by
    exact mul_nonneg (by norm_num)
      (quantitativeCubeCutoffHessianConst_nonneg d)
  have hprefix_large_nonneg :
      0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hprefix_s_nonneg :
      0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * (5 * s⁻¹) :=
    mul_nonneg hprefix_large_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hs.le))
  unfold coarseCaccioppoliCenteredBesovHessianFront
    coarseCaccioppoliCenteredBesovHessianBase centeredHessianFrontEnvelope
  calc
    (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          (Homogenization.geometricDiscount s 1)⁻¹ *
        (2 *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹))) *
        (4 * quantitativeCubeCutoffHessianConst d)
        ≤
      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
          (5 * s⁻¹) *
        (2 *
          ((5 * (1 - s)⁻¹) *
            (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹))) *
        (4 * quantitativeCubeCutoffHessianConst d) := by
          gcongr
    _ =
      ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
          ((5 : ℝ) *
            (2 * ((5 : ℝ) *
              (((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
                (Homogenization.geometricDiscount (1 : ℝ) 1)⁻¹)))) *
          (4 * quantitativeCubeCutoffHessianConst d)) *
        (s⁻¹ * (1 - s)⁻¹) := by
          ring_nf

private theorem centeredHessianFront_mul_den_le_envelope_mul_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliCenteredBesovHessianFront d s C * (s * (1 - s)) ≤
      centeredHessianFrontEnvelope d C * s⁻¹ := by
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    exact mul_nonneg hs.le (by linarith)
  have hfront :=
    centeredHessianFront_le_envelope_mul_endpoint_inv d hC hs hs1
  have hscaled :=
    mul_le_mul_of_nonneg_right hfront hden_nonneg
  have henv_nonneg : 0 ≤ centeredHessianFrontEnvelope d C :=
    centeredHessianFrontEnvelope_nonneg d hC
  calc
    coarseCaccioppoliCenteredBesovHessianFront d s C * (s * (1 - s))
        ≤
      (centeredHessianFrontEnvelope d C * (s⁻¹ * (1 - s)⁻¹)) *
        (s * (1 - s)) := hscaled
    _ =
      centeredHessianFrontEnvelope d C *
        (s⁻¹ * ((1 - s)⁻¹ * (s * (1 - s)))) := by
          ring
    _ ≤ centeredHessianFrontEnvelope d C * s⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (two_endpoint_inv_mul_self_one_sub_le_inv hs hs1) henv_nonneg

private theorem inv_one_sub_rpow_three_neg_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ 5 * s⁻¹ := by
  have h := old_inv_geometricDiscount_le_five_inv
    (s := s) (p := 1) hs hs_le (by norm_num : (1 : ℝ) ≤ 1)
  simpa [Homogenization.geometricDiscount] using h

private theorem triple_endpoint_inv_mul_self_one_sub_eq_inv {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    s⁻¹ * (s⁻¹ * ((1 - s)⁻¹ * (s * (1 - s)))) = s⁻¹ := by
  have hs_ne : s ≠ 0 := hs.ne'
  have hs1_pos : 0 < 1 - s := by linarith
  have hs1_ne : 1 - s ≠ 0 := hs1_pos.ne'
  field_simp [hs_ne, hs1_ne]

private noncomputable def centeredGradientFrontEnvelope
    (d : ℕ) (C : ℝ) : ℝ :=
  (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
    ((5 : ℝ) *
      (2 * ((((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
        (5 : ℝ)) * (5 : ℝ)))) *
    (2 * quantitativeCubeCutoffGradientConst d)

private theorem centeredGradientFront_le_envelope_mul_endpoint_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliCenteredBesovGradientFront d s C ≤
      centeredGradientFrontEnvelope d C *
        (s⁻¹ * (s⁻¹ * (1 - s)⁻¹)) := by
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hdisc_s_inv :
      (Homogenization.geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
    old_inv_geometricDiscount_le_five_inv hs hs_le (by norm_num : (1 : ℝ) ≤ 1)
  have hgeom_inv :
      (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ 5 * s⁻¹ :=
    inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have hdisc_sub_inv :
      (Homogenization.geometricDiscount (1 - s) 1)⁻¹ ≤ 5 * (1 - s)⁻¹ :=
    old_inv_geometricDiscount_le_five_inv
      (by linarith : 0 < 1 - s) (by linarith : 1 - s ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1)
  have hpow :
      Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
        Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    rpow_three_d_add_s_le_d_add_one d hs_le
  have hnote_nonneg :
      0 ≤ (3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hdisc_s_pos : 0 < Homogenization.geometricDiscount s 1 := by
    exact Homogenization.geometricDiscount_pos (by simpa using hs)
  have hdisc_sub_pos : 0 < Homogenization.geometricDiscount (1 - s) 1 := by
    exact Homogenization.geometricDiscount_pos
      (by nlinarith : 0 < (1 - s) * 1)
  have hgeom_pos : 0 < 1 - Real.rpow (3 : ℝ) (-s) := by
    simpa [Homogenization.geometricDiscount] using hdisc_s_pos
  have hcut_nonneg : 0 ≤ 2 * quantitativeCubeCutoffGradientConst d := by
    exact mul_nonneg (by norm_num)
      (quantitativeCubeCutoffGradientConst_nonneg d)
  have hprefix_large_nonneg :
      0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hprefix_s_nonneg :
      0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * (5 * s⁻¹) :=
    mul_nonneg hprefix_large_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hs.le))
  unfold coarseCaccioppoliCenteredBesovGradientFront
    coarseCaccioppoliCenteredBesovGradientBase centeredGradientFrontEnvelope
  calc
    (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          (Homogenization.geometricDiscount s 1)⁻¹ *
        (2 *
          ((((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            (Homogenization.geometricDiscount (1 - s) 1)⁻¹)) *
        (2 * quantitativeCubeCutoffGradientConst d)
        ≤
      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
          (5 * s⁻¹) *
        (2 *
          ((((3 / 2 : ℝ) * C * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (5 * s⁻¹)) *
            (5 * (1 - s)⁻¹))) *
        (2 * quantitativeCubeCutoffGradientConst d) := by
          gcongr
    _ =
      ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) *
          ((5 : ℝ) *
            (2 * ((((3 / 2 : ℝ) * C *
                Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (5 : ℝ)) * (5 : ℝ)))) *
          (2 * quantitativeCubeCutoffGradientConst d)) *
        (s⁻¹ * (s⁻¹ * (1 - s)⁻¹)) := by
          ring_nf

private theorem centeredGradientFront_mul_den_le_envelope_mul_inv
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliCenteredBesovGradientFront d s C * (s * (1 - s)) ≤
      centeredGradientFrontEnvelope d C * s⁻¹ := by
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    exact mul_nonneg hs.le (by linarith)
  have hfront :=
    centeredGradientFront_le_envelope_mul_endpoint_inv d hC hs hs1
  have hscaled :=
    mul_le_mul_of_nonneg_right hfront hden_nonneg
  calc
    coarseCaccioppoliCenteredBesovGradientFront d s C * (s * (1 - s))
        ≤
      (centeredGradientFrontEnvelope d C *
          (s⁻¹ * (s⁻¹ * (1 - s)⁻¹))) *
        (s * (1 - s)) := hscaled
    _ =
      centeredGradientFrontEnvelope d C *
        (s⁻¹ * (s⁻¹ * ((1 - s)⁻¹ * (s * (1 - s))))) := by
          ring
    _ =
      centeredGradientFrontEnvelope d C * s⁻¹ := by
          rw [triple_endpoint_inv_mul_self_one_sub_eq_inv hs hs1]

noncomputable def boundaryScaleZeroAlphaBudgetEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Ceff : ℝ := coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q0 Csol
  max 1 ((81 : ℝ) *
    (6 * centeredAverageFrontEnvelope d Ceff +
      12 * centeredHessianFrontEnvelope d Ceff +
      6 * centeredGradientFrontEnvelope d Ceff))

private theorem localPatchBufferedCeffLocalBudget_unit_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤
      coarseCaccioppoliLocalPatchBufferedCeffLocalBudget (originCube d 0)
        (fullVectorPoincareCubeConstant (originCube d 0)) := by
  unfold coarseCaccioppoliLocalPatchBufferedCeffLocalBudget
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d)))
    (localPatchBufferedLocalBudget_unit_nonneg d)

private theorem localPatchBufferedAlphaBudgetUnit_le_envelope_mul_inv
    {d : ℕ} [NeZero d] {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s ≤
      boundaryScaleZeroAlphaBudgetEnvelope d * s⁻¹ := by
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Ceff : ℝ := coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q0 Csol
  let A : ℝ := coarseCaccioppoliCenteredAverageFront d s Ceff
  let H : ℝ := coarseCaccioppoliCenteredBesovHessianFront d s Ceff
  let G : ℝ := coarseCaccioppoliCenteredBesovGradientFront d s Ceff
  let Aenv : ℝ := centeredAverageFrontEnvelope d Ceff
  let Henv : ℝ := centeredHessianFrontEnvelope d Ceff
  let Genv : ℝ := centeredGradientFrontEnvelope d Ceff
  let den : ℝ := s * (1 - s)
  let K : ℝ := (81 : ℝ) * (6 * Aenv + 12 * Henv + 6 * Genv)
  let Env : ℝ := boundaryScaleZeroAlphaBudgetEnvelope d
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hCeff_nonneg : 0 ≤ Ceff := by
    dsimp [Ceff, Csol, Q0]
    exact localPatchBufferedCeffLocalBudget_unit_nonneg d
  have hAden : A * den ≤ Aenv * s⁻¹ := by
    dsimp [A, Aenv, den]
    exact centeredAverageFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hHden : H * den ≤ Henv * s⁻¹ := by
    dsimp [H, Henv, den]
    exact centeredHessianFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hGden : G * den ≤ Genv * s⁻¹ := by
    dsimp [G, Genv, den]
    exact centeredGradientFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hsum_den :
      (6 * A + 12 * H + 6 * G) * den ≤
        (6 * Aenv + 12 * Henv + 6 * Genv) * s⁻¹ := by
    calc
      (6 * A + 12 * H + 6 * G) * den =
          6 * (A * den) + 12 * (H * den) + 6 * (G * den) := by ring
      _ ≤ 6 * (Aenv * s⁻¹) + 12 * (Henv * s⁻¹) +
            6 * (Genv * s⁻¹) := by
            nlinarith
      _ = (6 * Aenv + 12 * Henv + 6 * Genv) * s⁻¹ := by ring
  have hfront :
      ((81 : ℝ) * (6 * A + 12 * H + 6 * G)) * den ≤ K * s⁻¹ := by
    dsimp [K]
    calc
      ((81 : ℝ) * (6 * A + 12 * H + 6 * G)) * den =
          81 * ((6 * A + 12 * H + 6 * G) * den) := by ring
      _ ≤ 81 * ((6 * Aenv + 12 * Henv + 6 * Genv) * s⁻¹) := by
            exact mul_le_mul_of_nonneg_left hsum_den (by norm_num)
      _ = ((81 : ℝ) * (6 * Aenv + 12 * Henv + 6 * Genv)) * s⁻¹ := by ring
  have hEnv_eq : Env = max 1 K := by
    dsimp [Env, boundaryScaleZeroAlphaBudgetEnvelope, K, Q0, Csol, Ceff,
      Aenv, Henv, Genv]
  have hEnv_ge_one : 1 ≤ Env := by
    rw [hEnv_eq]
    exact le_max_left _ _
  have hEnv_ge_K : K ≤ Env := by
    rw [hEnv_eq]
    exact le_max_right _ _
  have hEnv_nonneg : 0 ≤ Env := by linarith
  have hone_le_inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hone_le_Env_mul_inv : 1 ≤ Env * s⁻¹ := by
    calc
      1 ≤ Env := hEnv_ge_one
      _ = Env * 1 := by ring
      _ ≤ Env * s⁻¹ := mul_le_mul_of_nonneg_left hone_le_inv hEnv_nonneg
  have hfront_le_Env : ((81 : ℝ) * (6 * A + 12 * H + 6 * G)) * den ≤
      Env * s⁻¹ := by
    exact hfront.trans (mul_le_mul_of_nonneg_right hEnv_ge_K (inv_nonneg.mpr hs.le))
  unfold coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit
    coarseCaccioppoliLocalPatchBufferedAlphaBudget
    coarseCaccioppoliLocalPatchBufferedCenteredFrontBudget
  dsimp [Q0, Csol, Ceff, A, H, G, den, Env]
  exact max_le hone_le_Env_mul_inv hfront_le_Env

noncomputable def interiorScaleZeroAlphaBudgetEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Ceff : ℝ := coarseCaccioppoliBufferedCeffLocalBudget Q0 Csol
  max 1 ((81 : ℝ) *
    (2 * centeredAverageFrontEnvelope d Ceff +
      4 * centeredHessianFrontEnvelope d Ceff +
      2 * centeredGradientFrontEnvelope d Ceff))

private theorem bufferedCeffLocalBudget_unit_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤
      coarseCaccioppoliBufferedCeffLocalBudget (originCube d 0)
        (fullVectorPoincareCubeConstant (originCube d 0)) := by
  unfold coarseCaccioppoliBufferedCeffLocalBudget
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d)))
    (bufferedLocalBudget_unit_nonneg d)

private theorem bufferedAlphaBudgetUnit_le_envelope_mul_inv
    {d : ℕ} [NeZero d] {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    coarseCaccioppoliBufferedAlphaBudgetUnit d s ≤
      interiorScaleZeroAlphaBudgetEnvelope d * s⁻¹ := by
  let Q0 : TriadicCube d := originCube d 0
  let Csol : ℝ := fullVectorPoincareCubeConstant Q0
  let Ceff : ℝ := coarseCaccioppoliBufferedCeffLocalBudget Q0 Csol
  let A : ℝ := coarseCaccioppoliCenteredAverageFront d s Ceff
  let H : ℝ := coarseCaccioppoliCenteredBesovHessianFront d s Ceff
  let G : ℝ := coarseCaccioppoliCenteredBesovGradientFront d s Ceff
  let Aenv : ℝ := centeredAverageFrontEnvelope d Ceff
  let Henv : ℝ := centeredHessianFrontEnvelope d Ceff
  let Genv : ℝ := centeredGradientFrontEnvelope d Ceff
  let den : ℝ := s * (1 - s)
  let K : ℝ := (81 : ℝ) * (2 * Aenv + 4 * Henv + 2 * Genv)
  let Env : ℝ := interiorScaleZeroAlphaBudgetEnvelope d
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hCeff_nonneg : 0 ≤ Ceff := by
    dsimp [Ceff, Csol, Q0]
    exact bufferedCeffLocalBudget_unit_nonneg d
  have hAden : A * den ≤ Aenv * s⁻¹ := by
    dsimp [A, Aenv, den]
    exact centeredAverageFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hHden : H * den ≤ Henv * s⁻¹ := by
    dsimp [H, Henv, den]
    exact centeredHessianFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hGden : G * den ≤ Genv * s⁻¹ := by
    dsimp [G, Genv, den]
    exact centeredGradientFront_mul_den_le_envelope_mul_inv d hCeff_nonneg hs hs1
  have hsum_den :
      (2 * A + 4 * H + 2 * G) * den ≤
        (2 * Aenv + 4 * Henv + 2 * Genv) * s⁻¹ := by
    calc
      (2 * A + 4 * H + 2 * G) * den =
          2 * (A * den) + 4 * (H * den) + 2 * (G * den) := by ring
      _ ≤ 2 * (Aenv * s⁻¹) + 4 * (Henv * s⁻¹) +
            2 * (Genv * s⁻¹) := by
            nlinarith
      _ = (2 * Aenv + 4 * Henv + 2 * Genv) * s⁻¹ := by ring
  have hfront :
      ((81 : ℝ) * (2 * A + 4 * H + 2 * G)) * den ≤ K * s⁻¹ := by
    dsimp [K]
    calc
      ((81 : ℝ) * (2 * A + 4 * H + 2 * G)) * den =
          81 * ((2 * A + 4 * H + 2 * G) * den) := by ring
      _ ≤ 81 * ((2 * Aenv + 4 * Henv + 2 * Genv) * s⁻¹) := by
            exact mul_le_mul_of_nonneg_left hsum_den (by norm_num)
      _ = ((81 : ℝ) * (2 * Aenv + 4 * Henv + 2 * Genv)) * s⁻¹ := by ring
  have hEnv_eq : Env = max 1 K := by
    dsimp [Env, interiorScaleZeroAlphaBudgetEnvelope, K, Q0, Csol, Ceff,
      Aenv, Henv, Genv]
  have hEnv_ge_one : 1 ≤ Env := by
    rw [hEnv_eq]
    exact le_max_left _ _
  have hEnv_ge_K : K ≤ Env := by
    rw [hEnv_eq]
    exact le_max_right _ _
  have hEnv_nonneg : 0 ≤ Env := by linarith
  have hone_le_inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hone_le_Env_mul_inv : 1 ≤ Env * s⁻¹ := by
    calc
      1 ≤ Env := hEnv_ge_one
      _ = Env * 1 := by ring
      _ ≤ Env * s⁻¹ := mul_le_mul_of_nonneg_left hone_le_inv hEnv_nonneg
  have hfront_le_Env : ((81 : ℝ) * (2 * A + 4 * H + 2 * G)) * den ≤
      Env * s⁻¹ := by
    exact hfront.trans (mul_le_mul_of_nonneg_right hEnv_ge_K (inv_nonneg.mpr hs.le))
  unfold coarseCaccioppoliBufferedAlphaBudgetUnit
    coarseCaccioppoliBufferedAlphaBudget
    coarseCaccioppoliBufferedCenteredFrontBudget
  dsimp [Q0, Csol, Ceff, A, H, G, den, Env]
  exact max_le hone_le_Env_mul_inv hfront_le_Env

noncomputable def boundaryScaleZeroAlphaInternalEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  (Fintype.card (Fin d) : ℝ) * boundaryScaleZeroAlphaBudgetEnvelope d

noncomputable def interiorScaleZeroAlphaInternalEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  (Fintype.card (Fin d) : ℝ) * interiorScaleZeroAlphaBudgetEnvelope d

noncomputable def boundaryScaleZeroCrossInternalEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  (Fintype.card (Fin d) : ℝ) * boundaryScaleZeroCrossBudgetEnvelope d

noncomputable def interiorScaleZeroCrossInternalEnvelope
    (d : ℕ) [NeZero d] : ℝ :=
  (Fintype.card (Fin d) : ℝ) * interiorScaleZeroCrossBudgetEnvelope d

private theorem boundaryScaleZeroAlphaInternal_le_envelope_mul_inv
    {d : ℕ} [NeZero d] {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s ≤
      boundaryScaleZeroAlphaInternalEnvelope d * s⁻¹ := by
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have h :=
    mul_le_mul_of_nonneg_left
      (localPatchBufferedAlphaBudgetUnit_le_envelope_mul_inv (d := d) hs hs1)
      hcard_nonneg
  unfold boundaryScaleZeroAlphaInternalEnvelope
  simpa [mul_assoc] using h

private theorem interiorScaleZeroAlphaInternal_le_envelope_mul_inv
    {d : ℕ} [NeZero d] {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudgetUnit d s ≤
      interiorScaleZeroAlphaInternalEnvelope d * s⁻¹ := by
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have h :=
    mul_le_mul_of_nonneg_left
      (bufferedAlphaBudgetUnit_le_envelope_mul_inv (d := d) hs hs1)
      hcard_nonneg
  unfold interiorScaleZeroAlphaInternalEnvelope
  simpa [mul_assoc] using h

private theorem boundaryScaleZeroCrossInternal_le_envelope
    {d : ℕ} [NeZero d] {s : ℝ} (hs_le : s ≤ 1) :
    (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s ≤
      boundaryScaleZeroCrossInternalEnvelope d := by
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have h :=
    mul_le_mul_of_nonneg_left
      (localPatchBufferedCrossBudgetUnit_le_envelope (d := d) hs_le)
      hcard_nonneg
  unfold boundaryScaleZeroCrossInternalEnvelope
  exact h

private theorem interiorScaleZeroCrossInternal_le_envelope
    {d : ℕ} [NeZero d] {s : ℝ} (hs_le : s ≤ 1) :
    (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudgetUnit d s ≤
      interiorScaleZeroCrossInternalEnvelope d := by
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have h :=
    mul_le_mul_of_nonneg_left
      (bufferedCrossBudgetUnit_le_envelope (d := d) hs_le)
      hcard_nonneg
  unfold interiorScaleZeroCrossInternalEnvelope
  exact h

private theorem localPatchBufferedAlphaBudgetUnit_nonneg
    (d : ℕ) [NeZero d] (s : ℝ) :
    0 ≤ coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s := by
  unfold coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit
    coarseCaccioppoliLocalPatchBufferedAlphaBudget
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)

private theorem bufferedAlphaBudgetUnit_nonneg
    (d : ℕ) [NeZero d] (s : ℝ) :
    0 ≤ coarseCaccioppoliBufferedAlphaBudgetUnit d s := by
  unfold coarseCaccioppoliBufferedAlphaBudgetUnit
    coarseCaccioppoliBufferedAlphaBudget
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)

private theorem localPatchBufferedCrossBudgetUnit_nonneg
    (d : ℕ) [NeZero d] (s : ℝ) :
    0 ≤ coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s := by
  unfold coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit
    coarseCaccioppoliLocalPatchBufferedCrossBudget
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)

private theorem bufferedCrossBudgetUnit_nonneg
    (d : ℕ) [NeZero d] (s : ℝ) :
    0 ≤ coarseCaccioppoliBufferedCrossBudgetUnit d s := by
  unfold coarseCaccioppoliBufferedCrossBudgetUnit
    coarseCaccioppoliBufferedCrossBudget
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)

/-- Explicit scale-zero boundary constant produced by the completed
deterministic Caccioppoli bridge with the standard beta-dependent radius
iteration.  This still depends on the exponents `s,t`; the remaining scalar
majorization step is to bound it by one dimension-only constant on `0 < s`,
`0 < t`, `s + t < 1`. -/
noncomputable def boundaryCaccioppoliScaleZeroExplicitConstant
    (d : ℕ) [NeZero d] (s t : ℝ) : ℝ :=
  let CalphaInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s
  let CcrossInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s
  (18 : ℝ) ^ d *
    caccioppoliStandardExplicitNoteBoundSplit s t CalphaInternal CcrossInternal

/-- Explicit scale-zero centered-interior constant produced by the completed
split deterministic Caccioppoli bridge with the standard beta-dependent radius
iteration. -/
noncomputable def interiorCaccioppoliScaleZeroExplicitConstant
    (d : ℕ) [NeZero d] (s t : ℝ) : ℝ :=
  let CalphaInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliBufferedAlphaBudgetUnit d s
  let CcrossInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliBufferedCrossBudgetUnit d s
  (18 : ℝ) ^ d *
    caccioppoliStandardExplicitNoteBoundSplit s t CalphaInternal CcrossInternal

theorem boundaryCaccioppoliScaleZeroExplicitConstant_le_envelopeExplicit
    {d : ℕ} [NeZero d] {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    boundaryCaccioppoliScaleZeroExplicitConstant d s t ≤
      (18 : ℝ) ^ d *
        caccioppoliStandardExplicitNoteBoundSplit s t
          (boundaryScaleZeroAlphaInternalEnvelope d * s⁻¹)
          (boundaryScaleZeroCrossInternalEnvelope d) := by
  have hs1 : s < 1 := by linarith
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCalpha_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s :=
    mul_nonneg hcard_nonneg (localPatchBufferedAlphaBudgetUnit_nonneg d s)
  have hCcross_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s :=
    mul_nonneg hcard_nonneg (localPatchBufferedCrossBudgetUnit_nonneg d s)
  have hCalpha_le :
      (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s ≤
        boundaryScaleZeroAlphaInternalEnvelope d * s⁻¹ :=
    boundaryScaleZeroAlphaInternal_le_envelope_mul_inv (d := d) hs hs1
  have hCcross_le :
      (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s ≤
        boundaryScaleZeroCrossInternalEnvelope d :=
    boundaryScaleZeroCrossInternal_le_envelope (d := d) hs_le
  have hnote :=
    caccioppoliStandardExplicitNoteBoundSplit_mono
      (s := s) (t := t)
      (Calpha₁ := (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s)
      (Calpha₂ := boundaryScaleZeroAlphaInternalEnvelope d * s⁻¹)
      (Ccross₁ := (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s)
      (Ccross₂ := boundaryScaleZeroCrossInternalEnvelope d)
      hs ht hst hCalpha_nonneg hCalpha_le hCcross_nonneg hCcross_le
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  unfold boundaryCaccioppoliScaleZeroExplicitConstant
  exact mul_le_mul_of_nonneg_left hnote hfactor_nonneg

theorem interiorCaccioppoliScaleZeroExplicitConstant_le_envelopeExplicit
    {d : ℕ} [NeZero d] {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    interiorCaccioppoliScaleZeroExplicitConstant d s t ≤
      (18 : ℝ) ^ d *
        caccioppoliStandardExplicitNoteBoundSplit s t
          (interiorScaleZeroAlphaInternalEnvelope d * s⁻¹)
          (interiorScaleZeroCrossInternalEnvelope d) := by
  have hs1 : s < 1 := by linarith
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCalpha_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudgetUnit d s :=
    mul_nonneg hcard_nonneg (bufferedAlphaBudgetUnit_nonneg d s)
  have hCcross_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudgetUnit d s :=
    mul_nonneg hcard_nonneg (bufferedCrossBudgetUnit_nonneg d s)
  have hCalpha_le :
      (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliBufferedAlphaBudgetUnit d s ≤
        interiorScaleZeroAlphaInternalEnvelope d * s⁻¹ :=
    interiorScaleZeroAlphaInternal_le_envelope_mul_inv (d := d) hs hs1
  have hCcross_le :
      (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliBufferedCrossBudgetUnit d s ≤
        interiorScaleZeroCrossInternalEnvelope d :=
    interiorScaleZeroCrossInternal_le_envelope (d := d) hs_le
  have hnote :=
    caccioppoliStandardExplicitNoteBoundSplit_mono
      (s := s) (t := t)
      (Calpha₁ := (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudgetUnit d s)
      (Calpha₂ := interiorScaleZeroAlphaInternalEnvelope d * s⁻¹)
      (Ccross₁ := (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudgetUnit d s)
      (Ccross₂ := interiorScaleZeroCrossInternalEnvelope d)
      hs ht hst hCalpha_nonneg hCalpha_le hCcross_nonneg hCcross_le
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  unfold interiorCaccioppoliScaleZeroExplicitConstant
  exact mul_le_mul_of_nonneg_left hnote hfactor_nonneg


end

end Ch03
end Book
end Homogenization
