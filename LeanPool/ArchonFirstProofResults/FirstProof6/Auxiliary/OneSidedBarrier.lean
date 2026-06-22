/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ResolventBound

/-!
# Problem 6: Large epsilon-light vertex subsets -- One-Sided Barrier

One-sided barrier machinery for the BSS coloring argument.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma barrier_smw_trace_bound
    (M B : Matrix V V ℝ)
    (u u' : ℝ) (hu : u < u')
    (hM_bound : (u • (1 : Matrix V V ℝ) - M).PosDef)
    (hB : B.PosSemidef)
    (htrBU_lt : (B * (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace < 1)
    (htrBU_nn : 0 ≤ (B * (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace)
    (_htrBU2_nn : 0 ≤ (B * (u' • (1 : Matrix V V ℝ) - M)⁻¹ *
      (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace) :
    barrierPotential u' (M + B) ≤
      barrierPotential u' M +
        (B * (u' • (1 : Matrix V V ℝ) - M)⁻¹ *
          (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace /
        (1 - (B * (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace) := by
  set A := u' • (1 : Matrix V V ℝ) - M with hA_def
  set U := A⁻¹ with hU_def
  have hA_pd : A.PosDef := barrier_shift_posDef M u u' hu hM_bound
  have hU_pd : U.PosDef := hA_pd.inv
  have hAU : U⁻¹ = A := by
    rw [hU_def]
    exact Matrix.nonsing_inv_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA_pd.isUnit)
  have hgoal_eq : barrierPotential u' (M + B) = (U⁻¹ - B)⁻¹.trace := by
    unfold barrierPotential; congr 1; rw [hAU, hA_def]; simp [sub_sub]
  have hphi_eq : barrierPotential u' M = U.trace := by
    unfold barrierPotential; rw [hU_def]
  rw [hgoal_eq, hphi_eq]
  exact psd_resolvent_trace_bound U B hU_pd hB htrBU_lt htrBU_nn

lemma one_sided_barrier
    (M B : Matrix V V ℝ)
    (u u' : ℝ) (hu : u < u')
    (hM_bound : (u • (1 : Matrix V V ℝ) - M).PosDef)
    (hB : B.PosSemidef)
    (hbarrier : let U := (u' • (1 : Matrix V V ℝ) - M)⁻¹
      (B * U).trace + (B * U * U).trace / (barrierPotential u M - barrierPotential u' M) ≤ 1) :
    barrierPotential u' (M + B) ≤ barrierPotential u M := by
  by_cases hne : IsEmpty V
  · simp only [barrierPotential, Matrix.trace]; simp
  · haveI : Nonempty V := not_isEmpty_iff.mp hne
    set U := (u' • (1 : Matrix V V ℝ) - M)⁻¹ with hU_def
    set trBU := (B * U).trace with htrBU_def
    set trBU2 := (B * U * U).trace with htrBU2_def
    set gap := barrierPotential u M - barrierPotential u' M with hgap_def
    have hgap_pos : 0 < gap := barrier_gap_pos M u u' hu hM_bound
    have hU_pd : U.PosDef := (barrier_shift_posDef M u u' hu hM_bound).inv
    have htrBU_nn : 0 ≤ trBU :=
      trace_mul_nonneg_of_posSemidef B U hB hU_pd.posSemidef
    have hU_sq_psd : (U * U).PosSemidef := by
      rw [show U * U = Uᴴ * U from by rw [hU_pd.isHermitian]]
      exact Matrix.posSemidef_conjTranspose_mul_self U
    have htrBU2_nn : 0 ≤ trBU2 := by
      rw [htrBU2_def, Matrix.mul_assoc]
      exact trace_mul_nonneg_of_posSemidef B (U * U) hB hU_sq_psd
    have hbarrier' : trBU + trBU2 / gap ≤ 1 := hbarrier
    by_cases htrBU2_pos : trBU2 = 0
    · have htrBU_le : trBU ≤ 1 := by linarith [div_nonneg htrBU2_nn hgap_pos.le]
      by_cases htrBU_eq : trBU = 1
      · have hUherm : Uᴴ = U := hU_pd.isHermitian
        have hUBU_psd : (U * B * U).PosSemidef := by
          have h := hB.mul_mul_conjTranspose_same Uᴴ
          rwa [hUherm, hUherm] at h
        have htr_eq : (U * B * U).trace = trBU2 := by
          rw [htrBU2_def, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
        have hUBU_zero : U * B * U = 0 :=
          hUBU_psd.trace_eq_zero_iff.mp (by linarith [htr_eq])
        have hU_det : IsUnit U.det :=
          (Matrix.isUnit_iff_isUnit_det U).mp hU_pd.isUnit
        have hB_zero : B = 0 := by
          have hUU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hU_det
          have hUU' : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU_det
          have h1 : U⁻¹ * (U * B * U) * U⁻¹ = B := by
            calc U⁻¹ * (U * B * U) * U⁻¹
                = U⁻¹ * U * B * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
              _ = B := by rw [hUU, hUU', one_mul, mul_one]
          rw [hUBU_zero, Matrix.mul_zero, Matrix.zero_mul] at h1
          exact h1.symm
        rw [hB_zero, add_zero]; linarith
      · have htrBU_lt : trBU < 1 := lt_of_le_of_ne htrBU_le htrBU_eq
        linarith [barrier_smw_trace_bound M B u u' hu hM_bound hB htrBU_lt htrBU_nn htrBU2_nn,
          barrier_rearrange hgap_pos htrBU_nn htrBU2_nn htrBU_lt hbarrier']
    · have htrBU2_pos' : 0 < trBU2 := lt_of_le_of_ne htrBU2_nn (Ne.symm htrBU2_pos)
      have htrBU_lt : trBU < 1 := by
        linarith [div_pos htrBU2_pos' hgap_pos]
      linarith [barrier_smw_trace_bound M B u u' hu hM_bound hB htrBU_lt htrBU_nn htrBU2_nn,
        barrier_rearrange hgap_pos htrBU_nn htrBU2_nn htrBU_lt hbarrier']

lemma inv_sub_posDef_of_trace_lt_one
    (U B : Matrix V V ℝ)
    (hU : U.PosDef) (hB : B.PosSemidef)
    (htr : (B * U).trace < 1) :
    (U⁻¹ - B).PosDef := by
  classical
  obtain ⟨Uhalf, hUhalf_herm, hUhalf_det, hUhalf_sq⟩ := posDef_sqrt_exists U hU
  have hUhalf_inv_sq : Uhalf⁻¹ * Uhalf⁻¹ = U⁻¹ :=
    (Matrix.mul_inv_rev Uhalf Uhalf).symm ▸ congrArg Inv.inv hUhalf_sq
  set K := Uhalf * B * Uhalf with hK_def
  have hK_psd : K.PosSemidef := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalfᴴ * B * Uhalf from by rw [hUhalf_herm.eq]]
    exact hB.conjTranspose_mul_mul_same Uhalf
  have htrK_lt : K.trace < 1 := by
    change (Uhalf * B * Uhalf).trace < 1
    rw [show Uhalf * B * Uhalf = Uhalf * (B * Uhalf) from Matrix.mul_assoc _ _ _,
        Matrix.trace_mul_comm Uhalf (B * Uhalf), Matrix.mul_assoc, hUhalf_sq]
    exact htr
  have hIK_pd : ((1 : Matrix V V ℝ) - K).PosDef :=
    one_sub_posDef_of_trace_lt_one K hK_psd htrK_lt
  have hUinv_sub_B : U⁻¹ - B = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUhalf_inv_sq]
    congr 1; rw [hK_def]; symm
    have hUU := Matrix.nonsing_inv_mul Uhalf hUhalf_det
    have hUU' := Matrix.mul_nonsing_inv Uhalf hUhalf_det
    calc Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹
        = (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hUU, hUU', one_mul, mul_one]
  rw [hUinv_sub_B]
  have hUhalf_inv_unit : IsUnit Uhalf⁻¹ :=
    IsUnit.of_mul_eq_one Uhalf (Matrix.nonsing_inv_mul Uhalf hUhalf_det)
  have hUhalf_inv_herm : (Uhalf⁻¹)ᴴ = Uhalf⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]; congr 1
  rw [show Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ =
      Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * star Uhalf⁻¹ from by
    rw [star_eq_conjTranspose, hUhalf_inv_herm]]
  exact hUhalf_inv_unit.posDef_star_right_conjugate_iff.mpr hIK_pd
end Problem6

end
