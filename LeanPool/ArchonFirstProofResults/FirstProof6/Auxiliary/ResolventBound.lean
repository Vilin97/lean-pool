/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.BarrierPotential

/-!
# Problem 6: Large epsilon-light vertex subsets -- Resolvent Bound

`psd_resolvent_trace_bound`: `tr((U⁻¹ - B)⁻¹) ≤ tr(U) + tr(B·U²) / (1 - tr(B·U))`.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma psd_resolvent_conj_inv (U B Uhalf K : Matrix V V ℝ)
    (hK_def : K = Uhalf * B * Uhalf) (hUhalf_sq : Uhalf * Uhalf = U)
    (hUhalf_det : IsUnit Uhalf.det) (hK_psd : K.PosSemidef) (htrK_lt : K.trace < 1) :
    (U⁻¹ - B)⁻¹ = Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
  classical
  have hUU : Uhalf⁻¹ * Uhalf = 1 := Matrix.nonsing_inv_mul Uhalf hUhalf_det
  have hUU' : Uhalf * Uhalf⁻¹ = 1 := Matrix.mul_nonsing_inv Uhalf hUhalf_det
  have hUhalf_inv_sq : Uhalf⁻¹ * Uhalf⁻¹ = U⁻¹ :=
    (Matrix.mul_inv_rev Uhalf Uhalf).symm ▸ congrArg Inv.inv hUhalf_sq
  have hUinv_sub_B : U⁻¹ - B = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUhalf_inv_sq]
    congr 1
    rw [hK_def]
    symm
    have : Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹ =
        (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹) := by simp only [Matrix.mul_assoc]
    simp only [this, hUU, hUU', one_mul, mul_one]
  rw [hUinv_sub_B]
  have hIK_pd : ((1 : Matrix V V ℝ) - K).PosDef :=
    one_sub_posDef_of_trace_lt_one K hK_psd htrK_lt
  have hIK_det : IsUnit ((1 : Matrix V V ℝ) - K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hIK_pd.isUnit
  have h_prod : (Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹) *
      (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) = 1 := by
    calc Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ *
          (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf)
        = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) *
            (Uhalf⁻¹ * Uhalf) * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
          simp only [Matrix.mul_assoc]
      _ = Uhalf⁻¹ * (((1 : Matrix V V ℝ) - K) * ((1 : Matrix V V ℝ) - K)⁻¹) * Uhalf := by
          rw [hUU]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hIK_det, Matrix.mul_one, hUU]
  exact Matrix.inv_eq_right_inv h_prod

private lemma psd_resolvent_trace_le (U B Uhalf K : Matrix V V ℝ) (hU : U.PosDef)
    (hUhalf_sq : Uhalf * Uhalf = U) (hK_def : K = Uhalf * B * Uhalf) (hK_psd : K.PosSemidef)
    (htrBU_lt : (B * U).trace < 1)
    (hconj_inv : (U⁻¹ - B)⁻¹ = Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) :
    (U⁻¹ - B)⁻¹.trace ≤ U.trace + (B * U * U).trace / (1 - (B * U).trace) := by
  classical
  have htrK : K.trace = (B * U).trace := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalf * (B * Uhalf) from Matrix.mul_assoc _ _ _,
      Matrix.trace_mul_comm Uhalf (B * Uhalf), Matrix.mul_assoc, hUhalf_sq]
  have htrK_lt : K.trace < 1 := htrK ▸ htrBU_lt
  rw [hconj_inv]
  have htr_rewrite : (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf).trace =
      (((1 : Matrix V V ℝ) - K)⁻¹ * U).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUhalf_sq]
  rw [htr_rewrite]
  set hK_herm := hK_psd.isHermitian with hK_herm_def
  set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ) with hQ_def
  set eig := hK_herm.eigenvalues with heig_def
  have hQ_star_mul : star eigQ * eigQ = 1 :=
    Unitary.coe_star_mul_self hK_herm.eigenvectorUnitary
  have hQ_mul_star : eigQ * star eigQ = 1 :=
    Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
  have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := realSpectralDecomp hK_herm
  have h_eig_nn := hK_psd.eigenvalues_nonneg
  have h_eig_lt_1 : ∀ i, eig i < 1 := fun i =>
    lt_of_le_of_lt (eigenvalue_le_trace_of_posSemidef K hK_psd i) htrK_lt
  have h_1_sub_pos : ∀ i, 0 < 1 - eig i := fun i => sub_pos.mpr (h_eig_lt_1 i)
  have h1t_pos : 0 < 1 - K.trace := sub_pos.mpr htrK_lt
  set invD := Matrix.diagonal (fun i => (1 - eig i)⁻¹) with invD_def
  set D := Matrix.diagonal (fun i => 1 - eig i) with D_def
  have hD_invD : D * invD = 1 := by
    rw [D_def, invD_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; exact mul_inv_cancel₀ (ne_of_gt (h_1_sub_pos i))
  have hIK_eq : (1 : Matrix V V ℝ) - K = eigQ * D * star eigQ := by
    rw [hK_eq]
    conv_lhs => rw [show (1 : Matrix V V ℝ) = eigQ * star eigQ from hQ_mul_star.symm]
    rw [show eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
        eigQ * ((1 : Matrix V V ℝ) - Matrix.diagonal eig) * star eigQ from by
          conv_lhs =>
            rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one]]
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]]
    congr 1
    congr 1
    rw [D_def]
    ext i j; simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h_diag_det : IsUnit D.det := by
    rw [D_def, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (h_1_sub_pos i))
  have hIK_inv : ((1 : Matrix V V ℝ) - K)⁻¹ = eigQ * invD * star eigQ := by
    rw [hIK_eq]
    apply Matrix.inv_eq_right_inv
    calc eigQ * D * star eigQ * (eigQ * invD * star eigQ)
        = eigQ * D * (star eigQ * eigQ) * invD * star eigQ := by simp only [Matrix.mul_assoc]
      _ = eigQ * (D * invD) * star eigQ := by
          rw [hQ_star_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD_invD, Matrix.mul_one, hQ_mul_star]
  set U' := star eigQ * U * eigQ with hU'_def
  have hU'_psd : U'.PosSemidef := by
    rw [hU'_def, show star eigQ = eigQᴴ from rfl]
    exact hU.posSemidef.conjTranspose_mul_mul_same eigQ
  have trace_diag_mul : ∀ (f : V → ℝ) (M : Matrix V V ℝ),
      (Matrix.diagonal f * M).trace = ∑ i, f i * M i i := by
    intro f M
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => by simp [Ne.symm hj])]
    simp
  have htr_expand : (((1 : Matrix V V ℝ) - K)⁻¹ * U).trace =
      ∑ i, U' i i / (1 - eig i) := by
    rw [hIK_inv,
        show eigQ * invD * star eigQ * U = eigQ * (invD * (star eigQ * U)) from by
          simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show invD * (star eigQ * U) * eigQ = invD * (star eigQ * U * eigQ) from by
          simp only [Matrix.mul_assoc],
        ← hU'_def, invD_def, trace_diag_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_inv_mul]
  have htr_U : U.trace = ∑ i, U' i i := by
    rw [show U = eigQ * star eigQ * U from by rw [hQ_mul_star, one_mul],
        show eigQ * star eigQ * U = eigQ * (star eigQ * U) from Matrix.mul_assoc _ _ _,
        Matrix.trace_mul_comm, hU'_def]
    simp [Matrix.trace]
  have htr_KU : (K * U).trace = ∑ i, eig i * U' i i := by
    rw [hK_eq, show eigQ * Matrix.diagonal eig * star eigQ * U =
        eigQ * (Matrix.diagonal eig * (star eigQ * U)) from by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show Matrix.diagonal eig * (star eigQ * U) * eigQ =
          Matrix.diagonal eig * (star eigQ * U * eigQ) from by simp only [Matrix.mul_assoc],
        ← hU'_def, trace_diag_mul]
  have htr_KU_eq_BUU : (K * U).trace = (B * U * U).trace := by
    rw [hK_def]
    rw [show Uhalf * B * Uhalf * U = Uhalf * (B * Uhalf * U) from by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm, ← hUhalf_sq]
    simp only [Matrix.mul_assoc]
  rw [htr_expand, htr_U, ← htr_KU_eq_BUU, htr_KU, ← htrK]
  have hU'_diag_nn : ∀ i, 0 ≤ U' i i := fun i => hU'_psd.diag_nonneg
  have h_split_sum : ∑ i : V, U' i i / (1 - eig i) =
      ∑ i : V, U' i i + ∑ i : V, eig i * U' i i / (1 - eig i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    field_simp [ne_of_gt (h_1_sub_pos i)]
    ring
  rw [h_split_sum]
  gcongr
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_left (mul_nonneg (h_eig_nn i) (hU'_diag_nn i)) h1t_pos
  linarith [eigenvalue_le_trace_of_posSemidef K hK_psd i]

lemma psd_resolvent_trace_bound
    (U B : Matrix V V ℝ)
    (hU : U.PosDef) (hB : B.PosSemidef)
    (htrBU_lt : (B * U).trace < 1)
    (_htrBU_nn : 0 ≤ (B * U).trace) :
    (U⁻¹ - B)⁻¹.trace ≤ U.trace + (B * U * U).trace / (1 - (B * U).trace) := by
  classical
  obtain ⟨Uhalf, hUhalf_herm, hUhalf_det, hUhalf_sq⟩ := posDef_sqrt_exists U hU
  set K := Uhalf * B * Uhalf with hK_def
  have hK_psd : K.PosSemidef := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalfᴴ * B * Uhalf from by rw [hUhalf_herm.eq]]
    exact hB.conjTranspose_mul_mul_same Uhalf
  have htrK : K.trace = (B * U).trace := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalf * (B * Uhalf) from Matrix.mul_assoc _ _ _,
      Matrix.trace_mul_comm Uhalf (B * Uhalf), Matrix.mul_assoc, hUhalf_sq]
  have htrK_lt : K.trace < 1 := htrK ▸ htrBU_lt
  have hconj_inv :=
    psd_resolvent_conj_inv U B Uhalf K hK_def hUhalf_sq hUhalf_det hK_psd htrK_lt
  exact psd_resolvent_trace_le U B Uhalf K hU hUhalf_sq hK_def hK_psd htrBU_lt hconj_inv

end Problem6

end
