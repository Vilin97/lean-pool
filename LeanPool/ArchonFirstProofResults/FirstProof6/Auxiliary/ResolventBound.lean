/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.BarrierPotential

/-!
# Problem 6: Large epsilon-light vertex subsets -- Resolvent Bound

The main lemma `psd_resolvent_trace_bound` establishing:
`tr((U^{-1} - B)^{-1}) <= tr(U) + tr(B*U^2) / (1 - tr(B*U))`
via matrix square root and spectral decomposition.

## Main theorems

- `Problem6.psd_resolvent_trace_bound`: PSD resolvent trace bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A positive-definite matrix has a Hermitian, invertible square root
(constructed via the spectral decomposition). -/
private lemma psd_resolvent_sqrt (U : Matrix V V ℝ) (hU : U.PosDef) :
    ∃ R : Matrix V V ℝ, R.IsHermitian ∧ IsUnit R.det ∧ R * R = U := by
  classical
  set hU_herm := hU.isHermitian with hU_herm_def
  set eigP := (hU_herm.eigenvectorUnitary : Matrix V V ℝ) with hP_def
  set d := hU_herm.eigenvalues with hd_def
  have hP_star_mul : star eigP * eigP = 1 :=
    Unitary.coe_star_mul_self hU_herm.eigenvectorUnitary
  have hP_mul_star : eigP * star eigP = 1 :=
    Unitary.coe_mul_star_self hU_herm.eigenvectorUnitary
  have hU_eq : U = eigP * Matrix.diagonal d * star eigP := by
    have h := hU_herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at h
    exact h
  have hd_pos : ∀ i, 0 < d i := hU.eigenvalues_pos
  set sqrtd := fun i => Real.sqrt (d i) with sqrtd_def
  set Uhalf := eigP * Matrix.diagonal sqrtd * star eigP with Uhalf_def
  have hsqrtd_pos : ∀ i, 0 < sqrtd i := fun i => Real.sqrt_pos_of_pos (hd_pos i)
  have hsqrtd_ne : ∀ i, sqrtd i ≠ 0 := fun i => ne_of_gt (hsqrtd_pos i)
  have hUhalf_sq : Uhalf * Uhalf = U := by
    rw [Uhalf_def, hU_eq]
    calc eigP * Matrix.diagonal sqrtd * star eigP *
        (eigP * Matrix.diagonal sqrtd * star eigP)
      = eigP * Matrix.diagonal sqrtd * (star eigP * eigP) *
          Matrix.diagonal sqrtd * star eigP := by
          simp only [Matrix.mul_assoc]
      _ = eigP * (Matrix.diagonal sqrtd * Matrix.diagonal sqrtd) * star eigP := by
          rw [hP_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = eigP * Matrix.diagonal d * star eigP := by
          rw [Matrix.diagonal_mul_diagonal]
          have hsq : (fun i => sqrtd i * sqrtd i) = d := by
            ext i; exact Real.mul_self_sqrt (le_of_lt (hd_pos i))
          rw [hsq]
  have hdiag_herm : (Matrix.diagonal sqrtd).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply, star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hUhalf_herm : Uhalf.IsHermitian := by
    rw [Uhalf_def, Matrix.IsHermitian]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hdiag_herm.eq,
      Matrix.mul_assoc]
  have hUhalf_det : IsUnit Uhalf.det := by
    rw [Uhalf_def, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (IsUnit.mul ?_ ?_) ?_
    · exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_mul_star, Matrix.det_one])
    · exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hsqrtd_ne i)
    · exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_star_mul, Matrix.det_one])
  exact ⟨Uhalf, hUhalf_herm, hUhalf_det, hUhalf_sq⟩

/-- **Conjugation-inverse identity**: with `Uhalf` a Hermitian invertible square root of `U`
and `K = Uhalf · B · Uhalf` positive semidefinite with `tr(K) < 1`,
`(U⁻¹ - B)⁻¹ = Uhalf · (I - K)⁻¹ · Uhalf`. -/
private lemma psd_resolvent_conj_inv (U B Uhalf K : Matrix V V ℝ)
    (hK_def : K = Uhalf * B * Uhalf) (hUhalf_sq : Uhalf * Uhalf = U)
    (hUhalf_det : IsUnit Uhalf.det) (hK_psd : K.PosSemidef) (htrK_lt : K.trace < 1) :
    (U⁻¹ - B)⁻¹ = Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
  classical
  have hUhalf_inv_sq : Uhalf⁻¹ * Uhalf⁻¹ = U⁻¹ := by
    rw [← hUhalf_sq]
    symm
    exact Matrix.mul_inv_rev Uhalf Uhalf
  have hUinv_sub_B : U⁻¹ - B = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ := by
    have hUU : Uhalf⁻¹ * Uhalf = 1 := Matrix.nonsing_inv_mul Uhalf hUhalf_det
    have hUU' : Uhalf * Uhalf⁻¹ = 1 := Matrix.mul_nonsing_inv Uhalf hUhalf_det
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hUhalf_inv_sq]
    congr 1
    rw [hK_def]
    symm
    calc Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹
        = (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * B * 1 := by rw [hUU, hUU']
      _ = B := by rw [one_mul, mul_one]
  have hUU_cancel : Uhalf⁻¹ * Uhalf = 1 := Matrix.nonsing_inv_mul Uhalf hUhalf_det
  have hUU'_cancel : Uhalf * Uhalf⁻¹ = 1 := Matrix.mul_nonsing_inv Uhalf hUhalf_det
  rw [hUinv_sub_B]
  have hIK_pd : ((1 : Matrix V V ℝ) - K).PosDef := by
    set hK_herm := hK_psd.isHermitian
    set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ)
    set eig := hK_herm.eigenvalues
    have hQ_star_mul : star eigQ * eigQ = 1 :=
      Unitary.coe_star_mul_self hK_herm.eigenvectorUnitary
    have hQ_mul_star : eigQ * star eigQ = 1 :=
      Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
    have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := by
      have h := hK_herm.spectral_theorem
      simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
        RCLike.ofReal_real_eq_id, id] at h; exact h
    have h_eig_lt_1 : ∀ i, eig i < 1 := fun i =>
      lt_of_le_of_lt (eigenvalue_le_trace_of_posSemidef K hK_psd i) htrK_lt
    have h_1_sub_pos : ∀ i, 0 < 1 - eig i := fun i => sub_pos.mpr (h_eig_lt_1 i)
    rw [hK_eq]
    have h_one_eq : (1 : Matrix V V ℝ) = eigQ * star eigQ := hQ_mul_star.symm
    rw [h_one_eq]
    have h_sub_eq : eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
        eigQ * Matrix.diagonal (fun i => 1 - eig i) * star eigQ := by
      conv_lhs =>
        rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one]]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 1; congr 1
      ext i j
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    rw [h_sub_eq]
    have hQ_unit : IsUnit (eigQ : Matrix V V ℝ) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact IsUnit.of_mul_eq_one _
        (by rw [← Matrix.det_mul, hQ_mul_star, Matrix.det_one])
    rw [hQ_unit.posDef_star_right_conjugate_iff]
    exact Matrix.PosDef.diagonal h_1_sub_pos
  have h_inv_prod : (Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹)⁻¹ =
      Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
    have hIK_det : IsUnit ((1 : Matrix V V ℝ) - K).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hIK_pd.isUnit
    have hIK_cancel : ((1 : Matrix V V ℝ) - K) *
        ((1 : Matrix V V ℝ) - K)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hIK_det
    have h_prod : (Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹) *
        (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) = 1 := by
      calc Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ *
            (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf)
          = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) *
              (Uhalf⁻¹ * Uhalf) * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
            simp only [Matrix.mul_assoc]
        _ = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * 1 *
              ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
            rw [hUU_cancel]
        _ = Uhalf⁻¹ * (((1 : Matrix V V ℝ) - K) *
              ((1 : Matrix V V ℝ) - K)⁻¹) * Uhalf := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = Uhalf⁻¹ * 1 * Uhalf := by rw [hIK_cancel]
        _ = 1 := by rw [Matrix.mul_one, hUU_cancel]
    exact Matrix.inv_eq_right_inv h_prod
  exact h_inv_prod

/-- **Eigenvalue inequality**: given the conjugation-inverse identity, bound the trace by
diagonalizing `K` and applying the pointwise estimate `1 / (1 - λᵢ) ≤ 1 / (1 - tr K)`. -/
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
    rw [show Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf =
        Uhalf * (((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc, hUhalf_sq]
  rw [htr_rewrite]
  set hK_herm := hK_psd.isHermitian with hK_herm_def
  set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ) with hQ_def
  set eig := hK_herm.eigenvalues with heig_def
  have hQ_star_mul : star eigQ * eigQ = 1 :=
    Unitary.coe_star_mul_self hK_herm.eigenvectorUnitary
  have hQ_mul_star : eigQ * star eigQ = 1 :=
    Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
  have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := by
    have h := hK_herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at h; exact h
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
  have hIK_eq : (1 : Matrix V V ℝ) - K =
      eigQ * D * star eigQ := by
    rw [hK_eq]
    conv_lhs => rw [show (1 : Matrix V V ℝ) = eigQ * star eigQ from hQ_mul_star.symm]
    rw [show eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
      eigQ * ((1 : Matrix V V ℝ) - Matrix.diagonal eig) * star eigQ from by
        conv_lhs =>
          rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one]]
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]]
    congr 1; congr 1
    rw [D_def]
    ext i j; simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h_diag_det : IsUnit D.det := by
    rw [D_def, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (h_1_sub_pos i))
  have hIK_inv : ((1 : Matrix V V ℝ) - K)⁻¹ = eigQ * invD * star eigQ := by
    rw [hIK_eq]
    have h_prod : (eigQ * D * star eigQ) * (eigQ * invD * star eigQ) = 1 := by
      calc eigQ * D * star eigQ * (eigQ * invD * star eigQ)
          = eigQ * D * (star eigQ * eigQ) * invD * star eigQ := by
            simp only [Matrix.mul_assoc]
        _ = eigQ * (D * invD) * star eigQ := by
            rw [hQ_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = eigQ * star eigQ := by rw [hD_invD, Matrix.mul_one]
        _ = 1 := hQ_mul_star
    exact Matrix.inv_eq_right_inv h_prod
  set U' := star eigQ * U * eigQ with hU'_def
  have hU'_psd : U'.PosSemidef := by
    rw [hU'_def, show star eigQ = eigQᴴ from rfl]
    exact hU.posSemidef.conjTranspose_mul_mul_same eigQ
  have trace_diag_mul : ∀ (f : V → ℝ) (M : Matrix V V ℝ),
      (Matrix.diagonal f * M).trace = ∑ i, f i * M i i := by
    intro f M
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro i _
    have : ∀ j ∈ Finset.univ, j ≠ i → (if i = j then f i else 0) * M j i = 0 := by
      intro j _ hj; simp [Ne.symm hj]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) this]
    simp
  have htr_expand : (((1 : Matrix V V ℝ) - K)⁻¹ * U).trace =
      ∑ i, U' i i / (1 - eig i) := by
    rw [hIK_inv]
    rw [show eigQ * invD * star eigQ * U =
        eigQ * (invD * (star eigQ * U)) from by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show invD * (star eigQ * U) * eigQ =
        invD * (star eigQ * U * eigQ) from by simp only [Matrix.mul_assoc]]
    rw [← hU'_def, invD_def, trace_diag_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [div_eq_inv_mul]
  have htr_U : U.trace = ∑ i, U' i i := by
    rw [show U = eigQ * star eigQ * U from by rw [hQ_mul_star, one_mul]]
    rw [show eigQ * star eigQ * U = eigQ * (star eigQ * U) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm]
    rw [show star eigQ * U * eigQ = star eigQ * U * eigQ from rfl]
    rfl
  have htr_KU : (K * U).trace = ∑ i, eig i * U' i i := by
    rw [hK_eq]
    rw [show eigQ * Matrix.diagonal eig * star eigQ * U =
        eigQ * (Matrix.diagonal eig * (star eigQ * U)) from by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Matrix.diagonal eig * (star eigQ * U) * eigQ =
        Matrix.diagonal eig * (star eigQ * U * eigQ) from by simp only [Matrix.mul_assoc]]
    rw [← hU'_def, trace_diag_mul]
  have htr_KU_eq_BUU : (K * U).trace = (B * U * U).trace := by
    rw [hK_def]
    rw [show Uhalf * B * Uhalf * U = Uhalf * (B * Uhalf * U) from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [← hUhalf_sq]
    simp only [Matrix.mul_assoc]
  rw [htr_expand, htr_U, ← htr_KU_eq_BUU, htr_KU, ← htrK]
  have hU'_diag_nn : ∀ i, 0 ≤ U' i i := fun i => hU'_psd.diag_nonneg
  have h_split_sum : ∑ i : V, U' i i / (1 - eig i) =
      ∑ i : V, U' i i + ∑ i : V, eig i * U' i i / (1 - eig i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h1 : (1 - eig i) ≠ 0 := ne_of_gt (h_1_sub_pos i)
    field_simp; ring
  rw [h_split_sum]
  gcongr
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_left (mul_nonneg (h_eig_nn i) (hU'_diag_nn i)) h1t_pos
  linarith [eigenvalue_le_trace_of_posSemidef K hK_psd i]

/-- **PSD resolvent trace bound**: If `U` is PD, `B` is PSD, and `tr(B·U) < 1`, then
`tr((U⁻¹ - B)⁻¹) ≤ tr(U) + tr(B·U²) / (1 - tr(B·U))`.
The proof uses the matrix square root `U^{1/2}`, the conjugation identity
`(U⁻¹ - B)⁻¹ = U^{1/2}·(I - K)⁻¹·U^{1/2}` with `K = U^{1/2}·B·U^{1/2}`,
and a spectral (eigenvalue) estimate. -/
lemma psd_resolvent_trace_bound
    (U B : Matrix V V ℝ)
    (hU : U.PosDef) (hB : B.PosSemidef)
    (htrBU_lt : (B * U).trace < 1)
    (_htrBU_nn : 0 ≤ (B * U).trace) :
    (U⁻¹ - B)⁻¹.trace ≤ U.trace + (B * U * U).trace / (1 - (B * U).trace) := by
  classical
  obtain ⟨Uhalf, hUhalf_herm, hUhalf_det, hUhalf_sq⟩ := psd_resolvent_sqrt U hU
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
