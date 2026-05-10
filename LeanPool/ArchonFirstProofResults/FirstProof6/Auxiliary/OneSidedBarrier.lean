/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ResolventBound

/-!
# Problem 6: Large epsilon-light vertex subsets -- One-Sided Barrier

One-sided barrier machinery for the BSS coloring argument.

## Main theorems

- `Problem6.barrier_smw_trace_bound`: SMW-based trace bound
- `Problem6.one_sided_barrier`: barrier propagation (Lemma 6.1)
- `Problem6.inv_sub_posDef_of_trace_lt_one`: PD propagation
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sublemma 6.1a (Trace bound via SMW)**: Under the barrier hypotheses,
    Φ_{u'}(M+B) ≤ Φ_{u'}(M) + tr(B·U²) / (1 - tr(B·U)).
    This uses the PSD resolvent trace bound applied with U = (u'I-M)⁻¹. -/
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
  -- Set A = u'I - M (positive definite) and U = A⁻¹ (positive definite)
  set A := u' • (1 : Matrix V V ℝ) - M with hA_def
  set U := A⁻¹ with hU_def
  have hA_pd : A.PosDef := barrier_shift_posDef M u u' hu hM_bound
  have hU_pd : U.PosDef := hA_pd.inv
  -- Key identity: A - B = U⁻¹ - B (since U = A⁻¹, so U⁻¹ = A)
  have hAU : U⁻¹ = A := by
    rw [hU_def]
    exact Matrix.nonsing_inv_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA_pd.isUnit)
  -- Φ_{u'}(M+B) = tr((u'I - M - B)⁻¹) = tr((A - B)⁻¹) = tr((U⁻¹ - B)⁻¹)
  have hgoal_eq : barrierPotential u' (M + B) = (U⁻¹ - B)⁻¹.trace := by
    unfold barrierPotential
    congr 1; rw [hAU, hA_def]; simp [sub_sub]
  -- Φ_{u'}(M) = tr(U)
  have hphi_eq : barrierPotential u' M = U.trace := by
    unfold barrierPotential; rw [hU_def]
  -- tr(BU²) and tr(BU) expressed using U
  have hBU_eq : (B * U).trace = (B * A⁻¹).trace := by rfl
  have hBU2_eq : (B * U * U).trace = (B * A⁻¹ * A⁻¹).trace := by rfl
  rw [hgoal_eq, hphi_eq]
  exact psd_resolvent_trace_bound U B hU_pd hB htrBU_lt htrBU_nn

/-- **Lemma 6.1 (One-sided barrier)**: If M ≺ uI, u' > u, B ≽ 0, and the
    barrier condition holds, then M + B ≺ u'I and Φ_{u'}(M + B) ≤ Φ_u(M). -/
lemma one_sided_barrier
    (M B : Matrix V V ℝ)
    (u u' : ℝ) (hu : u < u')
    (hM_bound : (u • (1 : Matrix V V ℝ) - M).PosDef)
    (hB : B.PosSemidef)
    (hbarrier : let U := (u' • (1 : Matrix V V ℝ) - M)⁻¹
      (B * U).trace + (B * U * U).trace / (barrierPotential u M - barrierPotential u' M) ≤ 1) :
    barrierPotential u' (M + B) ≤ barrierPotential u M := by
  -- Handle empty V case: all traces are 0, so both sides equal 0
  by_cases hne : IsEmpty V
  · simp only [barrierPotential, Matrix.trace]
    simp
  · haveI : Nonempty V := not_isEmpty_iff.mp hne
    -- Abbreviations
    set U := (u' • (1 : Matrix V V ℝ) - M)⁻¹ with hU_def
    set trBU := (B * U).trace with htrBU_def
    set trBU2 := (B * U * U).trace with htrBU2_def
    set gap := barrierPotential u M - barrierPotential u' M with hgap_def
    -- Step 1: gap > 0
    have hgap_pos : 0 < gap := barrier_gap_pos M u u' hu hM_bound
    -- Step 2: u'I - M is PD, so U is PD
    have hB' := barrier_shift_posDef M u u' hu hM_bound
    have hU_pd : U.PosDef := hB'.inv
    -- Step 3: tr(BU) ≥ 0 (product of PSD matrices)
    have htrBU_nn : 0 ≤ trBU :=
      trace_mul_nonneg_of_posSemidef B U hB hU_pd.posSemidef
    -- Step 4: tr(BU²) ≥ 0
    have hU_sq_psd : (U * U).PosSemidef := by
      rw [show U * U = Uᴴ * U from by rw [hU_pd.isHermitian]]
      exact Matrix.posSemidef_conjTranspose_mul_self U
    have htrBU2_nn : 0 ≤ trBU2 := by
      rw [htrBU2_def, Matrix.mul_assoc]
      exact trace_mul_nonneg_of_posSemidef B (U * U) hB hU_sq_psd
    -- Step 5: From barrier condition, tr(BU) ≤ 1 and tr(BU) + tr(BU²)/gap ≤ 1
    have hbarrier' : trBU + trBU2 / gap ≤ 1 := hbarrier
    -- If trBU2 > 0, then trBU < 1 strictly (since trBU2/gap > 0)
    -- If trBU2 = 0, the conclusion follows from monotonicity of Φ
    by_cases htrBU2_pos : trBU2 = 0
    · -- Case B contributes no trace to U²:
      -- barrierPotential u' (M+B) ≤ barrierPotential u' M ≤ barrierPotential u M
      -- The first inequality uses barrier_smw_trace_bound with trBU2=0 and trBU ≤ 1
      -- The second uses monotonicity (gap > 0)
      -- In fact, with trBU2 = 0 and gap > 0: trBU ≤ 1 from hbarrier'
      have htrBU_le : trBU ≤ 1 := by linarith [div_nonneg htrBU2_nn hgap_pos.le]
      -- Use barrier_smw_trace_bound if trBU < 1, or handle trBU = 1 directly
      by_cases htrBU_eq : trBU = 1
      · -- trBU = 1, trBU2 = 0: Show B = 0 from tr(BU²) = 0.
        -- UBU is PSD (conjugation of PSD B by Hermitian U).
        -- tr(UBU) = tr(BU²) = 0, so UBU = 0, and U invertible gives B = 0.
        have hUherm : Uᴴ = U := hU_pd.isHermitian
        -- UBU is PSD: rewrite as Uᴴ * B * (Uᴴ)ᴴ and use mul_mul_conjTranspose_same
        have hUBU_psd : (U * B * U).PosSemidef := by
          have h := hB.mul_mul_conjTranspose_same Uᴴ
          rwa [hUherm, hUherm] at h
        have htr_eq : (U * B * U).trace = trBU2 := by
          rw [htrBU2_def, Matrix.mul_assoc,
              Matrix.trace_mul_comm, Matrix.mul_assoc]
        have hUBU_zero : U * B * U = 0 :=
          hUBU_psd.trace_eq_zero_iff.mp (by linarith [htr_eq])
        -- U is invertible, so B = U⁻¹ * 0 * U⁻¹ = 0
        have hU_det : IsUnit U.det :=
          (Matrix.isUnit_iff_isUnit_det U).mp hU_pd.isUnit
        have hB_zero : B = 0 := by
          have hUU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hU_det
          have hUU' : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU_det
          have h1 : U⁻¹ * (U * B * U) * U⁻¹ = B := by
            calc U⁻¹ * (U * B * U) * U⁻¹
                = U⁻¹ * U * B * (U * U⁻¹) := by
                  simp only [Matrix.mul_assoc]
              _ = 1 * B * 1 := by rw [hUU, hUU']
              _ = B := by rw [one_mul, mul_one]
          rw [hUBU_zero, Matrix.mul_zero, Matrix.zero_mul] at h1
          exact h1.symm
        -- With B = 0: M + B = M, and Φ_{u'}(M) ≤ Φ_u(M)
        rw [hB_zero, add_zero]
        linarith
      · have htrBU_lt : trBU < 1 := lt_of_le_of_ne htrBU_le htrBU_eq
        have h_smw := barrier_smw_trace_bound M B u u' hu hM_bound hB htrBU_lt htrBU_nn htrBU2_nn
        suffices h_suff : trBU2 / (1 - trBU) ≤ gap by linarith [h_smw]
        exact barrier_rearrange hgap_pos htrBU_nn htrBU2_nn htrBU_lt hbarrier'
    · -- Case trBU2 > 0: then trBU < 1 strictly
      have htrBU2_pos' : 0 < trBU2 := lt_of_le_of_ne htrBU2_nn (Ne.symm htrBU2_pos)
      have htrBU_lt : trBU < 1 := by
        have : 0 < trBU2 / gap := div_pos htrBU2_pos' hgap_pos
        linarith
      -- Step 6: Apply the SMW trace bound
      have h_smw := barrier_smw_trace_bound M B u u' hu hM_bound hB htrBU_lt htrBU_nn htrBU2_nn
      -- Step 7: Use barrier rearrangement to show the RHS ≤ Φ_u(M)
      suffices h_suff : trBU2 / (1 - trBU) ≤ gap by linarith [h_smw]
      exact barrier_rearrange hgap_pos htrBU_nn htrBU2_nn htrBU_lt hbarrier'

/-- **PosDef propagation**: If U is PD, B is PSD, and tr(B·U) < 1,
    then U⁻¹ - B is PD. This is the missing PosDef conclusion of the
    BSS barrier step (Lemma 6.1). The proof constructs U^{1/2} via spectral
    theorem, forms K = U^{1/2}·B·U^{1/2} with tr(K) < 1, shows I - K is PD
    (eigenvalue bound), and factors U⁻¹ - B = U^{-1/2}·(I-K)·U^{-1/2}. -/
lemma inv_sub_posDef_of_trace_lt_one
    (U B : Matrix V V ℝ)
    (hU : U.PosDef) (hB : B.PosSemidef)
    (htr : (B * U).trace < 1) :
    (U⁻¹ - B).PosDef := by
  classical
  -- === Step 0: Spectral decomposition of U (same pattern as psd_resolvent_trace_bound) ===
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
      RCLike.ofReal_real_eq_id, id] at h; exact h
  have hd_pos : ∀ i, 0 < d i := hU.eigenvalues_pos
  -- === Step 1: Construct U^{1/2} ===
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
  have hUU := Matrix.nonsing_inv_mul Uhalf hUhalf_det
  have hUU' := Matrix.mul_nonsing_inv Uhalf hUhalf_det
  have hUhalf_inv_sq : Uhalf⁻¹ * Uhalf⁻¹ = U⁻¹ := by
    rw [← hUhalf_sq]; symm; exact Matrix.mul_inv_rev Uhalf Uhalf
  -- === Step 2: K = Uhalf * B * Uhalf, PSD with tr(K) < 1 ===
  set K := Uhalf * B * Uhalf with hK_def
  have hK_psd : K.PosSemidef := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalfᴴ * B * Uhalf from by
      rw [hUhalf_herm.eq]]
    exact hB.conjTranspose_mul_mul_same Uhalf
  have htrK_lt : K.trace < 1 := by
    change (Uhalf * B * Uhalf).trace < 1
    have : (Uhalf * B * Uhalf).trace = (B * U).trace := by
      rw [show Uhalf * B * Uhalf = Uhalf * (B * Uhalf) from Matrix.mul_assoc _ _ _]
      rw [Matrix.trace_mul_comm Uhalf (B * Uhalf)]
      rw [Matrix.mul_assoc, hUhalf_sq]
    rwa [this]
  -- === Step 3: I - K is PD (same spectral argument as psd_resolvent_trace_bound) ===
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
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (h_eig_lt_1 i))
  -- === Step 4: U⁻¹ - B = Uhalf⁻¹ * (I-K) * Uhalf⁻¹ ===
  have hUinv_sub_B : U⁻¹ - B = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUhalf_inv_sq]
    congr 1; rw [hK_def]; symm
    calc Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹
        = (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * B * 1 := by rw [hUU, hUU']
      _ = B := by rw [one_mul, mul_one]
  -- === Step 5: Conclude PD via congruence ===
  rw [hUinv_sub_B]
  -- Uhalf⁻¹ is Hermitian (inverse of Hermitian invertible is Hermitian)
  have hUhalf_inv_herm : (Uhalf⁻¹)ᴴ = Uhalf⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]; congr 1
  have hUhalf_inv_unit : IsUnit Uhalf⁻¹ :=
    IsUnit.of_mul_eq_one Uhalf hUU
  rw [show Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ =
      Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * star Uhalf⁻¹ from by
    rw [star_eq_conjTranspose, hUhalf_inv_herm]]
  exact hUhalf_inv_unit.posDef_star_right_conjugate_iff.mpr hIK_pd
end Problem6

end
