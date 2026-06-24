/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Problem 6: Large epsilon-light vertex subsets -- Barrier Potential

BSS barrier potential `Phi_u(M) = tr((uI - M)^{-1})`, trace
monotonicity, barrier shift/decrease/gap lemmas, eigenvalue bounds,
unitary conjugation, and the Neumann-Loewner trace bound.

## Main definitions

- `Problem6.barrierPotential`: the upper barrier potential

## Main theorems

- `Problem6.trace_mul_nonneg_of_posSemidef`: `tr(PQ) >= 0` for PSD
- `Problem6.trace_mul_le_of_loewner`: trace monotonicity under Loewner
- `Problem6.barrier_potential_decrease`: barrier decrease estimate
- `Problem6.barrier_gap_pos`: positivity of barrier gap
- `Problem6.barrier_rearrange`: algebraic rearrangement lemma
- `Problem6.eigenvalue_le_trace_of_posSemidef`: eigenvalue-trace bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The upper barrier potential Φ_u(M) = tr((uI - M)⁻¹), defined for symmetric M
    with eigenvalues < u. -/
def barrierPotential (u : ℝ) (M : Matrix V V ℝ) : ℝ :=
  (u • (1 : Matrix V V ℝ) - M)⁻¹.trace

/-- Real form of the spectral theorem: a real Hermitian matrix equals
    `U * diagonal eigenvalues * star U` for its eigenvector unitary `U`. -/
lemma realSpectralDecomp {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Matrix V V ℝ) * diagonal hM.eigenvalues *
      star (hM.eigenvectorUnitary : Matrix V V ℝ) := by
  have h := hM.spectral_theorem
  simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
    RCLike.ofReal_real_eq_id, id] using h

omit [DecidableEq V] in
/-- PSD factorization via spectral theorem: P PSD implies P = Nᴴ * N for some N. -/
lemma psd_factorization (P : Matrix V V ℝ) (hP : P.PosSemidef) :
    ∃ (N : Matrix V V ℝ), P = Nᴴ * N := by
  classical
  set herm := hP.isHermitian
  set U := (herm.eigenvectorUnitary : Matrix V V ℝ)
  set eig := herm.eigenvalues
  have hP_eq : P = U * diagonal eig * star U := realSpectralDecomp herm
  have h_nn := hP.eigenvalues_nonneg
  set sqrt_eig := fun i => Real.sqrt (eig i)
  use diagonal sqrt_eig * star U
  have hNH : (diagonal sqrt_eig * star U)ᴴ = U * diagonal sqrt_eig := by
    rw [conjTranspose_mul,
        show (star U : Matrix V V ℝ)ᴴ = U from conjTranspose_conjTranspose U,
        diagonal_conjTranspose]
    simp only [star_trivial]
  have h_sqrt_sq : diagonal sqrt_eig * diagonal sqrt_eig = diagonal eig := by
    rw [diagonal_mul_diagonal]; congr 1; ext i; exact Real.mul_self_sqrt (h_nn i)
  rw [hP_eq, hNH, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal sqrt_eig), h_sqrt_sq]

/-- The Hermitian, invertible square root of a positive definite matrix. -/
lemma posDef_sqrt_exists (U : Matrix V V ℝ) (hU : U.PosDef) :
    ∃ R : Matrix V V ℝ, R.IsHermitian ∧ IsUnit R.det ∧ R * R = U := by
  classical
  set hU_herm := hU.isHermitian
  set eigP := (hU_herm.eigenvectorUnitary : Matrix V V ℝ)
  set d := hU_herm.eigenvalues
  have hP_star_mul : star eigP * eigP = 1 := Unitary.coe_star_mul_self hU_herm.eigenvectorUnitary
  have hP_mul_star : eigP * star eigP = 1 := Unitary.coe_mul_star_self hU_herm.eigenvectorUnitary
  have hU_eq : U = eigP * Matrix.diagonal d * star eigP := realSpectralDecomp hU_herm
  set sqrtd := fun i => Real.sqrt (d i) with sqrtd_def
  set Uhalf := eigP * Matrix.diagonal sqrtd * star eigP with Uhalf_def
  have hsqrtd_ne : ∀ i, sqrtd i ≠ 0 := fun i =>
    ne_of_gt (Real.sqrt_pos_of_pos (hU.eigenvalues_pos i))
  have hUhalf_sq : Uhalf * Uhalf = U := by
    rw [Uhalf_def, hU_eq]
    calc eigP * Matrix.diagonal sqrtd * star eigP *
          (eigP * Matrix.diagonal sqrtd * star eigP)
        = eigP * Matrix.diagonal sqrtd * (star eigP * eigP) *
              Matrix.diagonal sqrtd * star eigP := by simp only [Matrix.mul_assoc]
      _ = eigP * (Matrix.diagonal sqrtd * Matrix.diagonal sqrtd) * star eigP := by
          rw [hP_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = eigP * Matrix.diagonal d * star eigP := by
          have h : Matrix.diagonal (fun i => sqrtd i * sqrtd i) = Matrix.diagonal d := by
            congr 1
            ext i
            exact Real.mul_self_sqrt (le_of_lt (hU.eigenvalues_pos i))
          rw [Matrix.diagonal_mul_diagonal, h]
  have hUhalf_herm : Uhalf.IsHermitian := by
    rw [Uhalf_def, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      (show (Matrix.diagonal sqrtd).IsHermitian from by simp [Matrix.IsHermitian]).eq,
      Matrix.mul_assoc]
  have hUhalf_det : IsUnit Uhalf.det := by
    rw [Uhalf_def, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    exact IsUnit.mul (IsUnit.mul
      (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_mul_star, Matrix.det_one]))
      (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hsqrtd_ne i)))
      (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_star_mul, Matrix.det_one]))
  exact ⟨Uhalf, hUhalf_herm, hUhalf_det, hUhalf_sq⟩

omit [DecidableEq V] in
/-- For PSD matrices P, Q over ℝ, tr(P * Q) ≥ 0.
    Proof: write P = Nᴴ * N, then tr(PQ) = tr(NQNᴴ) ≥ 0 since NQNᴴ is PSD. -/
lemma trace_mul_nonneg_of_posSemidef
    (P Q : Matrix V V ℝ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace := by
  obtain ⟨N, hN⟩ := psd_factorization P hP
  rw [hN, mul_assoc, Matrix.trace_mul_comm]
  exact (hQ.mul_mul_conjTranspose_same N).trace_nonneg

omit [DecidableEq V] in
/-- Trace monotonicity under Loewner order: if X ≤ Y (Loewner) and C ≥ 0,
    then tr(X * C) ≤ tr(Y * C). This follows from tr((Y-X)*C) ≥ 0
    since Y-X ≥ 0 and C ≥ 0. -/
lemma trace_mul_le_of_loewner
    (X Y C : Matrix V V ℝ)
    (hXY : (Y - X).PosSemidef) (hC : C.PosSemidef) :
    (X * C).trace ≤ (Y * C).trace := by
  have h := trace_mul_nonneg_of_posSemidef (Y - X) C hXY hC
  rw [Matrix.sub_mul] at h
  linarith [Matrix.trace_sub (Y * C) (X * C)]

omit [Fintype V] in
/-- Helper: u'I - M is positive definite when uI - M is positive definite and u' > u. -/
lemma barrier_shift_posDef
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    (u' • (1 : Matrix V V ℝ) - M).PosDef := by
  have h_eq : u' • (1 : Matrix V V ℝ) - M =
    (u • (1 : Matrix V V ℝ) - M) + (u' - u) • (1 : Matrix V V ℝ) := by
    simp [sub_smul]
  rw [h_eq]
  exact hM.add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hu.le))

/-- The barrier potential decreases as the barrier level increases:
    Φ_u(M) - Φ_{u'}(M) ≥ δ · tr(U²) where δ = u' - u and U = (u'I - M)⁻¹. -/
lemma barrier_potential_decrease
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    barrierPotential u M - barrierPotential u' M ≥
      (u' - u) * ((u' • (1 : Matrix V V ℝ) - M)⁻¹ *
        (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace := by
  -- Abbreviate A = uI - M, B = u'I - M
  set A := u • (1 : Matrix V V ℝ) - M with hA_def
  set B := u' • (1 : Matrix V V ℝ) - M with hB_def
  -- Step 1: B is PD (B = A + (u'-u)I, A is PD, (u'-u)I is PSD)
  have hB_eq : B = A + (u' - u) • (1 : Matrix V V ℝ) := by
    simp only [hA_def, hB_def, sub_smul]; abel
  have h_smul_psd : ((u' - u) • (1 : Matrix V V ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sub_nonneg.mpr hu.le)
  have hB : B.PosDef := hB_eq ▸ hM.add_posSemidef h_smul_psd
  -- Step 2: Both A and B are invertible (PD over a field)
  have hAu : IsUnit A := hM.isUnit
  have hBu : IsUnit B := hB.isUnit
  -- Step 3: Resolvent identity:
  --   A⁻¹ - B⁻¹ = A⁻¹(B-A)B⁻¹ = (u'-u)·(A⁻¹·B⁻¹)
  have hBA : B - A = (u' - u) • (1 : Matrix V V ℝ) := by
    simp only [hA_def, hB_def, sub_smul]; abel
  have hres2 : A⁻¹ - B⁻¹ = (u' - u) • (A⁻¹ * B⁻¹) := by
    rw [Matrix.inv_sub_inv (iff_of_true hAu hBu), hBA, mul_assoc]
    simp
  -- Step 4: tr(A⁻¹) - tr(B⁻¹) = (u'-u) * tr(A⁻¹ * B⁻¹)
  have htrace : barrierPotential u M - barrierPotential u' M =
      (u' - u) * (A⁻¹ * B⁻¹).trace := by
    unfold barrierPotential
    -- Convert u•1-M back to A, u'•1-M back to B, so hres2 can match
    simp only [← hA_def, ← hB_def]
    rw [← Matrix.trace_sub, hres2, Matrix.trace_smul, smul_eq_mul]
  -- Step 5: A⁻¹ is PSD, B⁻¹*B⁻¹ is PSD
  have hA_inv_psd : A⁻¹.PosSemidef := hM.inv.posSemidef
  have hB_sq_psd : (B⁻¹ * B⁻¹).PosSemidef := by
    have hBherm : B⁻¹.IsHermitian := hB.inv.isHermitian
    rw [show B⁻¹ * B⁻¹ = B⁻¹ᴴ * B⁻¹ from by rw [hBherm]]
    exact Matrix.posSemidef_conjTranspose_mul_self B⁻¹
  -- Step 6: tr(A⁻¹ * B⁻¹) ≥ tr(B⁻² ) [using trace_mul_nonneg]
  have hkey : (B⁻¹ * B⁻¹).trace ≤ (A⁻¹ * B⁻¹).trace := by
    have h1 : 0 ≤ ((A⁻¹ - B⁻¹) * B⁻¹).trace := by
      rw [hres2, smul_mul_assoc, Matrix.trace_smul]
      apply mul_nonneg (sub_nonneg.mpr hu.le)
      rw [Matrix.mul_assoc]
      exact trace_mul_nonneg_of_posSemidef A⁻¹ (B⁻¹ * B⁻¹) hA_inv_psd hB_sq_psd
    have hsplit : (A⁻¹ * B⁻¹).trace =
        (B⁻¹ * B⁻¹).trace + ((A⁻¹ - B⁻¹) * B⁻¹).trace := by
      rw [Matrix.sub_mul, Matrix.trace_sub]; ring
    linarith
  -- Step 7: Conclude
  rw [htrace]
  exact mul_le_mul_of_nonneg_left hkey (sub_nonneg.mpr hu.le)

/-- Helper: the barrier potential gap is positive when u' > u and M ≺ uI.
    Requires Nonempty V since trace is 0 on the empty type. -/
lemma barrier_gap_pos [Nonempty V]
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    0 < barrierPotential u M - barrierPotential u' M := by
  have h_dec := barrier_potential_decrease M u u' hu hM
  have hB := barrier_shift_posDef M u u' hu hM
  -- tr(U²) > 0 since U = (u'I-M)⁻¹ is positive definite
  have hU_pd : ((u' • (1 : Matrix V V ℝ) - M)⁻¹).PosDef := hB.inv
  have hU_sq_pd : ((u' • (1 : Matrix V V ℝ) - M)⁻¹ *
      (u' • (1 : Matrix V V ℝ) - M)⁻¹).PosDef := by
    set U' := (u' • (1 : Matrix V V ℝ) - M)⁻¹
    have hUherm := hU_pd.isHermitian
    rw [show U' * U' = U'ᴴ * U' from by rw [hUherm]]
    exact Matrix.PosDef.conjTranspose_mul_self U'
      (Matrix.mulVec_injective_of_isUnit hU_pd.isUnit)
  linarith [mul_pos (sub_pos.mpr hu) hU_sq_pd.trace_pos]

/-- Key scalar rearrangement: if a + b/c ≤ 1 with c > 0 and 0 ≤ a < 1, 0 ≤ b,
    then b/(1-a) ≤ c. This is the algebraic core of the barrier argument. -/
lemma barrier_rearrange {a b c : ℝ} (hc : 0 < c)
    (_ha_nn : 0 ≤ a) (_hb_nn : 0 ≤ b) (ha_lt : a < 1)
    (hbarr : a + b / c ≤ 1) :
    b / (1 - a) ≤ c := by
  have h1ma : (0 : ℝ) < 1 - a := by linarith
  rw [div_le_iff₀ h1ma]
  have hbc : b / c ≤ 1 - a := by linarith [div_nonneg _hb_nn hc.le]
  calc b = (b / c) * c := by rw [div_mul_cancel₀ b (ne_of_gt hc)]
    _ ≤ (1 - a) * c := by nlinarith
    _ = c * (1 - a) := by ring

/-- For a PSD matrix, each eigenvalue is at most the trace. -/
lemma eigenvalue_le_trace_of_posSemidef
    (K : Matrix V V ℝ)
    (hK : K.PosSemidef)
    (i : V) :
    hK.isHermitian.eigenvalues i ≤ K.trace := by
  classical
  have hK_herm := hK.isHermitian
  have h_eig_nn := hK.eigenvalues_nonneg
  -- trace = sum of eigenvalues (for real Hermitian matrices, ofReal is the identity on ℝ)
  have htr : K.trace = ∑ j, hK_herm.eigenvalues j := by
    have h := hK_herm.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at h
    exact h
  rw [htr]
  exact Finset.single_le_sum (fun j _ => h_eig_nn j) (Finset.mem_univ i)

/-- If `K` is PSD with trace `< 1`, then `I - K` is positive definite. -/
lemma one_sub_posDef_of_trace_lt_one (K : Matrix V V ℝ) (hK_psd : K.PosSemidef)
    (htrK_lt : K.trace < 1) :
    ((1 : Matrix V V ℝ) - K).PosDef := by
  classical
  set hK_herm := hK_psd.isHermitian
  set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ)
  set eig := hK_herm.eigenvalues
  have hQ_mul_star : eigQ * star eigQ = 1 := Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
  have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := realSpectralDecomp hK_herm
  have h_eig_lt_1 : ∀ i, eig i < 1 := fun i =>
    lt_of_le_of_lt (eigenvalue_le_trace_of_posSemidef K hK_psd i) htrK_lt
  have hQ_unit : IsUnit (eigQ : Matrix V V ℝ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hQ_mul_star, Matrix.det_one])
  rw [hK_eq, ← hQ_mul_star,
      show eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
        eigQ * Matrix.diagonal (fun i => 1 - eig i) * star eigQ from by
          rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one],
              ← Matrix.sub_mul, ← Matrix.mul_sub]
          congr 2; ext i j
          simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
          split_ifs <;> simp,
      hQ_unit.posDef_star_right_conjugate_iff]
  exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (h_eig_lt_1 i))

end Problem6

end
