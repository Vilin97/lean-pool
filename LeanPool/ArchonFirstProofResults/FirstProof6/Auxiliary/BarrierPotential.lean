/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Problem 6: Large epsilon-light vertex subsets -- Barrier Potential

BSS barrier potential `Phi_u(M) = tr((uI - M)^{-1})`, trace
monotonicity, barrier shift/decrease/gap lemmas, and eigenvalue bounds.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

def barrierPotential (u : ℝ) (M : Matrix V V ℝ) : ℝ :=
  (u • (1 : Matrix V V ℝ) - M)⁻¹.trace

omit [DecidableEq V] in
lemma psd_factorization (P : Matrix V V ℝ) (hP : P.PosSemidef) :
    ∃ (N : Matrix V V ℝ), P = Nᴴ * N := by
  classical
  set herm := hP.isHermitian
  set U := (herm.eigenvectorUnitary : Matrix V V ℝ)
  set eig := herm.eigenvalues
  have hP_eq : P = U * diagonal eig * star U := by
    have h := herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id] at h
    exact h
  set sqrt_eig := fun i => Real.sqrt (eig i)
  refine ⟨diagonal sqrt_eig * star U, ?_⟩
  have hNH : (diagonal sqrt_eig * star U)ᴴ = U * diagonal sqrt_eig := by
    rw [conjTranspose_mul, show (star U : Matrix V V ℝ)ᴴ = U from conjTranspose_conjTranspose U,
        diagonal_conjTranspose]; simp only [star_trivial]
  have h_sqrt_sq : diagonal sqrt_eig * diagonal sqrt_eig = diagonal eig := by
    rw [diagonal_mul_diagonal]; congr 1; ext i; exact Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
  rw [hP_eq, hNH, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal sqrt_eig),
      h_sqrt_sq]

omit [DecidableEq V] in
lemma trace_mul_nonneg_of_posSemidef
    (P Q : Matrix V V ℝ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace := by
  obtain ⟨N, hN⟩ := psd_factorization P hP
  rw [hN, mul_assoc, Matrix.trace_mul_comm]
  exact (hQ.mul_mul_conjTranspose_same N).trace_nonneg

omit [DecidableEq V] in
lemma trace_mul_le_of_loewner
    (X Y C : Matrix V V ℝ)
    (hXY : (Y - X).PosSemidef) (hC : C.PosSemidef) :
    (X * C).trace ≤ (Y * C).trace := by
  have h := trace_mul_nonneg_of_posSemidef (Y - X) C hXY hC
  rw [Matrix.sub_mul, Matrix.trace_sub] at h
  linarith

omit [Fintype V] in
lemma barrier_shift_posDef
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    (u' • (1 : Matrix V V ℝ) - M).PosDef := by
  have h_eq : u' • (1 : Matrix V V ℝ) - M =
      (u • (1 : Matrix V V ℝ) - M) + (u' - u) • (1 : Matrix V V ℝ) := by
    simp [sub_smul]
  rw [h_eq]; exact hM.add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hu.le))

lemma barrier_potential_decrease
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    barrierPotential u M - barrierPotential u' M ≥
      (u' - u) * ((u' • (1 : Matrix V V ℝ) - M)⁻¹ *
        (u' • (1 : Matrix V V ℝ) - M)⁻¹).trace := by
  set A := u • (1 : Matrix V V ℝ) - M with hA_def
  set B := u' • (1 : Matrix V V ℝ) - M with hB_def
  have hB : B.PosDef := by
    rw [show B = A + (u' - u) • (1 : Matrix V V ℝ) from by
      simp only [hA_def, hB_def, sub_smul]; abel]
    exact hM.add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hu.le))
  have hBA : B - A = (u' - u) • (1 : Matrix V V ℝ) := by
    simp only [hA_def, hB_def, sub_smul]; abel
  have hres2 : A⁻¹ - B⁻¹ = (u' - u) • (A⁻¹ * B⁻¹) := by
    rw [Matrix.inv_sub_inv (iff_of_true hM.isUnit hB.isUnit), hBA, Matrix.mul_assoc]
    simp
  have htrace : barrierPotential u M - barrierPotential u' M =
      (u' - u) * (A⁻¹ * B⁻¹).trace := by
    unfold barrierPotential
    simp only [← hA_def, ← hB_def]
    rw [← Matrix.trace_sub, hres2, Matrix.trace_smul, smul_eq_mul]
  have hA_inv_psd : A⁻¹.PosSemidef := hM.inv.posSemidef
  have hB_sq_psd : (B⁻¹ * B⁻¹).PosSemidef := by
    rw [show B⁻¹ * B⁻¹ = B⁻¹ᴴ * B⁻¹ from by rw [hB.inv.isHermitian]]
    exact Matrix.posSemidef_conjTranspose_mul_self B⁻¹
  have hkey : (B⁻¹ * B⁻¹).trace ≤ (A⁻¹ * B⁻¹).trace := by
    have h1 : 0 ≤ ((A⁻¹ - B⁻¹) * B⁻¹).trace := by
      rw [hres2, smul_mul_assoc, Matrix.trace_smul, Matrix.mul_assoc]
      exact mul_nonneg (sub_nonneg.mpr hu.le)
        (trace_mul_nonneg_of_posSemidef A⁻¹ (B⁻¹ * B⁻¹) hA_inv_psd hB_sq_psd)
    linarith [show (A⁻¹ * B⁻¹).trace = (B⁻¹ * B⁻¹).trace + ((A⁻¹ - B⁻¹) * B⁻¹).trace from by
      rw [Matrix.sub_mul, Matrix.trace_sub]; ring]
  rw [htrace]; exact mul_le_mul_of_nonneg_left hkey (sub_nonneg.mpr hu.le)

lemma barrier_gap_pos [Nonempty V]
    (M : Matrix V V ℝ) (u u' : ℝ) (hu : u < u')
    (hM : (u • (1 : Matrix V V ℝ) - M).PosDef) :
    0 < barrierPotential u M - barrierPotential u' M := by
  have h_dec := barrier_potential_decrease M u u' hu hM
  have hU_pd : ((u' • (1 : Matrix V V ℝ) - M)⁻¹).PosDef :=
    (barrier_shift_posDef M u u' hu hM).inv
  have hU_sq_pd : ((u' • (1 : Matrix V V ℝ) - M)⁻¹ *
      (u' • (1 : Matrix V V ℝ) - M)⁻¹).PosDef := by
    set U' := (u' • (1 : Matrix V V ℝ) - M)⁻¹
    rw [show U' * U' = U'ᴴ * U' from by rw [hU_pd.isHermitian]]
    exact Matrix.PosDef.conjTranspose_mul_self U' (Matrix.mulVec_injective_of_isUnit hU_pd.isUnit)
  linarith [mul_pos (sub_pos.mpr hu) hU_sq_pd.trace_pos]

lemma barrier_rearrange {a b c : ℝ} (hc : 0 < c)
    (_ha_nn : 0 ≤ a) (_hb_nn : 0 ≤ b) (ha_lt : a < 1)
    (hbarr : a + b / c ≤ 1) :
    b / (1 - a) ≤ c := by
  have h1ma : (0 : ℝ) < 1 - a := by linarith
  rw [div_le_iff₀ h1ma]
  have hbc : b / c ≤ 1 - a := by linarith [div_nonneg _hb_nn hc.le]
  nlinarith [div_mul_cancel₀ b (ne_of_gt hc)]

lemma eigenvalue_le_trace_of_posSemidef
    (K : Matrix V V ℝ)
    (hK : K.PosSemidef)
    (i : V) :
    hK.isHermitian.eigenvalues i ≤ K.trace := by
  classical
  have htr : K.trace = ∑ j, hK.isHermitian.eigenvalues j := by
    have h := hK.isHermitian.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at h; exact h
  rw [htr]
  exact Finset.single_le_sum (fun j _ => hK.eigenvalues_nonneg j) (Finset.mem_univ i)

end Problem6

end
