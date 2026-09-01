/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Generic quadratic-form and spectral lemmas

This file contains a number of useful results concerning spectral bounds of matrices and their
inverses, followed by several results specialised to symmetric idempotent matrices.

 -/

namespace LeanPool.LinearModel

noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

section Definitions

/-- The squared norm `‖v‖² = v ⬝ᵥ v` (note that the standard norm notation reverts
to the sup norm for `v : Fin n → ℝ`). -/
abbrev normSq (v : Fin n → ℝ) : ℝ := v ⬝ᵥ v

/-- The (pseudo)-inner product `⟨u,v⟩_A = uᵀAv` (renaming of `Matrix.toBilin'`) -/
abbrev inner' (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) := toBilin' A u v

/-- The squared (pseudo)-norm `‖v‖²_A = ⟨v,v⟩_A`. -/
abbrev normSq' (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) := toBilin' A v v

/-- `c` is a spectral lower bound for `A`. -/
abbrev isSpectralLb (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) := ∀ w, c * normSq w ≤ normSq' A w

/-- `C` is a spectral upper bound for `A`. -/
abbrev isSpectralUb (A : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) := ∀ w, normSq' A w ≤ C * normSq w

/-- `A` is positive semi-definite -/
abbrev IsPsd (A : Matrix (Fin n) (Fin n) ℝ) := ∀ w, 0 ≤ normSq' A w

end Definitions

section Spectral

/-- `normSq` is non-negative. -/
lemma normSq_nonneg (v : Fin n → ℝ) : 0 ≤ normSq v := by
  simp only [normSq, dotProduct]
  exact Finset.sum_nonneg fun v i => mul_self_nonneg _

/-- `‖v‖² = ∑ₖ vₖ²`. -/
lemma normSq_eq_sum_sq (v : Fin n → ℝ) : normSq v = ∑ k, v k ^ 2 := by
  simp only [normSq, dotProduct, pow_two]

/-- `‖v‖²_A = ⟨v,v⟩_A`. -/
lemma normSq'_eq_inner'_self (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    normSq' A v = inner' A v v := by
  simp

/-- `‖Av‖² = ‖v‖^2_{AᵀA}` -/
lemma mulVec_normSq_eq (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    normSq (A *ᵥ v) = normSq' (Aᵀ * A) v := by
  simp only [normSq, toBilin'_apply']
  rw [dotProduct_mulVec,  ← mulVec_transpose, mulVec_mulVec, dotProduct_comm]

/-- For symmetric `A`, `inner'` is symmetric. -/
lemma inner'_symm (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (u v : Fin n → ℝ) : inner' A v u = inner' A u v := by
  simp only [toBilin'_apply']; rw [dotProduct_mulVec, ← mulVec_transpose, hA_sym, dotProduct_comm]

/-- For symmetric `A`, `‖v‖²_{ABA} = ‖Av‖^2_B`. -/
lemma normSq'_conj (A B : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A) (v : Fin n → ℝ) :
    normSq' (A * B * A) v = normSq' B (A *ᵥ v) := by
  nth_rewrite 1 [← hA_sym]; simp only [normSq']; rw [← toBilin'_comp]; simp [toLin'_apply]

/-- For invertible `A`, `‖v‖²_{A⁻¹} = ‖A⁻¹ v‖²_A`. -/
lemma normSq'_inv (A : Matrix (Fin n) (Fin n) ℝ) (hA_inv : IsUnit A.det)
    (v : Fin n → ℝ) :
    normSq' A⁻¹ v = normSq' A (A⁻¹ *ᵥ v) := by
  simp only [toBilin'_apply']
  rw [mulVec_mulVec, mul_nonsing_inv _ hA_inv, one_mulVec, dotProduct_comm]

/-- Cauchy–Schwarz for a PSD matrix `A` `⟨u,v⟩²_A ≤ ‖u‖²_A ‖v‖²_A`. -/
lemma psd_cauchy_schwarz (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_psd : IsPsd A) (u v : Fin n → ℝ) :
    (inner' A u v) ^ 2 ≤ (normSq' A u) * (normSq' A v) := by
  have hquad : ∀ t : ℝ, 0 ≤
      (normSq' A v) * (t * t) + 2 * (inner' A u v) * t + (normSq' A u) := by
    intro t
    have h := hA_psd (u + t • v)
    have hexp : normSq' A (u + t • v)
        = (normSq' A v) * (t * t) + 2 * (inner' A u v) * t + (normSq' A u) := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [two_mul]; nth_rewrite 1 [← inner'_symm A hA_sym u v]; ring
    rwa [hexp] at h
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- A non-negative spectral lower bound implies PSD. -/
lemma is_psd_of_nonneg_spectral_lb (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA_lb : isSpectralLb A c) : IsPsd A :=
  fun w => le_trans (mul_nonneg hc (normSq_nonneg w)) (hA_lb w)

/-- The inverse of an invertible PSD matrix is PSD. -/
lemma is_psd_inv (A : Matrix (Fin n) (Fin n) ℝ) (hA_psd : IsPsd A) (hA_inv : IsUnit A.det) :
    IsPsd A⁻¹ := by
  intro w
  rw [normSq'_inv A hA_inv w]; exact hA_psd _

/-- `‖Av‖² ≤ C·‖v‖²_A` for symmetric PSD `A` with spectral upper bound `C ≥ 0`. -/
lemma mulVec_normSq_le_spectral_ub_normSq' (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_psd : IsPsd A) (C : ℝ) (hC : 0 ≤ C)
    (hA_ub : isSpectralUb A C) :
    ∀ v, normSq (A *ᵥ v) ≤ C * normSq' A v := by
  intro v
  set s := normSq (A *ᵥ v) with hs
  have hs_nn : 0 ≤ s := normSq_nonneg _
  have hcs := psd_cauchy_schwarz A hA_sym hA_psd v (A *ᵥ v)
  have hs_inner' : inner' A v (A *ᵥ v) = s := by
    rw [hs]; simpa only [toBilin'_apply'] using (inner'_symm A hA_sym v (A *ᵥ v)).symm
  have hCs_normSq' : normSq' A (A *ᵥ v) ≤ C * s := hA_ub _
  rw [hs_inner'] at hcs
  have hchain : s ^ 2 ≤ normSq' A v * (C * s) :=
    hcs.trans (mul_le_mul_of_nonneg_left hCs_normSq' (hA_psd v))
  rcases eq_or_lt_of_le hs_nn with h0 | hpos
  · rw [← h0]; exact mul_nonneg hC (hA_psd v)
  · have hmul : s * s ≤ (C * normSq' A v) * s := by nlinarith [hchain]
    exact le_of_mul_le_mul_right hmul hpos

/-- `‖Av‖² ≤ C²·‖v‖²` for symmetric PSD `A` with spectral upper bound `C ≥ 0`. -/
lemma mulVec_normSq_le_spectral_ub_sq_normSq (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_psd : IsPsd A) (C : ℝ) (hC : 0 ≤ C)
    (hA_ub : isSpectralUb A C) :
    ∀ v, normSq (A *ᵥ v) ≤ C ^ 2 * normSq v := by
    intro v
    calc normSq (A *ᵥ v)
      ≤ C * normSq' A v := mulVec_normSq_le_spectral_ub_normSq' A hA_sym hA_psd C hC hA_ub v
    _ ≤ C * (C * normSq v) := mul_le_mul_of_nonneg_left (hA_ub v) hC
    _ = C ^ 2 * normSq v := by ring

/-- `c·‖v‖²_A ≤ ‖Av‖²` for symmetric PSD `A` with spectral lower bound `c ≥ 0`. -/
lemma spectral_lb_normSq'_le_mulVec_normSq (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA_lb : isSpectralLb A c) :
    ∀ v, c * normSq' A v ≤ normSq (A *ᵥ v) := by
  intro v
  set s := normSq' A v with hs
  have hs_nn : 0 ≤ s := le_trans (mul_nonneg hc (normSq_nonneg v)) (hA_lb v)
  have hcs : s ^ 2 ≤ normSq v * normSq (A *ᵥ v) := by
    simp only [normSq, hs, dotProduct, normSq', toBilin'_apply']
    simpa only [← pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (A *ᵥ v)
  rcases (normSq_nonneg v).lt_or_eq with hv_pos | hv0
  · have hmul : (c * s) * normSq v ≤ normSq (A *ᵥ v) * normSq v := by
      nlinarith [mul_le_mul_of_nonneg_left (hA_lb v) hs_nn, hcs]
    exact le_of_mul_le_mul_right hmul hv_pos
  · have hs0 : s = 0 := by
      rw [hs, dotProduct_self_eq_zero.mp hv0.symm]; simp
    rw [hs0, mul_zero]
    exact normSq_nonneg _

/-- If `c` and `C` are spectral lower and upper bounds for symmetric invertible PSD `A` then
`c·‖v‖² ≤ C²‖v‖²_{A⁻¹}` for all `v`. -/
theorem spectral_lb_normSq_le_spectral_ub_sq_inv_normSq (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_inv : IsUnit A.det) (hA_sym : Aᵀ = A) (hA_psd : IsPsd A)
    (c C : ℝ) (hc_pos : 0 < c) (hC_pos : 0 < C)
    (hA_lb : isSpectralLb A c) (hA_ub : isSpectralUb A C) :
    ∀ v, c * normSq v ≤ C ^ 2 * normSq' A⁻¹ v := by
  intro v
  set u := A⁻¹ *ᵥ v with hu
  have hv_eq : A *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA_inv, Matrix.one_mulVec]
  have h_invQuad : normSq' A⁻¹ v = normSq' A u := by
    rw [normSq'_inv A hA_inv v, ← hu]
  have h_up : normSq v ≤ C ^ 2 * normSq u := by
    have h := mulVec_normSq_le_spectral_ub_sq_normSq A hA_sym hA_psd C hC_pos.le hA_ub u
    rwa [hv_eq] at h
  calc c * normSq v
      ≤ c * (C ^ 2 * normSq u) := mul_le_mul_of_nonneg_left h_up hc_pos.le
    _ = C ^ 2 * (c * normSq u) := by ring
    _ ≤ C ^ 2 * normSq' A u := mul_le_mul_of_nonneg_left (hA_lb u) (sq_nonneg C)
    _ = C ^ 2 * normSq' A⁻¹ v := by rw [h_invQuad]


/-- If `A` is invertible symmetric PSD with spectral upper bound `C > 0`
then `A⁻¹` has spectral lower bound `1/C`. -/
lemma inv_spectral_lb (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_inv : IsUnit A.det) (hA_psd : IsPsd A) (C : ℝ)
    (hC : 0 < C) (hA_ub : isSpectralUb A C) :
    isSpectralLb A⁻¹ (1/C) := by
  unfold isSpectralLb
  intro v
  have h_cancel : A *ᵥ A⁻¹ *ᵥ v = v := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hA_inv, Matrix.one_mulVec]
  have key := mulVec_normSq_le_spectral_ub_normSq' A hA_sym hA_psd C hC.le hA_ub (A⁻¹ *ᵥ v)
  have hA_inv_symm : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hA_sym]
  rw [h_cancel, ← normSq'_conj A⁻¹ A hA_inv_symm, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hA_inv, Matrix.mul_one] at key
  have h := mul_le_mul_of_nonneg_left key (one_div_pos.mpr hC).le
  rwa [← mul_assoc, one_div_mul_cancel hC.ne', one_mul] at h

/-- If `A` has positive spectral lower bound `c > 0` then `A` is invertible. -/
lemma inv_of_pos_spectral_lb (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hA_lb : isSpectralLb A c) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨v, hv_ne, hv0⟩ := hdet
  have h1 : normSq' A v = 0 := by rw [normSq', toBilin'_apply', hv0, dotProduct_zero]
  have h2 : c * normSq v ≤ 0 := by rw [← h1]; exact hA_lb v
  have h3 : 0 < normSq v := by
    rcases (normSq_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv_ne
  nlinarith [mul_pos hc h3]

/-- If `A` has positive spectral lower bound `c > 0` then `A⁻¹` has spectral
upper bound `1/c`. -/
lemma inv_spectral_ub (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hA_lb : isSpectralLb A c) :
    isSpectralUb A⁻¹ (1/c) := by
  unfold isSpectralUb
  intro v
  have hA_inv : IsUnit A.det := inv_of_pos_spectral_lb A c hc hA_lb
  have h_cancel : A *ᵥ A⁻¹ *ᵥ v = v := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hA_inv, Matrix.one_mulVec]
  have h_eq : normSq' A⁻¹ v = normSq' A (A⁻¹ *ᵥ v) := normSq'_inv A hA_inv v
  have key := spectral_lb_normSq'_le_mulVec_normSq A c hc.le hA_lb (A⁻¹ *ᵥ v)
  rw [h_cancel, ← h_eq] at key
  have h := mul_le_mul_of_nonneg_left key (one_div_pos.mpr hc).le
  rwa [← mul_assoc, one_div_mul_cancel hc.ne', one_mul] at h

/-- If `A` is symmetric PSD with spectral upper bound `C`, then `|A i j| ≤ C` for
all `i, j`. -/
lemma entry_ub_of_spectral_ub (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_psd : IsPsd A) (C : ℝ)
    (hA_ub : isSpectralUb A C) :
    ∀ i j : Fin n, |A i j| ≤ C := by
  intro i j
  have hbasis: ∀ k l : Fin n, inner' A (Pi.single k 1) (Pi.single l 1) = A k l := by
    intro k l; simp
  have hA_diag_nn : ∀ t, 0 ≤ A t t := by
    intro t; have := hA_psd (Pi.single t 1); rwa [normSq'_eq_inner'_self, hbasis] at this
  by_cases hij : i = j
  · subst hij
    rw [abs_le]
    have := hA_ub (Pi.single i 1); rw [normSq'_eq_inner'_self, hbasis] at this; simp at this
    constructor <;> linarith [hA_diag_nn i]
  · set ei : Fin n → ℝ := Pi.single i 1 with hei
    set ej : Fin n → ℝ := Pi.single j 1 with hej
    have hplus : normSq (ei + ej) = 2 := by rw [hei, hej]; norm_num [Pi.single_apply, hij]
    have hminus : normSq (ei - ej) = 2 := by rw [hei, hej]; norm_num [Pi.single_apply, hij]
    have hplus' : normSq' A (ei + ej) = A i i + 2 * A i j + A j j := by
      simp only [map_add, LinearMap.add_apply, hei, hej, hbasis]
      rw [← transpose_apply A i j, hA_sym]
      ring
    have hminus' : normSq' A (ei - ej) = A i i - 2 * A i j + A j j := by
      simp only [map_sub, LinearMap.sub_apply, hei, hej, hbasis]
      rw [← transpose_apply A i j, hA_sym]
      ring
    have h1 := hA_ub (ei + ej)
    have h2 := hA_ub (ei - ej)
    rw [hplus', hplus] at h1
    rw [hminus', hminus] at h2
    rw [abs_le]
    constructor <;> linarith [hA_diag_nn i, hA_diag_nn j]

/-- If `A` is symmetric with spectral lower bound `c > 0` then `|A⁻¹ i j| ≤ 1/c` for
all `i, j`. -/
lemma inv_entry_ub_of_spectral_lb (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (hA_sym : Aᵀ = A)
    (hA_lb : isSpectralLb A c) :
    ∀ i j, |A⁻¹ i j| ≤ 1 / c := by
  have hA_inv : IsUnit A.det := inv_of_pos_spectral_lb A c hc hA_lb
  have hA_psd : IsPsd A := is_psd_of_nonneg_spectral_lb A c hc.le hA_lb
  have hA_inv_sym : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hA_sym]
  have hA_inv_spectral_ub := inv_spectral_ub A c hc hA_lb
  have hA_inv_psd : IsPsd A⁻¹ := is_psd_inv A hA_psd hA_inv
  exact entry_ub_of_spectral_ub A⁻¹ hA_inv_sym hA_inv_psd (1/c) hA_inv_spectral_ub

end Spectral


section Projections

/-- For symmetric idempotent `A`, `‖Av‖² = ‖v‖²_A`. -/
lemma proj_mulVec_normSq_eq (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) :
    ∀ v, normSq (A *ᵥ v) = normSq' A v := by
  intro v
  simp only [toBilin'_apply', normSq]
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA_sym, hA_idem,
    dotProduct_comm]

/-- Any symmetric idempotent `A` is PSD -/
lemma proj_is_psd (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) :
    IsPsd A := by
  unfold IsPsd
  intro v
  exact le_trans (normSq_nonneg (A *ᵥ v)) (proj_mulVec_normSq_eq A hA_sym hA_idem v).le

/-- For symmetric idempotent `A`, `‖Av‖² ≤ ‖v‖^2`. -/
lemma proj_mulVec_normSq_le (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) :
    ∀ v, normSq (A *ᵥ v) ≤ normSq v := by
  intro v
  have hc_sym : (1 - A)ᵀ = 1 - A := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hA_sym]
  have hc_idem : (1 - A) * (1 - A) = 1 - A := by
    simp [Matrix.sub_mul, Matrix.mul_sub, hA_idem]
  have hnn : 0 ≤ normSq' (1 - A) v := by
    rw [← proj_mulVec_normSq_eq (1 - A) hc_sym hc_idem v]
    exact normSq_nonneg _
  have hsplit : normSq' (1 - A) v = normSq v - normSq' A v := by
    simp only [Matrix.toBilin'_apply', Matrix.sub_mulVec, dotProduct_sub,
      Matrix.one_mulVec, normSq]
  have hA := proj_mulVec_normSq_eq A hA_sym hA_idem v
  linarith

/-- For symmetric idempotent `A`, `Aᵢᵢ = ‖Aᵢ‖²`. -/
lemma proj_diag_eq_row_normSq (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) (i : Fin n) :
    A i i = normSq (A i) := by
  calc A i i = (A * A) i i := by rw [hA_idem]
    _ = normSq (A i) := by
      nth_rewrite 2 [← hA_sym]
      simp [Matrix.mul_apply, normSq, dotProduct]

/-- For symmetric idempotent `A`, `0 ≤ Aᵢᵢ`. -/
lemma proj_diag_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) (i : Fin n) :
    0 ≤ A i i := by
  rw [proj_diag_eq_row_normSq A hA_sym hA_idem i]
  exact normSq_nonneg _

/-- For symmetric idempotent `A`, `Aᵢᵢ ≤ 1`. -/
lemma proj_diag_le_one (A : Matrix (Fin n) (Fin n) ℝ) (hA_sym : Aᵀ = A)
    (hA_idem : A * A = A) (i : Fin n) :
    A i i ≤ 1 := by
  have hsq : (A i i) ^ 2 ≤ A i i := by
    rw [pow_two]
    calc A i i * A i i
        ≤ ∑ k, A i k * A i k :=
          Finset.single_le_sum (f := fun k => A i k * A i k)
            (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
      _ = normSq (A i) := by simp [normSq, dotProduct]
      _ = A i i := (proj_diag_eq_row_normSq A hA_sym hA_idem i).symm
  nlinarith


end Projections

end
end LinearModel
end LeanPool
