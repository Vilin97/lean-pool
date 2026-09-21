/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SpectralCauchy
import LeanPool.OperatorTheory.Operator.Crouzeix.SpectralAuxiliary
import LeanPool.OperatorTheory.Operator.Crouzeix.AffineAuxiliary
import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm

/-!
# The disk auxiliary operator at an arbitrary center under spectral enclosure (L4.2 support)

`SpectralAuxiliary.lean` identifies the conjugate-polynomial auxiliary operator of the centered disk
`ball 0 r` with `star (p.eval 0) • 1` whenever `σ(A) ⊆ ball 0 r`.  Translating by
`AffineAuxiliary.lean` (`G(A, ball c r, p) = G(A - c•1, ball 0 r, p(z + c))`) and the spectrum
shift `σ(A - c•1) = σ(A) - {c}`, the same holds at any center: `G = star (p.eval c) • 1` whenever
`σ(A) ⊆ ball c r`.  Combined with the symmetrized bound of `SpectralCauchy.lean`, this gives the
classical-looking estimate `‖p(A) + p(c) • 1‖ ≤ 2 * sup_{|z - c| ≤ r} ‖p(z)‖` whenever the closure
of the numerical range lies in the open disk `ball c r`.

## Main declarations

* `spectrum_sub_smul_one_subset_ball_of_subset_ball` — the spectrum shift.
* `auxiliary_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball`
* `norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball`
* `norm_aeval_le_three_mul_polynomialSupNorm_of_numericalRange_subset_ball`,
  `isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball` — an open disk
  containing `closure (numericalRange A)` yields a `3`-polynomial-spectral set (from the
  symmetrized bound and `|p(c)| ≤ sup`; the sharp constant needs the product estimate).
* `isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall` — the
  same for a closed disk `closure (numericalRange A) ⊆ closedBall c r`, by passing to the limit
  through the open disks `ball c (r + 1/(n+1))` (`ApproximationSupNorm.lean`).
-/

open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Translating the spectrum: if `σ(A) ⊆ ball c r` then `σ(A - c • 1) ⊆ ball 0 r`. -/
theorem spectrum_sub_smul_one_subset_ball_of_subset_ball (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆ Metric.ball (0 : ℂ) r := by
  have hshift : spectrum ℂ (A - c • (1 : E →L[ℂ] E)) = spectrum ℂ A - ({c} : Set ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
  rw [hshift]
  rintro w ⟨z, hz, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
  exact hσ hz

/-- The disk auxiliary operator with center `c` under spectral enclosure equals
`star (p.eval c) • 1`. -/
theorem auxiliary_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c r hr) p =
      star (p.eval c) • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center A c hr p,
    crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
      (A - c • (1 : E →L[ℂ] E)) hr (spectrum_sub_smul_one_subset_ball_of_subset_ball A hσ),
    eval_affineComposition, one_mul, zero_add]

/-- **Classical symmetrized bound for a disk containing the numerical range**: if
`closure W(A) ⊆ ball c r`, then `‖p(A) + p(c) • 1‖ ≤ 2 * sup_{|z - c| ≤ r} ‖p(z)‖`. -/
theorem norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p + (p.eval c) • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall c r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball c r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have h := norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball_center
    A hr hW p
  rw [auxiliary_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
    A c hr hσ p, star_smul, star_one, star_star] at h
  exact h

/-! ### A `3`-polynomial-spectral set from the symmetrized bound alone -/

/-- If `closure W(A) ⊆ ball c r`, then `‖p(A)‖ ≤ 3 * sup_{|z - c| ≤ r} ‖p(z)‖`. -/
theorem norm_aeval_le_three_mul_polynomialSupNorm_of_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by
  have hsym := norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
    A hr hW p
  have hc : ‖p.eval c‖ ≤ polynomialSupNorm p (Metric.closedBall c r) :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c r))
      (Metric.mem_closedBall_self hr.le)
  have hconst : ‖(p.eval c) • (1 : E →L[ℂ] E)‖ ≤ ‖p.eval c‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  calc ‖aeval A p‖ = ‖(aeval A p + (p.eval c) • (1 : E →L[ℂ] E)) - (p.eval c) • (1 : E →L[ℂ] E)‖
    := by
        rw [add_sub_cancel_right]
    _ ≤ ‖aeval A p + (p.eval c) • (1 : E →L[ℂ] E)‖ + ‖(p.eval c) • (1 : E →L[ℂ] E)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * polynomialSupNorm p (Metric.closedBall c r) +
          polynomialSupNorm p (Metric.closedBall c r) := add_le_add hsym (hconst.trans hc)
    _ = 3 * polynomialSupNorm p (Metric.closedBall c r) := by ring

/-- **Disks containing the numerical range are 3-polynomial-spectral sets**: if
`closure W(A) ⊆ ball c r`, then `closedBall c r` is a `3`-polynomial-spectral set for `A`. -/
theorem isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) :=
  ⟨((spectrum_subset_closure_numericalRange A).trans hW).trans Metric.ball_subset_closedBall,
    fun p => norm_aeval_le_three_mul_polynomialSupNorm_of_numericalRange_subset_ball
      A hr hW p⟩

/-! ### Closed disks, by passing to the limit -/

omit [CompleteSpace E] in
/-- The closed disks `closedBall c (r + 1 / (n + 1))` intersect to `closedBall c r`. -/
theorem iInter_closedBall_add_inv_succ (c : ℂ) (r : ℝ) :
    (⋂ n : ℕ, Metric.closedBall c (r + 1 / ((n : ℝ) + 1))) = Metric.closedBall c r := by
  ext z
  simp only [Set.mem_iInter, Metric.mem_closedBall]
  constructor
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (h n).trans_lt (by linarith)
  · intro h n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- If `closure W(A) ⊆ closedBall c r` with `0 ≤ r`, then `‖p(A)‖ ≤ 3 * sup_{|z - c| ≤ r}
  ‖p(z)‖`. -/
theorem norm_aeval_le_three_mul_polynomialNorm_of_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by
  let K : ℕ → Set ℂ := fun n => Metric.closedBall c (r + 1 / ((n : ℝ) + 1))
  have hanti : Antitone K := by
    intro m n hmn
    apply Metric.closedBall_subset_closedBall
    have h1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    have h2 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have := one_div_le_one_div_of_le h2 h1
    linarith
  have hcompact : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall _ _
  have hnonempty : ∀ n, (K n).Nonempty := fun n =>
    ⟨c, Metric.mem_closedBall_self (by positivity)⟩
  have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact p K hanti hcompact hnonempty
  rw [show (⋂ n, K n) = Metric.closedBall c r from iInter_closedBall_add_inv_succ c r] at hlim
  have hbound : ∀ n, ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (K n) := by
    intro n
    have hpos : (0 : ℝ) < r + 1 / ((n : ℝ) + 1) := by positivity
    refine norm_aeval_le_three_mul_polynomialSupNorm_of_numericalRange_subset_ball
      A hpos (hW.trans ?_) p
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.const_mul 3) hbound

/-- **Closed disks containing the numerical range are 3-polynomial-spectral sets.** -/
theorem isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) :=
  ⟨(spectrum_subset_closure_numericalRange A).trans hW,
    fun p => norm_aeval_le_three_mul_polynomialNorm_of_numericalRange_subset_closedBall
      A hr hW p⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
