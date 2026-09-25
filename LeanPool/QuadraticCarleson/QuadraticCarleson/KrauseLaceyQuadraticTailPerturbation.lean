/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticAnnularTail

/-!
# Perturbations of finite quadratic annular tails

This file is deliberately independent of the concrete projection and
remainder constructions. It records the finite-dimensional fact that a
tail maximal function is stable under changing every piece, with the sum of
the pointwise errors as the loss.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson.KrauseLaceyQuadraticTailPerturbation

open KrauseLaceyQuadraticAnnularTail


noncomputable
section

/-- The scalar pointwise loss incurred by replacing `u` with `v` in the
first `N` pieces. -/
def finitePieceErrorMajorant
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ‖u n x - v n x‖ₑ

/-- The scalar error majorant is measurable when the two sequences are. -/
theorem measurable_finitePieceErrorMajorant
    {N : ℕ} {u v : ℕ → ℝ → ℂ}
    (hu : ∀ n, Measurable (u n)) (hv : ∀ n, Measurable (v n)) :
    Measurable (finitePieceErrorMajorant N u v) := by
  classical
  unfold finitePieceErrorMajorant
  exact Finset.measurable_sum _ fun n _ ↦ (hu n).sub (hv n) |>.enorm

private theorem enorm_sum_Ico_sub_le_errorMajorant
    (N n : ℕ) (u v : ℕ → ℝ → ℂ) (x : ℝ) :
    ‖∑ j ∈ Finset.Ico n N, (u j x - v j x)‖ₑ ≤
      finitePieceErrorMajorant N u v x := by
  calc
    ‖∑ j ∈ Finset.Ico n N, (u j x - v j x)‖ₑ ≤
        ∑ j ∈ Finset.Ico n N, ‖u j x - v j x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ‖u j x - v j x‖ₑ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
      intro j hj _
      exact bot_le
    _ = finitePieceErrorMajorant N u v x := rfl

/-- A single finite tail changes by at most the sum of all piecewise errors. -/
theorem enorm_finitePieceTail_le_finitePieceTail_add_errorMajorant
    (N n : ℕ) (u v : ℕ → ℝ → ℂ) (x : ℝ) (hn : n ≤ N) :
    ‖finitePieceTail N u n x‖ₑ ≤
      ‖finitePieceTail N v n x‖ₑ + finitePieceErrorMajorant N u v x := by
  have htail : finitePieceTail N u n x =
      finitePieceTail N v n x + ∑ j ∈ Finset.Ico n N, (u j x - v j x) := by
    rw [finitePieceTail_eq_sum_Ico hn u x,
      finitePieceTail_eq_sum_Ico hn v x, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    abel
  rw [htail]
  exact (enorm_add_le _ _).trans (add_le_add le_rfl
    (enorm_sum_Ico_sub_le_errorMajorant N n u v x))

/-- Pointwise stability of the finite tail maximal function under a change of
the individual pieces. -/
theorem finitePieceTailMax_le_finitePieceTailMax_add_errorMajorant
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (x : ℝ) :
    finitePieceTailMax N u x ≤
      finitePieceTailMax N v x + finitePieceErrorMajorant N u v x := by
  unfold finitePieceTailMax
  apply Finset.sup_le
  intro n hn
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact (enorm_finitePieceTail_le_finitePieceTail_add_errorMajorant
    N n u v x hnN).trans
    (add_le_add
      (Finset.le_sup (s := Finset.range (N + 1))
        (f := fun m ↦ ‖finitePieceTail N v m x‖ₑ) hn)
      le_rfl)

/-- The perturbation estimate in its expanded form. -/
theorem finitePieceTailMax_le_finitePieceTailMax_add_sum_enorm_sub
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (x : ℝ) :
    finitePieceTailMax N u x ≤ finitePieceTailMax N v x +
      ∑ n ∈ Finset.range N, ‖u n x - v n x‖ₑ := by
  simpa only [finitePieceErrorMajorant] using
    (finitePieceTailMax_le_finitePieceTailMax_add_errorMajorant N u v x)

/-- The version of the perturbation estimate supplied by an arbitrary scalar
error majorant. -/
theorem finitePieceTailMax_le_finitePieceTailMax_add_of_error_majorant
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (E : ℝ → ℝ≥0∞) (x : ℝ)
    (hE : finitePieceErrorMajorant N u v x ≤ E x) :
    finitePieceTailMax N u x ≤ finitePieceTailMax N v x + E x :=
  (finitePieceTailMax_le_finitePieceTailMax_add_errorMajorant N u v x).trans
    (add_le_add le_rfl hE)

private theorem ennreal_add_sq_le_four_sum_sq (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : a + b ≤ 2 * max a b := by
    calc
      a + b ≤ max a b + max a b :=
        add_le_add (le_max_left a b) (le_max_right a b)
      _ = 2 * max a b := by ring
  have hmax : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    by_cases h : a ≤ b
    · rw [max_eq_right h]
      exact le_add_left le_rfl
    · rw [max_eq_left (le_of_not_ge h)]
      exact le_add_right le_rfl
  calc
    (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' hab 2
    _ = 4 * (max a b) ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl hmax

/-- An `L²` transfer principle: an `L²` tail estimate for `v` and an `L²`
estimate for a measurable scalar error majorant give an `L²` estimate for
`u`. The deliberately harmless factor `4` avoids any finiteness side
conditions on extended nonnegative values. -/
theorem finitePieceTailMax_sq_lintegral_le_of_error_majorant
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (E : ℝ → ℝ≥0∞)
    (hEmeas : Measurable E)
    (hpoint : ∀ x, finitePieceErrorMajorant N u v x ≤ E x)
    (B C : ℝ≥0∞)
    (hprojected : (∫⁻ x, finitePieceTailMax N v x ^ 2) ≤ B)
    (herror : (∫⁻ x, E x ^ 2) ≤ C) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤ 4 * (B + C) := by
  have hbound (x : ℝ) :
      finitePieceTailMax N u x ^ 2 ≤
        4 * (finitePieceTailMax N v x ^ 2 + E x ^ 2) := by
    exact (pow_le_pow_left'
      (finitePieceTailMax_le_finitePieceTailMax_add_of_error_majorant
        N u v E x (hpoint x)) 2).trans
      (ennreal_add_sq_le_four_sum_sq _ _)
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (finitePieceTailMax N v x ^ 2 + E x ^ 2) :=
      lintegral_mono hbound
    _ = 4 * ((∫⁻ x, finitePieceTailMax N v x ^ 2) + ∫⁻ x, E x ^ 2) := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_right _ (hEmeas.pow_const 2)]
    _ ≤ 4 * (B + C) := by gcongr

/-- Almost-everywhere form of the `L²` tail transfer principle. This is the
natural interface when the individual pieces are represented by `L²`
functions and their projection/remainder decomposition holds only almost
everywhere. -/
theorem finitePieceTailMax_sq_lintegral_le_of_ae_bound
    (N : ℕ) (u v : ℕ → ℝ → ℂ) (E : ℝ → ℝ≥0∞)
    (hEmeas : AEMeasurable E volume)
    (hpoint : ∀ᵐ x, finitePieceTailMax N u x ≤
      finitePieceTailMax N v x + E x)
    (B C : ℝ≥0∞)
    (hprojected : (∫⁻ x, finitePieceTailMax N v x ^ 2) ≤ B)
    (herror : (∫⁻ x, E x ^ 2) ≤ C) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤ 4 * (B + C) := by
  have hbound : ∀ᵐ x, finitePieceTailMax N u x ^ 2 ≤
      4 * (finitePieceTailMax N v x ^ 2 + E x ^ 2) := by
    filter_upwards [hpoint] with x hx
    exact (pow_le_pow_left' hx 2).trans
      (ennreal_add_sq_le_four_sum_sq _ _)
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (finitePieceTailMax N v x ^ 2 + E x ^ 2) :=
      lintegral_mono_ae hbound
    _ = 4 * ((∫⁻ x, finitePieceTailMax N v x ^ 2) + ∫⁻ x, E x ^ 2) := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_right' _ (hEmeas.pow_const 2)]
    _ ≤ 4 * (B + C) := by gcongr

/-- The preceding transfer principle specialized to the explicit finite sum
of piecewise projection errors. -/
theorem finitePieceTailMax_sq_lintegral_le_of_piecewise_error
    (N : ℕ) (u v : ℕ → ℝ → ℂ)
    (hu : ∀ n, Measurable (u n)) (hvpieces : ∀ n, Measurable (v n))
    (B C : ℝ≥0∞)
    (hprojected : (∫⁻ x, finitePieceTailMax N v x ^ 2) ≤ B)
    (herror : (∫⁻ x, finitePieceErrorMajorant N u v x ^ 2) ≤ C) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤ 4 * (B + C) := by
  apply finitePieceTailMax_sq_lintegral_le_of_error_majorant
    N u v (finitePieceErrorMajorant N u v)
    (measurable_finitePieceErrorMajorant hu hvpieces)
    (fun _ ↦ le_rfl) B C hprojected herror


end
end QuadraticCarleson.KrauseLaceyQuadraticTailPerturbation
