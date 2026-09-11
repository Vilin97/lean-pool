/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.TN.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Convex vanishing at zero and total nonnegativity

Lemma `lem:convex` of `docs/sol.tex`: if `f : [0, ∞) → [0, ∞)` is convex and
`f 0 = 0`, then for `0 < t₁ ≤ ⋯ ≤ tₖ` the matrix with rows `(1, tᵢ, f tᵢ)` is
totally nonnegative.
-/

open Function Matrix Set

namespace BollobasNikiforov

variable {f : ℝ → ℝ}

/-! ### TN14: monotonicity of `f` and of `f t / t` -/

/-- Convexity on `[0, ∞)` together with `f 0 = 0` makes `t ↦ f t / t`
nondecreasing on `(0, ∞)`. -/
lemma convexOn_Ici_zero_div_monotoneOn
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) (hf0 : f 0 = 0) :
    MonotoneOn (fun t ↦ f t / t) (Ioi 0) := by
  intro t ht u hu htu
  rcases htu.eq_or_lt with rfl | htu
  · rfl
  · have hs := hf.slope_mono_adjacent (x := (0 : ℝ)) (y := t) (z := u)
      (mem_Ici.mpr le_rfl) (Ioi_subset_Ici_self hu) ht htu
    have ht0 : 0 < t := ht
    have hdiff : 0 < u - t := sub_pos.mpr htu
    simp only [hf0, sub_zero] at hs
    rw [div_le_div_iff₀ ht0 hdiff] at hs
    rw [div_le_div_iff₀ ht0 (ht0.trans htu)]
    linarith

/-- A nonnegative convex function on `[0, ∞)` with `f 0 = 0` is nondecreasing
there. -/
lemma convexOn_Ici_zero_monotoneOn
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) (hf0 : f 0 = 0)
    (hfnn : ∀ x, 0 ≤ x → 0 ≤ f x) :
    MonotoneOn f (Ici 0) := by
  intro t ht u hu htu
  rcases htu.eq_or_lt with rfl | htu
  · rfl
  · rcases eq_or_lt_of_le (mem_Ici.mp ht) with ht0 | ht0
    · simpa [← ht0, hf0] using hfnn u (mem_Ici.mp hu)
    · have hu0 : 0 < u := ht0.trans htu
      have hdiv := convexOn_Ici_zero_div_monotoneOn hf hf0 ht0 hu0 htu.le
      have := (div_le_div_iff₀ ht0 hu0).mp hdiv
      have : f t * u ≤ f u * u :=
        this.trans (mul_le_mul_of_nonneg_left htu.le (hfnn u (mem_Ici.mp hu)))
      exact le_of_mul_le_mul_right this hu0

/-! ### TN15: size-one and size-two minors of rows `(1, t, f t)` -/

/-- The feature row `(1, t, f t)`. -/
def row3 (f : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ := ![1, t, f t]

@[simp] lemma row3_zero (f : ℝ → ℝ) (t : ℝ) : row3 f t 0 = 1 := rfl
@[simp] lemma row3_one (f : ℝ → ℝ) (t : ℝ) : row3 f t 1 = t := rfl
@[simp] lemma row3_two (f : ℝ → ℝ) (t : ℝ) : row3 f t 2 = f t := by
  simp [row3, cons_val_two, vecHead, vecTail]

/-- The `ι × 3` matrix whose `i`th row is `(1, t i, f (t i))`. -/
def convexRowMatrix {ι : Type*} (f : ℝ → ℝ) (t : ι → ℝ) : Matrix ι (Fin 3) ℝ :=
  fun i j ↦ row3 f (t i) j

lemma row3_nonneg (hfnn : ∀ x, 0 ≤ x → 0 ≤ f x) {t : ℝ} (ht : 0 < t) (j : Fin 3) :
    0 ≤ row3 f t j := by
  fin_cases j
  · simp
  · exact ht.le
  · exact hfnn t ht.le

/-- Every `1 × 1` and `2 × 2` minor of two increasing rows `(1, t, f t)`,
`(1, u, f u)` is nonnegative. -/
lemma row3_one_two_minors_nonneg
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) (hf0 : f 0 = 0)
    (hfnn : ∀ x, 0 ≤ x → 0 ≤ f x) {t u : ℝ}
    (ht : 0 < t) (htu : t ≤ u) :
    (∀ j : Fin 3, 0 ≤ row3 f t j) ∧
      0 ≤ u - t ∧ 0 ≤ f u - f t ∧ 0 ≤ t * f u - u * f t := by
  refine ⟨row3_nonneg hfnn ht, sub_nonneg.mpr htu, ?_, ?_⟩
  · have := convexOn_Ici_zero_monotoneOn hf hf0 hfnn (mem_Ici.mpr ht.le)
      (mem_Ici.mpr (ht.le.trans htu)) htu
    exact sub_nonneg.mpr this
  · have hu : 0 < u := ht.trans_le htu
    have hdiv := convexOn_Ici_zero_div_monotoneOn hf hf0 ht hu htu
    linarith [(div_le_div_iff₀ ht hu).mp hdiv]

/-! ### TN16: the `3 × 3` minor -/

/-- Three-slope comparison: for `0 < t < u < v` the displayed `3 × 3` minor
expression is nonnegative. -/
lemma convex_three_slope
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) {t u v : ℝ}
    (ht : 0 < t) (htu : t < u) (huv : u < v) :
    0 ≤ (u - t) * (f v - f t) - (v - t) * (f u - f t) := by
  have hs := hf.slope_mono_adjacent (x := t) (y := u) (z := v)
    (mem_Ici.mpr ht.le) (mem_Ici.mpr (ht.trans htu |>.trans huv).le) htu huv
  have h1 : 0 < u - t := sub_pos.mpr htu
  have h2 : 0 < v - u := sub_pos.mpr huv
  rw [div_le_div_iff₀ h1 h2] at hs
  linarith

/-- Three rows `(1, t, f t)`, `(1, u, f u)`, `(1, v, f v)`. -/
def row3Triple (t u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  of ![row3 f t, row3 f u, row3 f v]

/-- Two rows `(1, t, f t)`, `(1, u, f u)` on a pair of columns `J`. -/
def row3Pair (t u : ℝ) (J : Fin 2 → Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  of ![row3 f t ∘ J, row3 f u ∘ J]

lemma det_row3Triple (t u v : ℝ) :
    (row3Triple (f := f) t u v).det =
      (u - t) * (f v - f t) - (v - t) * (f u - f t) := by
  rw [det_fin_three]
  simp [row3Triple, of_apply, row3_zero, row3_one, row3_two, cons_val_zero,
    cons_val_one, cons_val_two, vecHead, vecTail]
  ring

/-! ### TN17: `lem:convex` -/

lemma det_convexRowMatrix_two
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) (hf0 : f 0 = 0)
    (hfnn : ∀ x, 0 ≤ x → 0 ≤ f x)
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) {J : Fin 2 → Fin 3}
    (hJ : StrictMono J) :
    0 ≤ (row3Pair (f := f) t u J).det := by
  obtain ⟨s, hs⟩ := exists_eq_succAbove_of_strictMono hJ
  subst hs
  have hminors := row3_one_two_minors_nonneg hf hf0 hfnn ht htu
  fin_cases s
  · rw [det_fin_two]
    simp [row3Pair, of_apply, row3_one, row3_two]
    linarith [hminors.2.2.2]
  · have h0 : Fin.succAbove (1 : Fin 3) (0 : Fin 2) = 0 := by decide
    have h1 : Fin.succAbove (1 : Fin 3) (1 : Fin 2) = 2 := by decide
    rw [det_fin_two]
    simp [row3Pair, of_apply, h0, h1, row3_zero, row3_two]
    linarith [hminors.2.2.1]
  · have h0 : Fin.succAbove (2 : Fin 3) (0 : Fin 2) = 0 := by decide
    have h1 : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := by decide
    rw [det_fin_two]
    simp [row3Pair, of_apply, h0, h1, row3_zero, row3_one]
    linarith [hminors.2.1]

lemma det_convexRowMatrix_three
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) {t u v : ℝ}
    (ht : 0 < t) (htu : t ≤ u) (huv : u ≤ v) :
    0 ≤ (row3Triple (f := f) t u v).det := by
  rw [det_row3Triple]
  rcases htu.eq_or_lt with rfl | htu
  · ring_nf; simp
  · rcases huv.eq_or_lt with rfl | huv
    · ring_nf; simp
    · exact convex_three_slope hf ht htu huv

/-- Lemma `lem:convex`: rows `(1, tᵢ, f tᵢ)` of a nonnegative convex `f`
vanishing at `0` form a totally nonnegative matrix, for `0 < t₁ ≤ ⋯ ≤ tₖ`. -/
lemma isTotallyNonneg_convexRowMatrix
    (hf : ConvexOn ℝ (Ici (0 : ℝ)) f) (hf0 : f 0 = 0)
    (hfnn : ∀ x, 0 ≤ x → 0 ≤ f x) {k : ℕ} {t : Fin k → ℝ}
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i) :
    IsTotallyNonneg (convexRowMatrix f t) := by
  intro r I J hI hJ
  match r with
  | 0 =>
    rw [det_fin_zero]
    exact zero_le_one
  | 1 =>
    rw [det_fin_one]
    simpa [convexRowMatrix, submatrix_apply] using row3_nonneg hfnn (htpos (I 0)) (J 0)
  | 2 =>
    have hI01 : I 0 < I 1 := hI (by decide : (0 : Fin 2) < 1)
    have htu : t (I 0) ≤ t (I 1) := htmono hI01.le
    have hmat : (convexRowMatrix f t).submatrix I J =
        row3Pair (f := f) (t (I 0)) (t (I 1)) J := by
      ext i j
      fin_cases i <;> simp [convexRowMatrix, row3Pair, submatrix_apply]
    rw [hmat]
    exact det_convexRowMatrix_two hf hf0 hfnn (htpos (I 0)) htu hJ
  | 3 =>
    have hJid : J = id := strictMono_eq_id hJ
    have h01 : I 0 < I 1 := hI (by decide : (0 : Fin 3) < 1)
    have h12 : I 1 < I 2 := hI (by decide : (1 : Fin 3) < 2)
    have htu : t (I 0) ≤ t (I 1) := htmono h01.le
    have huv : t (I 1) ≤ t (I 2) := htmono h12.le
    have hmat :
        (convexRowMatrix f t).submatrix I J =
          row3Triple (f := f) (t (I 0)) (t (I 1)) (t (I 2)) := by
      subst hJid
      ext i j
      fin_cases i <;> simp [convexRowMatrix, row3Triple, submatrix_apply]
    rw [hmat]
    exact det_convexRowMatrix_three hf (htpos (I 0)) htu huv
  | r + 4 =>
    exact (isEmpty_strictMonoFin3_of_three_lt (by omega)).elim ⟨J, hJ⟩

end BollobasNikiforov
