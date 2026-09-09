/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
public import LeanPool.NavierStokesAndEuler.Euler.NonnegativeLogConvex

@[expose] public section

/-! Genuine L² interpolation of ordinary derivative words. Integration
by parts gives log-convexity of the largest norm at each order. This
yields endpoint product estimates without a change of Sobolev order. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field Finset
open scoped ContDiff

def wordMaximum (n : ℕ) (A : SmoothL2Field Space) : ℝ :=
  (univ : Finset (Fin n → Fin 3)).sup' univ_nonempty (fun w => ‖(wordField A w).toLp‖)

theorem word_norm_le_maximum (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ‖(wordField A w).toLp‖ ≤ wordMaximum n A :=
  le_sup' (fun v => ‖(wordField A v).toLp‖) (mem_univ w)

theorem wordMaximum_nonneg (A : SmoothL2Field Space) (n : ℕ) : 0 ≤ wordMaximum n A :=
  (norm_nonneg _).trans (word_norm_le_maximum A (fun _ => 0 : Fin n → Fin 3))

theorem wordMaximum_le {A : SmoothL2Field Space} {s n : ℕ} {M : ℝ}
    (h : WordBound s M A) (hn : n ≤ s) : wordMaximum n A ≤ M :=
  sup'_le univ_nonempty _ (fun w _ => h n hn w)

theorem wordMaximum_logconvex (A : SmoothL2Field Space) (n : ℕ) :
    (wordMaximum (n+1) A)^2 ≤ wordMaximum n A*wordMaximum (n+2) A := by
  obtain ⟨w,_,hw⟩ := exists_mem_eq_sup' (univ_nonempty :
    (univ : Finset (Fin (n+1) → Fin 3)).Nonempty) (fun w => ‖(wordField A w).toLp‖)
  change wordMaximum (n+1) A=‖(wordField A w).toLp‖ at hw
  rw [hw]
  let B := wordField A (Fin.tail w)
  let v := axis (w 0)
  change ‖(B.directionalField v).toLp‖^2 ≤ _
  have he := field_directional_inner B (B.directionalField v) v
  rw [real_inner_self_eq_norm_sq] at he
  calc
    _ = -⟪B.toLp,((B.directionalField v).directionalField v).toLp⟫_ℝ := he
    _ ≤ |⟪B.toLp,((B.directionalField v).directionalField v).toLp⟫_ℝ| := neg_le_abs _
    _ ≤ ‖B.toLp‖*‖((B.directionalField v).directionalField v).toLp‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ wordMaximum n A*wordMaximum (n+2) A := by
      apply mul_le_mul (word_norm_le_maximum A (Fin.tail w)) _ (norm_nonneg _)
        (wordMaximum_nonneg A n)
      exact word_norm_le_maximum A (Fin.cons (w 0) (Fin.cons (w 0) (Fin.tail w)))

theorem wordMaximum_product_le (A : SmoothL2Field Space) (m : ℕ) (M N : ℝ)
    (hM : WordBound 3 M A) (hN : WordBound m N A)
    {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) (hab : a+b ≤ m+3) :
    wordMaximum a A*wordMaximum b A ≤ M*N := by
  have hm := wordBound_nonneg hM
  by_cases has : a ≤ 3
  · exact mul_le_mul (wordMaximum_le hM has) (wordMaximum_le hN hb)
      (wordMaximum_nonneg A b) hm
  by_cases hbs : b ≤ 3
  · rw [mul_comm (wordMaximum a A)]
    exact mul_le_mul (wordMaximum_le hM hbs) (wordMaximum_le hN ha)
      (wordMaximum_nonneg A a) hm
  have he (c d : ℕ) (hcs : 3 ≤ c) (hcd : c ≤ d) (hcm : c+d ≤ m+3) :
      wordMaximum c A*wordMaximum d A ≤ M*N := by
    have h := EulerNonnegativeLogConvex.between (fun j => wordMaximum j A)
      (wordMaximum_nonneg A) (wordMaximum_logconvex A) 3 c d hcs hcd
    exact h.trans (mul_le_mul (wordMaximum_le hM (le_refl 3))
      (wordMaximum_le hN (by omega)) (wordMaximum_nonneg A _) hm)
  rcases le_total a b with h | h
  · exact he a b (by omega) h hab
  · rw [mul_comm (wordMaximum a A)]
    exact he b a (by omega) h (by omega)

theorem wordMaximum_directional (A : SmoothL2Field Space) (n : ℕ) (i : Fin 3) :
    wordMaximum n (A.directionalField (axis i)) ≤ wordMaximum (n+1) A := by
  apply sup'_le
  intro w _
  rw [← wordField_snoc]
  exact word_norm_le_maximum A (Fin.snoc w i)

theorem wordMaximum_wordField (A : SmoothL2Field Space) {k : ℕ} (w : Fin k → Fin 3) (n : ℕ) :
    wordMaximum n (wordField A w) ≤ wordMaximum (n+k) A := by
  induction k generalizing A with
  | zero => simp only [wordField_zero,Nat.add_zero,le_refl]
  | succ k ih =>
    have he : wordField A w=wordField (A.directionalField (axis (w (Fin.last k)))) (Fin.init w) :=
      by
      simpa only [Fin.snoc_init_self] using wordField_snoc A (Fin.init w) (w (Fin.last k))
    rw [he]
    exact (ih _ _).trans (wordMaximum_directional A (n+k) (w (Fin.last k)))

theorem jet_norm_le_wordMaximum (A : SmoothL2Field Space) (n : ℕ) :
    ‖A.jetLp n‖ ≤ (3 : ℝ)^n*wordMaximum n A := by
  apply (jet_norm_le_word_sum A n).trans
  calc
    _ ≤ ∑ _w : Fin n → Fin 3, wordMaximum n A :=
      sum_le_sum (fun w _ => word_norm_le_maximum A w)
    _ = _ := by simp

theorem wordField_jet_maximum (A : SmoothL2Field Space) {k : ℕ} (w : Fin k → Fin 3) (n : ℕ) :
    ‖(wordField A w).jetLp n‖ ≤ (3 : ℝ)^n*wordMaximum (k+n) A := by
  apply (jet_norm_le_wordMaximum (wordField A w) n).trans
  simpa only [Nat.add_comm n k] using mul_le_mul_of_nonneg_left
    (wordMaximum_wordField A w n) (by positivity : 0 ≤ (3 : ℝ)^n)

theorem wordField_pointwise_maximum (A : SmoothL2Field Space) {k : ℕ}
    (w : Fin k → Fin 3) (x : Space) :
    ‖(wordField A w).field x‖ ≤ EulerSmoothSobolev.smoothEmbeddingConstant*
      (∑ j ∈ range 3, (3 : ℝ)^j*wordMaximum (k+j) A) :=
  (real_pointwise_H2 (wordField A w) x).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum (fun j _ => wordField_jet_maximum A w j))
    EulerSmoothSobolev.smoothEmbeddingConstant_nonneg)

end EulerOrdinarySobolev
