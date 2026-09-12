/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordInterpolation
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Products
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds

/-! Tame products of genuine ordinary derivatives.  The low norm is
H³ and the high norm has any integer order at least three.  The only
interpolation input is the integration-by-parts theorem in
`OrdinaryWordInterpolation`. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerSmoothSobolev Finset
open scoped ContDiff

/-- Word point bound, given by `smoothEmbeddingConstant*(∑ j ∈ range 3, (3 : ℝ)^j*wordMaximum
(k+j) A)`. -/
def wordPointBound (A : SmoothL2Field Space) (k : ℕ) : ℝ :=
  smoothEmbeddingConstant*(∑ j ∈ range 3, (3 : ℝ)^j*wordMaximum (k+j) A)

theorem wordPointBound_nonneg (A : SmoothL2Field Space) (k : ℕ) : 0 ≤ wordPointBound A k :=
  mul_nonneg smoothEmbeddingConstant_nonneg
    (sum_nonneg (fun j _ => mul_nonneg (by positivity) (wordMaximum_nonneg A _)))

theorem wordPointBound_product (A : SmoothL2Field Space) (m : ℕ) (M N : ℝ)
    (hM : WordBound 3 M A) (hN : WordBound m N A)
    {a b : ℕ} (ha : a + 2 ≤ m) (hb : b ≤ m) (hab : a + b ≤ m + 1) :
    wordPointBound A a*wordMaximum b A ≤ (13*smoothEmbeddingConstant)*M*N := by
  have hj (j : ℕ) (hjr : j ∈ range 3) :
      wordMaximum (a+j) A*wordMaximum b A ≤ M*N :=
    wordMaximum_product_le A m M N hM hN
      (by have := mem_range.mp hjr; omega) hb (by have := mem_range.mp hjr; omega)
  calc
    _ = smoothEmbeddingConstant *
        (∑ j ∈ range 3, (3 : ℝ)^j*(wordMaximum (a+j) A*wordMaximum b A)) := by
      simp only [wordPointBound,sum_mul,mul_assoc]
    _ ≤ smoothEmbeddingConstant*(∑ j ∈ range 3, (3 : ℝ)^j*(M*N)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun j hjr =>
        mul_le_mul_of_nonneg_left (hj j hjr) (by positivity))) smoothEmbeddingConstant_nonneg
    _ = _ := by norm_num [sum_range_succ]; ring

theorem coordinateProduct_word_left (A : SmoothL2Field Space) {k l : ℕ}
    (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(coordinateProduct i (wordField A w) (wordField A v)).toLp‖ ≤
      wordPointBound A k*wordMaximum l A := by
  have hs (x : Space) : ‖(mapField (EuclideanSpace.proj i) (wordField A w)).field x‖ ≤
      wordPointBound A k :=
    (PiLp.norm_apply_le ((wordField A w).field x) i).trans (wordField_pointwise_maximum A w x)
  exact (scalarProduct_norm_left _ _ _ hs).trans (mul_le_mul_of_nonneg_left
    (word_norm_le_maximum A v) (wordPointBound_nonneg A k))

theorem coordinateProduct_word_right (A : SmoothL2Field Space) {k l : ℕ}
    (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(coordinateProduct i (wordField A w) (wordField A v)).toLp‖ ≤
      wordPointBound A l*wordMaximum k A := by
  have h := scalarProduct_norm_right (mapField (EuclideanSpace.proj i) (wordField A w))
    (wordField A v) (wordPointBound A l) (wordField_pointwise_maximum A v)
  have hm : ‖(mapField (EuclideanSpace.proj i) (wordField A w)).toLp‖ ≤ wordMaximum k A :=
    (mapField_norm_le _ _).trans ((mul_le_mul_of_nonneg_right
      (norm_coordinate_le i) (norm_nonneg _)).trans
      (by simpa only [one_mul] using word_norm_le_maximum A w))
  exact h.trans (mul_le_mul_of_nonneg_left hm (wordPointBound_nonneg A l))

theorem coordinateProduct_tame (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m) (M N : ℝ)
    (hM : WordBound 3 M A) (hN : WordBound m N A)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l ≤ m + 1)
    (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(coordinateProduct i (wordField A w) (wordField A v)).toLp‖ ≤ h3ProductConstant*M*N := by
  by_cases h3 : m=3
  · subst m
    simpa only [wordField_zero,pow_zero,one_mul] using
      gradient_outer_product A A M N hM hN hk hl (by omega : 0+k+l ≤ 4)
        (Fin.elim0 : Fin 0 → Fin 3) w v i
  have h4 : 4 ≤ m := by omega
  have hbound : (13*smoothEmbeddingConstant)*M*N ≤ h3ProductConstant*M*N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3ProductConstant_left
      (wordBound_nonneg hM)) (wordBound_nonneg hN)
  rcases le_total k l with h | h
  · exact ((coordinateProduct_word_left A w v i).trans
      (wordPointBound_product A m M N hM hN (by omega) (by omega) hkl)).trans hbound
  · exact ((coordinateProduct_word_right A w v i).trans
      (wordPointBound_product A m M N hM hN (by omega) (by omega) (by omega))).trans hbound

theorem tame_outer_product (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m) (M N : ℝ)
    (hM : WordBound 3 M A) (hN : WordBound m N A)
    {n k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (horder : n + k + l ≤ m + 1)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(wordField (coordinateProduct i (wordField A w) (wordField A v)) a).toLp‖ ≤
      (2 : ℝ)^n*h3ProductConstant*M*N := by
  induction n generalizing k l with
  | zero =>
    simpa only [wordField_zero,pow_zero,one_mul] using
      coordinateProduct_tame A m hm M N hM hN hk hl (by omega) w v i
  | succ n ih =>
    rw [word_coordinateProduct_recurrence,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := ih (k := k+1) (l := l) (by omega) hl (by omega)
      (Fin.init a) (Fin.cons (a (Fin.last n)) w) v
    have h2 := ih (k := k) (l := l+1) hk (by omega) (by omega)
      (Fin.init a) w (Fin.cons (a (Fin.last n)) v)
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

end EulerOrdinarySobolev
