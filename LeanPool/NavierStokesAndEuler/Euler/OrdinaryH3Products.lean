/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra

@[expose] public section

/-! The middle H³ product uses genuine H¹×H¹→L². All other
distributions use H² point evaluation. The constant is independent of
the fields and contains no fourth derivative of either H³ argument. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerSmoothSobolev EulerMeanCutoffCurl Finset
open scoped ContDiff

def h3ProductConstant : ℝ :=
  1+13*smoothEmbeddingConstant+4*(1+3*(sobolevConstant : ℝ))^2

theorem h3ProductConstant_nonneg : 0 ≤ h3ProductConstant := by
  have h := smoothEmbeddingConstant_nonneg
  unfold h3ProductConstant
  positivity

theorem h3ProductConstant_left : 13*smoothEmbeddingConstant ≤ h3ProductConstant := by
  unfold h3ProductConstant
  nlinarith [sq_nonneg (1+3*(sobolevConstant : ℝ))]

theorem h3ProductConstant_middle : 4*(1+3*(sobolevConstant : ℝ))^2 ≤ h3ProductConstant := by
  unfold h3ProductConstant
  nlinarith [smoothEmbeddingConstant_nonneg]

theorem scalarProduct_h1_bound (A : SmoothL2Field ℝ) (B : SmoothL2Field Space) :
    ‖(scalarProduct A B).toLp‖ ≤
      4*(‖A.toLp‖+(sobolevConstant : ℝ)*‖A.derivative.toLp‖)*
        (‖B.toLp‖+(sobolevConstant : ℝ)*‖B.derivative.toLp‖) := by
  have h := (smooth_product_h1 A.field B.field A.smooth B.smooth
    A.memLp B.memLp A.derivative.memLp B.derivative.memLp).2
  have he : (scalarProduct A B).field=fun x => A.field x • B.field x :=
    funext (scalarProduct_field A B)
  rw [← he] at h
  change lpNorm (scalarProduct A B).field 2 volume ≤
    4*(lpNorm A.field 2 volume+(sobolevConstant : ℝ)*lpNorm A.derivative.field 2 volume)*
      (lpNorm B.field 2 volume+(sobolevConstant : ℝ)*lpNorm B.derivative.field 2 volume) at h
  rw [field_lpNorm (scalarProduct A B),field_lpNorm A,field_lpNorm A.derivative,
    field_lpNorm B,field_lpNorm B.derivative] at h
  exact h

theorem coordinateProduct_h2_left (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 2 M A) (hB : WordBound 0 N B) (i : Fin 3) :
    ‖(coordinateProduct i A B).toLp‖ ≤ h3ProductConstant*M*N := by
  have hs (x : Space) : ‖(mapField (EuclideanSpace.proj i) A).field x‖ ≤
      (13*smoothEmbeddingConstant)*M :=
    (PiLp.norm_apply_le (A.field x) i).trans (wordBound_pointwise hA x)
  have h := scalarProduct_norm_left (mapField (EuclideanSpace.proj i) A) B _ hs
  apply h.trans
  apply (mul_le_mul_of_nonneg_left (wordBound_toLp hB)
    (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg)
      (wordBound_nonneg hA))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h3ProductConstant_left (wordBound_nonneg hA)) (wordBound_nonneg hB)

theorem coordinateProduct_h2_right (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 0 M A) (hB : WordBound 2 N B) (i : Fin 3) :
    ‖(coordinateProduct i A B).toLp‖ ≤ h3ProductConstant*M*N := by
  have h := scalarProduct_norm_right (mapField (EuclideanSpace.proj i) A) B _
    (wordBound_pointwise hB)
  have hm := wordBound_toLp (wordBound_coordinate hA i)
  apply h.trans
  calc
    _ ≤ ((13*smoothEmbeddingConstant)*N)*M := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hB))
    _ = (13*smoothEmbeddingConstant)*M*N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h3ProductConstant_left (wordBound_nonneg hA)) (wordBound_nonneg
        hB)

theorem coordinateProduct_h1 (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 1 M A) (hB : WordBound 1 N B) (i : Fin 3) :
    ‖(coordinateProduct i A B).toLp‖ ≤ h3ProductConstant*M*N := by
  have ha := wordBound_coordinate hA i
  have h := scalarProduct_h1_bound (mapField (EuclideanSpace.proj i) A) B
  have hc : 0 ≤ (sobolevConstant : ℝ) := sobolevConstant.coe_nonneg
  have hleft := add_le_add (wordBound_toLp ha)
    (mul_le_mul_of_nonneg_left (wordBound_derivative ha le_rfl) hc)
  have hright := add_le_add (wordBound_toLp hB)
    (mul_le_mul_of_nonneg_left (wordBound_derivative hB le_rfl) hc)
  apply h.trans
  calc
    _ ≤ 4*(M+(sobolevConstant : ℝ)*(3*M))*(N+(sobolevConstant : ℝ)*(3*N)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hleft (by norm_num)) hright
        (add_nonneg (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)))
        (mul_nonneg (by norm_num) (add_nonneg (wordBound_nonneg hA)
          (mul_nonneg hc (mul_nonneg (by norm_num) (wordBound_nonneg hA)))))
    _ = (4*(1+3*(sobolevConstant : ℝ))^2)*M*N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h3ProductConstant_middle (wordBound_nonneg hA)) (wordBound_nonneg
        hB)

theorem coordinateProduct_mixed (A B : SmoothL2Field Space) (M N : ℝ)
    {s t k l : ℕ} (hA : WordBound s M A) (hB : WordBound t N B)
    (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3)
    (hmargin : (k+2 ≤ s ∧ l ≤ t) ∨ (k ≤ s ∧ l+2 ≤ t) ∨ (k+1 ≤ s ∧ l+1 ≤ t)) :
    ‖(coordinateProduct i (wordField A w) (wordField B v)).toLp‖ ≤ h3ProductConstant*M*N := by
  rcases hmargin with h | h | h
  · exact coordinateProduct_h2_left _ _ M N
      (wordBound_wordField (wordBound_mono hA h.1) w)
      (wordBound_wordField (wordBound_mono hB (by simpa only [Nat.add_zero] using h.2)) v) i
  · exact coordinateProduct_h2_right _ _ M N
      (wordBound_wordField (wordBound_mono hA (by simpa only [Nat.add_zero] using h.1)) w)
      (wordBound_wordField (wordBound_mono hB h.2) v) i
  · exact coordinateProduct_h1 _ _ M N
      (wordBound_wordField (wordBound_mono hA h.1) w)
      (wordBound_wordField (wordBound_mono hB h.2) v) i

theorem coordinateProduct_directional (A B : SmoothL2Field Space) (i j : Fin 3) :
    (coordinateProduct i A B).directionalField (axis j) =
      addField (coordinateProduct i (A.directionalField (axis j)) B)
        (coordinateProduct i A (B.directionalField (axis j))) := by
  have hm : (mapField (EuclideanSpace.proj i) A).directionalField (axis j) =
      mapField (EuclideanSpace.proj i) (A.directionalField (axis j)) := by
    simpa only [wordField_cons,wordField_zero] using
      wordField_map (EuclideanSpace.proj i) A (Fin.cons j Fin.elim0)
  unfold coordinateProduct
  rw [scalarProduct_directional,hm]

theorem word_coordinateProduct_recurrence (A B : SmoothL2Field Space)
    {n k l : ℕ} (a : Fin (n+1) → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    wordField (coordinateProduct i (wordField A w) (wordField B v)) a =
      addField
        (wordField (coordinateProduct i (wordField A (Fin.cons (a (Fin.last n)) w)) (wordField B
          v)) (Fin.init a))
        (wordField (coordinateProduct i (wordField A w) (wordField B (Fin.cons (a (Fin.last n))
          v))) (Fin.init a)) := by
  conv_lhs => rw [← Fin.snoc_init_self a,wordField_snoc,coordinateProduct_directional,wordField_add]
  simp only [wordField_cons]

theorem gradient_outer_product (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 3 N B)
    {n k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (horder : n+k+l ≤ 4)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(wordField (coordinateProduct i (wordField A w) (wordField B v)) a).toLp‖ ≤
      (2 : ℝ)^n*h3ProductConstant*M*N := by
  induction n generalizing k l with
  | zero =>
    simpa only [wordField_zero,pow_zero,one_mul] using
      coordinateProduct_mixed A B M N hA hB w v i (by omega)
  | succ n ih =>
    rw [word_coordinateProduct_recurrence,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := ih (k := k+1) (l := l) (by omega) hl (by omega)
      (Fin.init a) (Fin.cons (a (Fin.last n)) w) v
    have h2 := ih (k := k) (l := l+1) hk (by omega) (by omega)
      (Fin.init a) w (Fin.cons (a (Fin.last n)) v)
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

theorem source_outer_product (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 4 N B)
    {n k l : ℕ} (hk : n+k ≤ 3) (hl : 1 ≤ l) (horder : n+k+l ≤ 4)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(wordField (coordinateProduct i (wordField A w) (wordField B v)) a).toLp‖ ≤
      (2 : ℝ)^n*h3ProductConstant*M*N := by
  induction n generalizing k l with
  | zero =>
    simpa only [wordField_zero,pow_zero,one_mul] using
      coordinateProduct_mixed A B M N hA hB w v i (by omega)
  | succ n ih =>
    rw [word_coordinateProduct_recurrence,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := ih (k := k+1) (l := l) (by omega) hl (by omega)
      (Fin.init a) (Fin.cons (a (Fin.last n)) w) v
    have h2 := ih (k := k) (l := l+1) (by omega) (by omega) (by omega)
      (Fin.init a) w (Fin.cons (a (Fin.last n)) v)
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

end EulerOrdinarySobolev
