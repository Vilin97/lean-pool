/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.SpatialWords

/-! # Word Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Every ordered split is retained, including repetitions. The only added
factor is the undifferentiated identity in the right Jacobian F = (F-I)+I. -/
def coarseCoeffWordBudget (K κ : ℝ) (F : ℕ → ℝ) (w : List (Fin 2)) : ℝ :=
  2 * K * F w.length + 4 * (K + |κ|) *
    ((iterateSpatialSplits w).map (fun p =>
      F p.1.length * (F p.2.length + if p.2 = [] then 1 else 0))).sum

theorem WordBounds.list_abs_sum_bound {α : Type*} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ g a) : |(L.map f).sum| ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb))))

theorem coarseCoeff_constant_matrix_word {D : Vec 2 → CoarseMatrix}
    (hD : ContDiff ℝ (⊤ : ℕ∞) D) (K : CoarseMatrix) (w : List (Fin 2))
    (x : Vec 2) (i j : Fin 2) :
    iterateSpatialWord w (fun y => (K * D y) i j) x =
      ∑ p : Fin 2, K i p * iterateSpatialWord w (fun y => D y p j) x := by
  simp only [Matrix.mul_apply]
  rw [iterateSpatialWord_sum Finset.univ _ (fun p _ => contDiff_const.mul
    (contDiff_pi.1 (contDiff_pi.1 hD p) j))]
  apply Finset.sum_congr rfl
  intro p _
  exact congrFun (iterateSpatialWord_const_mul (contDiff_pi.1 (contDiff_pi.1 hD p) j) (K i p) w) x

/-- The quadratic term is an explicit Leibniz expansion of two flow factors. -/
theorem coarseCoeff_quadratic_word {D F : Vec 2 → CoarseMatrix}
    (hD : ContDiff ℝ (⊤ : ℕ∞) D) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (C : CoarseMatrix) (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    iterateSpatialWord w (fun y => ((D y).transpose * C * F y) i j) x =
      ∑ q : Fin 2, ∑ p : Fin 2, C p q *
        ((iterateSpatialSplits w).map (fun r =>
          iterateSpatialWord r.1 (fun y => D y p i) x *
          iterateSpatialWord r.2 (fun y => F y q j) x)).sum := by
  have hd p q : ContDiff ℝ (⊤ : ℕ∞) (fun y => D y p q) :=
    contDiff_pi.1 (contDiff_pi.1 hD p) q
  have hf p q : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y p q) :=
    contDiff_pi.1 (contDiff_pi.1 hF p) q
  have he : (fun y => ((D y).transpose * C * F y) i j) =
      fun y => ∑ q : Fin 2, ∑ p : Fin 2, C p q * (D y p i * F y q j) := by
    funext y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he, iterateSpatialWord_sum Finset.univ _
    (fun q _ => ContDiff.sum (fun p _ => contDiff_const.mul ((hd p i).mul (hf q j))))]
  apply Finset.sum_congr rfl
  intro q _
  rw [iterateSpatialWord_sum Finset.univ _ (fun p _ => contDiff_const.mul ((hd p i).mul (hf q j)))]
  apply Finset.sum_congr rfl
  intro p _
  rw [iterateSpatialWord_const_mul ((hd p i).mul (hf q j))]
  dsimp only
  congr 1
  exact iterateSpatialWord_mul (hd p i) (hf q j) w x

/-- Quantitative jets of the polynomial use only actual flow jets, at all
suborders in the ordered Leibniz rule. No coefficient jet is assumed. -/
theorem coarseCoeffPolynomial_word_entry_bound {F : Vec 2 → CoarseMatrix}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {K : CoarseMatrix} {k a b κ : ℝ} {B : ℕ → ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hB : ∀ n, 0 ≤ B n)
    (hK : ∀ i j, |K i j| ≤ k)
    (hjets : ∀ w : List (Fin 2), ∀ x i j,
      |iterateSpatialWord w (fun y => (F y - 1) i j) x| ≤ B w.length)
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateSpatialWord w (fun y => coarseCoeffPolynomial a b κ K (F y) i j) x| ≤
      coarseCoeffWordBudget k κ B w := by
  let D : Vec 2 → CoarseMatrix := fun y => F y - 1
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := hF.sub contDiff_const
  have hk : 0 ≤ k := (abs_nonneg _).trans (hK 0 0)
  have hjfull (v : List (Fin 2)) (p q : Fin 2) :
      |iterateSpatialWord v (fun y => F y p q) x| ≤ B v.length + if v = [] then 1 else 0 := by
    have he : (fun y => F y p q) = fun y => D y p q + (1 : CoarseMatrix) p q := by
      funext y
      simp only [D, Matrix.sub_apply, sub_add_cancel]
    rw [he, coarseCoeff_word_add (contDiff_pi.1 (contDiff_pi.1 hD p) q) contDiff_const,
      iterateSpatialWord_const]
    have ht := abs_add_le (iterateSpatialWord v (fun y => D y p q) x)
      (if v = [] then (1 : CoarseMatrix) p q else 0)
    apply ht.trans
    apply add_le_add (hjets v x p q)
    classical
    by_cases hv : v = [] <;> by_cases hpq : p = q <;> simp [hv, hpq, Matrix.one_apply]
  let Q := ((iterateSpatialSplits w).map (fun r =>
    B r.1.length * (B r.2.length + if r.2 = [] then 1 else 0))).sum
  have hprod (p q : Fin 2) :
      |((iterateSpatialSplits w).map (fun r =>
        iterateSpatialWord r.1 (fun y => D y p i) x *
        iterateSpatialWord r.2 (fun y => F y q j) x)).sum| ≤ Q := by
    apply WordBounds.list_abs_sum_bound
    intro r _
    rw [abs_mul]
    exact mul_le_mul (hjets r.1 x p i) (hjfull r.2 q j) (abs_nonneg _) (hB _)
  have hμ (p q : Fin 2) : |(κ • (1 : CoarseMatrix)) p q| ≤ |κ| := by
    classical
    by_cases hpq : p = q <;> simp [Matrix.smul_apply, hpq]
  have hKm (p q : Fin 2) : |(K - κ • (1 : CoarseMatrix)) p q| ≤ k + |κ| := by
    have ht := abs_sub_le (K p q) 0 ((κ • (1 : CoarseMatrix)) p q)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (add_le_add (hK p q) (hμ p q))
  have hlin : |iterateSpatialWord w (fun y => (K * D y) i j) x| ≤ 2 * k * B w.length := by
    rw [coarseCoeff_constant_matrix_word hD]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _p : Fin 2, k * B w.length := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hK i p) (hjets w x p j) (abs_nonneg _) hk
      _ = _ := by simp; ring
  have hquad : |iterateSpatialWord w (fun y =>
      ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y) i j) x| ≤ 4 * (k + |κ|) * Q := by
    rw [coarseCoeff_quadratic_word hD hF]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _q : Fin 2, ∑ _p : Fin 2, (k + |κ|) * Q := by
        apply Finset.sum_le_sum
        intro q _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hKm p q) (hprod p q) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have hls : ContDiff ℝ (⊤ : ℕ∞) (fun y => (K * D y) i j) :=
    contDiff_pi.1 (contDiff_pi.1 (coarseCoeff_matrix_mul_contDiff contDiff_const hD) i) j
  have hqs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y)
      i j) := by
    have hDt : ContDiff ℝ (⊤ : ℕ∞) (fun y => (D y).transpose) :=
      contDiff_pi.2 fun p => contDiff_pi.2 fun q => contDiff_pi.1 (contDiff_pi.1 hD q) p
    exact contDiff_pi.1 (contDiff_pi.1 (coarseCoeff_matrix_mul_contDiff
      (coarseCoeff_matrix_mul_contDiff hDt contDiff_const) hF) i) j
  have htranspose (y : Vec 2) : (F y).transpose - 1 = (D y).transpose := by
    ext p q
    simp [D, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, eq_comm]
  simp only [coarseCoeffPolynomial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, htranspose]
  change |iterateSpatialWord w (fun y => a * (K * D y) i j +
    b * ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y) i j) x| ≤ _
  rw [coarseCoeff_word_add (contDiff_const.mul hls) (contDiff_const.mul hqs),
    iterateSpatialWord_const_mul hls, iterateSpatialWord_const_mul hqs]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add
      (by simpa only [one_mul] using mul_le_mul ha hlin (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      (by simpa only [one_mul] using mul_le_mul hb hquad (abs_nonneg _) (by norm_num : (0 : ℝ) ≤
          1)))

/-- The full coefficient jet budget is derived from the active flow jets.
This applies unchanged to the old and left-Jacobian instances. -/
theorem CoarseCoeffForm.word_entry_bound {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κ : ℝ}
    {s : ℝ → Vec 2 → CoarseMatrix} (hs : CoarseCoeffForm I hΦ m κ s)
    (hm : 1 ≤ m) (t : ℝ) {k : ℝ} {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (hK : ∀ i j, |I.Kmat κ m t i j| ≤ k)
    (hflow : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hjets : ∀ l, I.hatXiML m l t ≠ 0 → ∀ v : List (Fin 2), ∀ y i j,
      |iterateSpatialWord v (fun z => (I.flowGrad hΦ m l t z - 1) i j) y| ≤ B v.length)
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateSpatialWord w (fun y => s t y i j) x| ≤ coarseCoeffWordBudget k κ B w := by
  obtain ⟨a, b, ha, hb, he⟩ := hs.window_form
  have hse : (fun y => s t y i j) =
      fun y => coarseCoeffWindow I hΦ m κ a b t y i j := by
    funext y
    rw [he]
  rw [hse]
  apply coarseCoeffWindow_word_entry_bound I hΦ hm κ a b t hflow w x
  intro l hl p q
  exact coarseCoeffPolynomial_word_entry_bound (hflow l) ha hb hB hK (hjets l hl) w x p q

end AVenhance.Infra.Section4
