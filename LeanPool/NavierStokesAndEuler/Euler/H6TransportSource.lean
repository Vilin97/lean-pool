/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct

@[expose] public section

/-! The actual transport forcing has the shifted Gevrey H⁶ estimate without a cutoff-plus-one loss.
  -/

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse EulerPacketWeights
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

section FiniteSums
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem word_zero {n : ℕ} (w : Fin n → Fin 4) :
    iteratedFieldDerivative period w (0 : LiftDomain period → F) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih]
    ext x
    change fderiv ℝ (fun _ : LiftTangent => (0 : F)) 0 _ = 0
    simp

@[simp] theorem wordSobolevNorm_zero_field (q n : ℕ) :
    wordSobolevNorm period q n (0 : LiftDomain period → F) = 0 := by
  simp [wordSobolevNorm, liftSobolevNorm, word_zero]

omit [Fact (0 < period)] in
theorem smooth_sum {α : Type*} (s : Finset α) (f : α → LiftDomain period → F)
    (hf : ∀ i ∈ s, ∀ x, ContDiff ℝ ∞ (localFieldLift period (f i) x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (∑ i ∈ s, f i) x) := by
  intro x
  have he : localFieldLift period (∑ i ∈ s, f i) x =
      fun y => ∑ i ∈ s, localFieldLift period (f i) x y := by
    funext y
    simp [localFieldLift]
  rw [he]
  exact ContDiff.sum (fun i hi => hf i hi x)

omit [Fact (0 < period)] in
theorem word_sum {α : Type*} (s : Finset α) (f : α → LiftDomain period → F)
    (hf : ∀ i ∈ s, ∀ x, ContDiff ℝ ∞ (localFieldLift period (f i) x))
    {n : ℕ} (w : Fin n → Fin 4) :
    iteratedFieldDerivative period w (∑ i ∈ s, f i) =
      ∑ i ∈ s, iteratedFieldDerivative period w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [word_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add period w (f a) (∑ i ∈ s, f i) (hf a (Finset.mem_insert_self ..))
        (smooth_sum period s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem sum_all_memLp {α : Type*} (s : Finset α) (f : α → LiftDomain period → F)
    (hf : ∀ i ∈ s, ∀ x, ContDiff ℝ ∞ (localFieldLift period (f i) x))
    (hfL2 : ∀ i ∈ s, ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (f i)) 2 (liftMeasure period)) :
    ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (∑ i ∈ s, f i)) 2 (liftMeasure period) := by
  intro j w
  rw [word_sum period s f hf w]
  exact memLp_finsetSum' s (fun i hi => hfL2 i hi j w)

theorem wordSobolevNorm_sum_le {α : Type*} (s : Finset α) (q n : ℕ)
    (f : α → LiftDomain period → F)
    (hf : ∀ i ∈ s, ∀ x, ContDiff ℝ ∞ (localFieldLift period (f i) x))
    (hfL2 : ∀ i ∈ s, ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (f i)) 2 (liftMeasure period)) :
    wordSobolevNorm period q n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, wordSobolevNorm period q n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (wordSobolevNorm_add_le period q n (f a) (∑ i ∈ s, f i)
      (hf a (Finset.mem_insert_self ..)) (smooth_sum period s f (fun i hi => hf i
        (Finset.mem_insert_of_mem hi)))
      (hfL2 a (Finset.mem_insert_self ..)) (sum_all_memLp period s f
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfL2 i
          (Finset.mem_insert_of_mem hi)))).trans
      (add_le_add le_rfl (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfL2 i (Finset.mem_insert_of_mem hi))))

end FiniteSums

section Postcomposition
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem wordSobolevNorm_postcomp_le (q n : ℕ) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period)) :
    wordSobolevNorm period q n (L ∘ f) ≤ wordSobolevNorm period q n f := by
  apply Finset.sum_le_sum
  intro w _
  rw [EulerRealCylinder.iteratedFieldDerivative_postcomp period L w f hf]
  exact postcomp_sobolevNorm_le period q L hL _ (iteratedFieldDerivative_smooth period w f hf)
    (fun j _ v => word_all_memLp period w f hfL2 j v)

end Postcomposition

/-- Actual transport in the four cylinder coordinates; angle is the first coordinate. -/
def transportField (q : ℕ) (b : LiftDomain period → Domain 4) (e : LiftDomain period → Domain q) :
    LiftDomain period → Domain q :=
  ∑ i : Fin 4, (fun x => b x i • fieldDerivative period (standardDirection i) e x)

theorem transport_all_memLp (q : ℕ) (b : LiftDomain period → Domain 4) (e : LiftDomain period →
  Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
      period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
      period)) :
    ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (transportField period q b e)) 2 (liftMeasure period)
        := by
  apply sum_all_memLp period Finset.univ
  · intro i _ x
    exact (postcomp_smooth period (coordinate 4 i) b hb x).smul (fieldDerivative_smooth period _ e
      he x)
  · intro i _
    exact product_all_memLp period q (coordinate 4 i ∘ b) _
      (postcomp_smooth period _ b hb) (fieldDerivative_smooth period _ e he)
      (fun j w => postcomp_word_memLp period (show j ≤ j by omega) _ b hb (fun r _ v => hbL2 r v) w)
      (derivative_all_memLp period e heL2 i)

/-- The actual transport source has a single derivative on the transported H⁶ block. -/
theorem transport_wordSobolevNorm_bound (q n : ℕ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
      period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
      period)) :
    wordSobolevNorm period 6 n (transportField period q b e) ≤
      productConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 (l + 1) e) n :=
          by
  have hbi (i : Fin 4) := postcomp_smooth period (coordinate 4 i) b hb
  have hbiL2 (i : Fin 4) : ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (coordinate 4 i ∘ b)) 2 (liftMeasure period) :=
    fun j w => postcomp_word_memLp period (show j ≤ j by omega) _ b hb (fun r _ v => hbL2 r v) w
  have hs := wordSobolevNorm_sum_le period Finset.univ 6 n
    (fun i x => b x i • fieldDerivative period (standardDirection i) e x)
    (fun i _ x => (hbi i x).smul (fieldDerivative_smooth period _ e he x))
    (fun i _ => product_all_memLp period q (coordinate 4 i ∘ b) _ (hbi i)
      (fieldDerivative_smooth period _ e he) (hbiL2 i) (derivative_all_memLp period e heL2 i))
  apply hs.trans
  calc
    _ ≤ ∑ i : Fin 4, productConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 6 l b)
        (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) e)) n :=
          by
      apply Finset.sum_le_sum
      intro i _
      have hp := product_wordSobolevNorm_bound period q n (coordinate 4 i ∘ b) _ (hbi i)
        (fieldDerivative_smooth period _ e he) (hbiL2 i) (derivative_all_memLp period e heL2 i)
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (productConstant_nonneg period q)
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (wordSobolevNorm_postcomp_le period 6 l (coordinate 4 i) (coordinate_norm_le 4 i) b hb
            hbL2)
          (Nat.cast_nonneg _)) (wordSobolevNorm_nonneg period 6 (n-l) _)
    _ = _ := by
      rw [← Finset.mul_sum, sum_leibnizConvolution_right]
      simp_rw [← wordSobolevNorm_succ]

/-- Source18's transport forcing bound, with every velocity derivative at or below the cutoff N. -/
theorem transport_shifted_weighted_bound (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
      period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
      period)) :
    (∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℝ) * weight ρ (n+1) *
      wordSobolevNorm period 6 n (transportField period q b e)) ≤
      2 * productConstant period q *
        (∑ l ∈ Finset.range (N+1), weight ρ l * wordSobolevNorm period 6 l b) *
        (∑ j ∈ Finset.range (N+1), (j : ℝ) * weight ρ j * wordSobolevNorm period 6 j e) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℝ) * weight ρ (n+1) *
        (productConstant period q * leibnizConvolution
          (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 (l+1) e) n) :=
            by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left (transport_wordSobolevNorm_bound period q n b e hb he hbL2
        heL2)
        (mul_nonneg (Nat.cast_nonneg _) (weight_pos hρ _).le)
    _ = productConstant period q * (∑ n ∈ Finset.range N, ∑ l ∈ Finset.range (n+1),
        ((n+1 : ℕ) : ℝ) * weight ρ (n+1) * (n.choose l : ℝ) *
          wordSobolevNorm period 6 l b * wordSobolevNorm period 6 (n-l+1) e) := by
      simp only [leibnizConvolution, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (EulerWeightedConvolution.shifted_source_sum ρ hρ N
          (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 l e)
          (fun l => wordSobolevNorm_nonneg period 6 l b) (fun l => wordSobolevNorm_nonneg period 6
            l e))
        (productConstant_nonneg period q)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end EulerH6Nonlinear
