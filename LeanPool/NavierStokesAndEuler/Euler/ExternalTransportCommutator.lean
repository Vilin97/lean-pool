/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExternalScalarCommutator

@[expose] public section

/-! The actual external transport commutator and its cutoff-independent Gevrey radius-loss
  estimate. -/

noncomputable section

namespace EulerExternalTransportCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerH6Nonlinear
    EulerBaseTransportCommutator
  EulerExternalScalarCommutator EulerJetProductBounds EulerSpatialSobolevInverse EulerPacketWeights
    EulerLiftedCurl
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- Actual coordinate words commute with each constant-direction derivative of a smooth field. -/
theorem word_derivative_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (w : Fin n → Fin 4) (a : LiftTangent) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (fieldDerivative period a f) =
      fieldDerivative period a (iteratedFieldDerivative period w f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w)]
    funext x
    exact fieldDerivatives_commute period _ _ _ (iteratedFieldDerivative_smooth period (Fin.tail w)
      f hf) x

/-- The literal external transport commutator D^w(b·∇e)−b·∇D^w e. -/
def transportCommutator {n : ℕ} (w : Fin n → Fin 4)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3) : LiftDomain period →
      Vector3 :=
  iteratedFieldDerivative period w (transportField period 3 b e) -
    transportField period 3 b (iteratedFieldDerivative period w e)

omit [Fact (0 < period)] in
/-- The actual transport commutator is exactly the sum of the scalar multiplication commutators. -/
theorem transportCommutator_eq_sum {n : ℕ} (w : Fin n → Fin 4)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) :
    transportCommutator period w b e = ∑ i : Fin 4,
      scalarCommutator period w (coordinate 4 i ∘ b) (fieldDerivative period (standardDirection i)
        e) := by
  unfold transportCommutator transportField
  rw [word_sum period Finset.univ (fun i : Fin 4 => fun x => b x i • fieldDerivative period
    (standardDirection i) e x) (fun i _ x =>
    (postcomp_smooth period (coordinate 4 i) b hb x).smul (fieldDerivative_smooth period
      (standardDirection i) e he x)) w,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarCommutator, word_derivative_comm period w (standardDirection i) e he]
  rfl

/-- Sum of the actual H⁶ norms of all external transport commutators at one order. -/
def transportCommutatorNorm (n : ℕ) (b : LiftDomain period → Domain 4) (e : LiftDomain period →
  Vector3) : ℝ :=
  ∑ w : Fin n → Fin 4, liftSobolevNorm period 6 (transportCommutator period w b e)

/-- Positivity allows monotonicity of the coefficient sequence in the genuine commutator convolution. -/
theorem commutatorConvolution_mono_left (n : ℕ) (A A' B : ℕ → ℝ)
    (hA : ∀ l, A l ≤ A' l) (hB : ∀ l, 0 ≤ B l) :
    commutatorConvolution A B n ≤ commutatorConvolution A' B n := by
  rw [commutatorConvolution_eq_sum, commutatorConvolution_eq_sum]
  exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hA (l+1)) (Nat.cast_nonneg _)) (hB _)

/-- The actual external transport commutator has no undifferentiated-velocity term. -/
theorem transportCommutatorNorm_bound (n : ℕ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u b) 2 (liftMeasure
      period))
    (heL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u e) 2 (liftMeasure
      period)) :
    transportCommutatorNorm period n b e ≤ productConstant period 3 *
      commutatorConvolution (fun l => wordSobolevNorm period 6 l b)
        (fun l => wordSobolevNorm period 6 (l+1) e) n := by
  have hbi (i : Fin 4) := postcomp_smooth period (coordinate 4 i) b hb
  have hbiL (i : Fin 4) : ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (coordinate 4 i ∘ b)) 2 (liftMeasure period) :=
    fun j w => postcomp_word_memLp period (show j ≤ j by omega) _ b hb (fun r _ v => hbL r v) w
  have hw (w : Fin n → Fin 4) : liftSobolevNorm period 6 (transportCommutator period w b e) ≤
      ∑ i : Fin 4, liftSobolevNorm period 6
        (scalarCommutator period w (coordinate 4 i ∘ b) (fieldDerivative period (standardDirection
          i) e)) := by
    rw [transportCommutator_eq_sum period w b e hb he]
    have h := wordSobolevNorm_sum_le period Finset.univ 6 0
      (fun i => scalarCommutator period w (coordinate 4 i ∘ b) (fieldDerivative period
        (standardDirection i) e))
      (fun i _ => scalarCommutator_smooth period w _ _ (hbi i) (fieldDerivative_smooth period _ e
        he))
      (fun i _ => scalarCommutator_all_memLp period w _ _ (hbi i) (fieldDerivative_smooth period _
        e he)
        (hbiL i) (derivative_all_memLp period e heL i))
    simpa only [wordSobolevNorm_zero] using h
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => hw w)
  rw [Finset.sum_comm] at hsum
  apply hsum.trans
  calc
    _ ≤ ∑ i : Fin 4, productConstant period 3 * commutatorConvolution
        (fun l => wordSobolevNorm period 6 l b)
        (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) e)) n :=
          by
      apply Finset.sum_le_sum
      intro i _
      have hi := commutatorH6Norm_bound period n _ _ (hbi i) (fieldDerivative_smooth period _ e he)
        (hbiL i) (derivative_all_memLp period e heL i)
      apply hi.trans
      apply mul_le_mul_of_nonneg_left _ (productConstant_nonneg period 3)
      exact commutatorConvolution_mono_left n _ _ _
        (fun l => wordSobolevNorm_postcomp_le period 6 l (coordinate 4 i) (coordinate_norm_le 4 i)
          b hb hbL)
        (fun l => wordSobolevNorm_nonneg period 6 l _)
    _ = _ := by
      rw [← Finset.mul_sum, sum_commutatorConvolution_right]
      simp_rw [← wordSobolevNorm_succ]

/-- The actual external transport commutator obeys the radius-loss bound with no cutoff-dependent constant or cutoff-plus-one velocity. -/
theorem transportCommutator_weighted_bound (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u b) 2 (liftMeasure
      period))
    (heL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u e) 2 (liftMeasure
      period)) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * transportCommutatorNorm period n b e) ≤
      productConstant period 3 * ρ⁻¹ *
        (∑ l ∈ Finset.range (N+1), weight ρ l * wordSobolevNorm period 6 l b) *
        (∑ j ∈ Finset.range (N+1), (j : ℝ)*weight ρ j * wordSobolevNorm period 6 j e) := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1), weight ρ n * (productConstant period 3 * commutatorConvolution
        (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 (l+1) e) n) :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
        (transportCommutatorNorm_bound period n b e hb he hbL heL) (weight_pos hρ n).le
    _ = productConstant period 3 * (∑ n ∈ Finset.range (N+1), ∑ l ∈ Finset.range n,
        weight ρ n * (n.choose (l+1) : ℝ) * wordSobolevNorm period 6 (l+1) b * wordSobolevNorm
          period 6 (n-l) e) := by
      simp only [commutatorConvolution_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro l hl
      have hn : n-(l+1)+1 = n-l := by have := Finset.mem_range.mp hl; omega
      rw [hn]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (EulerWeightedConvolution.external_commutator_sum ρ hρ N
        (fun l => wordSobolevNorm period 6 l b) (fun l => wordSobolevNorm period 6 l e)
        (fun l => wordSobolevNorm_nonneg period 6 l b) (fun l => wordSobolevNorm_nonneg period 6 l
          e))
      (productConstant_nonneg period 3)).trans_eq (by ring)

end EulerExternalTransportCommutator
