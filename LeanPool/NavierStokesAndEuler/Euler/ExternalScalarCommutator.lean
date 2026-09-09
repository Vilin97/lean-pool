/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.H6TransportSource

@[expose] public section

/-! Actual fixed-H⁶ external scalar multiplication commutators with positive-order binomial bounds.
  -/

noncomputable section

namespace EulerExternalScalarCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerH6Nonlinear
    EulerBaseTransportCommutator
  EulerJetProductBounds EulerSpatialSobolevInverse
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

section Subtraction
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f-g) = fieldDerivative period a f-fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.sub (((hg x).differentiable (by
    simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] F => A a) h.fderiv

omit [Fact (0 < period)] in
theorem word_sub {n : ℕ} (w : Fin n → Fin 4) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    iteratedFieldDerivative period w (f-g) = iteratedFieldDerivative period w
      f-iteratedFieldDerivative period w g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w), fieldDerivative_sub period _ _ _
      (iteratedFieldDerivative_smooth period _ f hf) (iteratedFieldDerivative_smooth period _ g hg)]
    rfl

end Subtraction

omit [Fact (0 < period)] in
theorem scalarCommutator_smooth {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (scalarCommutator period w f g) x) :=
  fun x => (iteratedFieldDerivative_smooth period w (fun x => f x • g x) (fun y => (hf y).smul (hg
    y)) x).sub
    ((hf x).smul (iteratedFieldDerivative_smooth period w g hg x))

theorem scalarCommutator_all_memLp {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u (scalarCommutator period w f
      g)) 2 (liftMeasure period) := by
  intro j u
  rw [scalarCommutator, word_sub period u (iteratedFieldDerivative period w (fun x => f x • g x))
    (fun x => f x • iteratedFieldDerivative period w g x)
    (iteratedFieldDerivative_smooth period w (fun x => f x • g x) (fun x => (hf x).smul (hg x)))
    (fun x => (hf x).smul (iteratedFieldDerivative_smooth period w g hg x))]
  exact (word_all_memLp period w _ (product_all_memLp period 3 f g hf hg hfL hgL) j u).sub
    (product_all_memLp period 3 f _ hf (iteratedFieldDerivative_smooth period w g hg) hfL
      (word_all_memLp period w g hgL) j u)

/-- Sum of actual H⁶ norms of external commutators at one order. -/
def commutatorH6Norm (n : ℕ) (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3) : ℝ :=
  ∑ w : Fin n → Fin 4, liftSobolevNorm period 6 (scalarCommutator period w f g)

theorem commutatorH6Norm_nonneg (n : ℕ) (f : LiftDomain period → ℝ) (g : LiftDomain period →
  Vector3) :
    0 ≤ commutatorH6Norm period n f g := Finset.sum_nonneg fun _ _ => liftSobolevNorm_nonneg period
      6 _

@[simp] theorem commutatorH6Norm_zero (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
  :
    commutatorH6Norm period 0 f g = 0 := by
  simp [commutatorH6Norm, scalarCommutator, iteratedFieldDerivative_zero, liftSobolevNorm,
    EulerH6Nonlinear.word_zero]

/-- The exact differential recurrence gives a recurrence of the actual fixed-base Sobolev norms. -/
theorem commutatorH6Norm_succ_le (n : ℕ) (f : LiftDomain period → ℝ) (g : LiftDomain period →
  Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    commutatorH6Norm period (n+1) f g ≤ ∑ i : Fin 4,
      (wordSobolevNorm period 6 n (fun x => fieldDerivative period (standardDirection i) f x • g x)
        +
        commutatorH6Norm period n f (fieldDerivative period (standardDirection i) g)) := by
  rw [commutatorH6Norm, sum_word_snoc]
  apply Finset.sum_le_sum
  intro i _
  rw [wordSobolevNorm, commutatorH6Norm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [scalarCommutator_recurrence period _ f g hf hg]
  have hi : (Fin.snoc (α := fun _ : Fin (n+1) => Fin 4) w i) (Fin.last n) = i := by simp [Fin.snoc]
  simp only [Fin.init_snoc, hi]
  have hdf := fieldDerivative_smooth period (standardDirection i) f hf
  have hdg := fieldDerivative_smooth period (standardDirection i) g hg
  have hdfL := derivative_all_memLp period f hfL i
  have hdgL := derivative_all_memLp period g hgL i
  exact sobolev_add_le period 6 _ _
    (iteratedFieldDerivative_smooth period w _ (fun x => (hdf x).smul (hg x)))
    (scalarCommutator_smooth period w f _ hf hdg)
    (fun j _ u => word_all_memLp period w _ (product_all_memLp period 3 _ g hdf hg hdfL hgL) j u)
    (fun j _ u => scalarCommutator_all_memLp period w f _ hf hdg hfL hdgL j u)

/-- The actual external commutator has exactly the positive-coefficient-order binomial convolution. -/
theorem commutatorH6Norm_bound (n : ℕ) (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    commutatorH6Norm period n f g ≤ productConstant period 3 *
      commutatorConvolution (fun l => wordSobolevNorm period 6 l f) (fun l => wordSobolevNorm
        period 6 l g) n := by
  induction n generalizing f g with
  | zero => simp [commutatorConvolution_eq_sum]
  | succ n ih =>
    apply (commutatorH6Norm_succ_le period n f g hf hg hfL hgL).trans
    calc
      _ ≤ ∑ i : Fin 4, (productConstant period 3 * leibnizConvolution
          (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) f))
          (fun l => wordSobolevNorm period 6 l g) n + productConstant period 3 *
            commutatorConvolution
          (fun l => wordSobolevNorm period 6 l f)
          (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) g)) n)
            := by
        apply Finset.sum_le_sum
        intro i _
        exact add_le_add (product_wordSobolevNorm_bound period 3 n _ g
          (fieldDerivative_smooth period _ f hf) hg (derivative_all_memLp period f hfL i) hgL)
          (ih f _ hf (fieldDerivative_smooth period _ g hg) hfL (derivative_all_memLp period g hgL
            i))
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_leibnizConvolution_left, sum_commutatorConvolution_right, commutatorConvolution_succ]
        simp_rw [← wordSobolevNorm_succ]
        ring

end EulerExternalScalarCommutator
