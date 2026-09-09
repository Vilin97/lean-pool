/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MixedWordProduct

@[expose] public section

/-! The actual base Sobolev transport commutator with no uncontrolled extra derivative. -/

noncomputable section

namespace EulerBaseTransportCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerGeneralCylinderAlgebra
    EulerH6Nonlinear
  EulerMixedH5Product
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of H⁵ norms of the four actual first derivatives. -/
def gradientFiveNorm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F) : ℝ :=
  ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) f)

theorem gradientFiveNorm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F) : 0 ≤ gradientFiveNorm period f :=
  Finset.sum_nonneg fun _ _ => liftSobolevNorm_nonneg period 5 _

theorem derivative_le_gradientFiveNorm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F) (i : Fin 4) :
    liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) f) ≤ gradientFiveNorm
      period f :=
  Finset.single_le_sum (f := fun j : Fin 4 => liftSobolevNorm period 5 (fieldDerivative period
    (standardDirection j) f))
    (fun j _ => liftSobolevNorm_nonneg period 5 (fieldDerivative period (standardDirection j) f))
      (Finset.mem_univ i)

/-- Six actual derivatives of a field give five derivatives of each first derivative. -/
theorem derivative_memLp_five {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F)
    (hfL : ∀ j ≤ 6, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (i : Fin 4) : ∀ j ≤ 5, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) f)) 2
        (liftMeasure period) := by
  intro j hj w
  exact word_memLp period (by omega : 1+j ≤ 6) w (fun _ : Fin 1 => i) f hfL

/-- The literal differential commutator D^w(fg)−f D^w g. -/
def scalarCommutator {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3) : LiftDomain period → Vector3 :=
  iteratedFieldDerivative period w (fun x => f x • g x) -
    (fun x => f x • iteratedFieldDerivative period w g x)

omit [Fact (0 < period)] in
/-- Exact commutator recurrence isolates one actual derivative of the scalar coefficient. -/
theorem scalarCommutator_recurrence {n : ℕ} (w : Fin (n+1) → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    scalarCommutator period w f g =
      iteratedFieldDerivative period (Fin.init w)
        (fun x => fieldDerivative period (standardDirection (w (Fin.last n))) f x • g x) +
      scalarCommutator period (Fin.init w) f (fieldDerivative period (standardDirection (w
        (Fin.last n))) g) := by
  unfold scalarCommutator
  rw [word_init_last period w, fieldDerivative_smul period _ f g hf hg]
  have hleft : ∀ x, ContDiff ℝ ∞ (localFieldLift period
      (fun x => fieldDerivative period (standardDirection (w (Fin.last n))) f x • g x) x) :=
    fun x => (fieldDerivative_smooth period _ f hf x).smul (hg x)
  have hright : ∀ x, ContDiff ℝ ∞ (localFieldLift period
      (fun x => f x • fieldDerivative period (standardDirection (w (Fin.last n))) g x) x) :=
    fun x => (hf x).smul (fieldDerivative_smooth period _ g hg x)
  rw [word_add period (Fin.init w) _ _ hleft hright, word_init_last period w g]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

/-- The commutator cancels its apparent highest derivative before the L² estimate is applied. -/
theorem mixed_scalarCommutator_bound {n l : ℕ} (hnl : n+l ≤ 6)
    (w : Fin n → Fin 4) (v : Fin l → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j ≤ 6, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    MemLp (scalarCommutator period w f (iteratedFieldDerivative period v g)) 2 (liftMeasure period)
      ∧
    (eLpNorm (scalarCommutator period w f (iteratedFieldDerivative period v g)) 2 (liftMeasure
      period)).toReal ≤
      ((2 : ℝ)^n-1) * mixedConstant period * gradientFiveNorm period f * liftSobolevNorm period 5 g
        := by
  induction n generalizing l with
  | zero => simp [scalarCommutator, iteratedFieldDerivative_zero]
  | succ n ih =>
    let i := w (Fin.last n)
    have hgV := iteratedFieldDerivative_smooth period v g hg
    rw [scalarCommutator_recurrence period w f _ hf hgV]
    have h1 := mixed_outer_product_bound period (by omega : n+0+l ≤ 5) (Fin.init w) Fin.elim0 v
      (fieldDerivative period (standardDirection i) f) g (fieldDerivative_smooth period _ f hf) hg
      (derivative_memLp_five period f hfL i) hgL
    have h2 := ih (by omega : n+(l+1) ≤ 6) (Fin.init w) (Fin.cons i v)
    have h3 : (eLpNorm (iteratedFieldDerivative period (Fin.init w)
        (fun x => fieldDerivative period (standardDirection i) f x • iteratedFieldDerivative period
          v g x))
        2 (liftMeasure period)).toReal ≤ (2 : ℝ)^n * mixedConstant period * gradientFiveNorm period
          f * liftSobolevNorm period 5 g :=
      h1.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (derivative_le_gradientFiveNorm period f i)
          (mul_nonneg (pow_nonneg (by norm_num) n) (mixedConstant_nonneg period)))
        (liftSobolevNorm_nonneg period 5 g))
    refine ⟨h1.1.add h2.1, ?_⟩
    have hh := fieldL2_add_le period _ _ h1.1 h2.1
    exact hh.trans ((add_le_add h3 h2.2).trans_eq (by rw [pow_succ]; ring))

/-- The actual base commutator through six derivatives has the source's H⁵×H⁵ bound. -/
theorem scalarCommutator_bound {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j ≤ 6, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
      period))
    (hgL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
      period)) :
    MemLp (scalarCommutator period w f g) 2 (liftMeasure period) ∧
    (eLpNorm (scalarCommutator period w f g) 2 (liftMeasure period)).toReal ≤
      ((2 : ℝ)^n-1) * mixedConstant period * gradientFiveNorm period f * liftSobolevNorm period 5 g
        := by
  exact mixed_scalarCommutator_bound period (by omega : n+0 ≤ 6) w Fin.elim0 f g hf hg hfL hgL

end EulerBaseTransportCommutator
