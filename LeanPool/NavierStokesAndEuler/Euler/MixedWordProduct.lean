/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MixedH5Product
import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct

/-! Actual outer derivatives of mixed products, with a fixed total derivative budget. -/

@[expose] public section


noncomputable section

namespace EulerMixedH5Product

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
    EulerTransportDerivatives
  EulerCylinderSobolev
      EulerH6Nonlinear
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Outer product differentiation preserves the total derivative budget and costs only the finite
Leibniz factor. -/
theorem mixed_outer_product_bound {n k l : ℕ} (hnkl : n + k + l ≤ 5)
    (a : Fin n → Fin 4) (w : Fin k → Fin 4) (v : Fin l → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
        period))
    (hgL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period a
      (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x)) 2
          (liftMeasure period) ∧
    (eLpNorm (iteratedFieldDerivative period a
      (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x))
      2 (liftMeasure period)).toReal ≤ (2 : ℝ)^n * mixedConstant period * liftSobolevNorm period 5
          f * liftSobolevNorm period 5 g := by
  induction n generalizing k l with
  | zero =>
      simpa only [iteratedFieldDerivative_zero, pow_zero, one_mul] using mixed_product_bound period
          (by
      omega : k+l ≤ 5) w v f g hf hg hfL hgL
  | succ n ih =>
    let i := a (Fin.last n)
    let F := iteratedFieldDerivative period w f
    let G := iteratedFieldDerivative period v g
    have hF : ∀ x, ContDiff ℝ ∞ (localFieldLift period F x) := iteratedFieldDerivative_smooth
        period w f hf
    have hG : ∀ x, ContDiff ℝ ∞ (localFieldLift period G x) := iteratedFieldDerivative_smooth
        period v g hg
    have h1 := ih (by omega : n+(k+1)+l ≤ 5) (Fin.init a) (Fin.cons i w) v
    have h2 := ih (by omega : n+k+(l+1) ≤ 5) (Fin.init a) w (Fin.cons i v)
    have he : iteratedFieldDerivative period a (fun x => F x • G x) =
        iteratedFieldDerivative period (Fin.init a)
          (fun x => iteratedFieldDerivative period (Fin.cons i w) f x • G x) +
        iteratedFieldDerivative period (Fin.init a)
          (fun x => F x • iteratedFieldDerivative period (Fin.cons i v) g x) := by
      rw [word_init_last, fieldDerivative_smul period _ F G hF hG]
      have hleft : ∀ x, ContDiff ℝ ∞ (localFieldLift period
          (fun x => fieldDerivative period (standardDirection i) F x • G x) x) :=
        fun x => (fieldDerivative_smooth period _ F hF x).smul (hG x)
      have hright : ∀ x, ContDiff ℝ ∞ (localFieldLift period
          (fun x => F x • fieldDerivative period (standardDirection i) G x) x) :=
        fun x => (hF x).smul (fieldDerivative_smooth period _ G hG x)
      rw [word_add period (Fin.init a) _ _ hleft hright]
      rfl
    change MemLp (iteratedFieldDerivative period a (fun x => F x • G x)) 2 (liftMeasure period) ∧ _
    rw [he]
    refine ⟨h1.1.add h2.1, ?_⟩
    have hh := fieldL2_add_le period _ _ h1.1 h2.1
    exact hh.trans ((add_le_add h1.2 h2.2).trans_eq (by rw [pow_succ]; ring))

end EulerMixedH5Product
