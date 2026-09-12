/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder
public import LeanPool.NavierStokesAndEuler.Euler.H6TransportSource
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedCurl
import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedConvolution
public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.Euler.Foundations.RealCylinder
import LeanPool.NavierStokesAndEuler.Euler.GeneralCylinderAlgebra

/-! The actual external transport commutator and its cutoff-independent Gevrey radius-loss estimate.
-/

section

/-! The actual base Sobolev transport commutator with no uncontrolled extra derivative. -/

section

/-! Mixed derivative product estimates with only five total derivatives, for the base transport
commutator. -/

@[expose] public section

noncomputable section

namespace EulerMixedH5Product

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
    EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerGeneralCylinderAlgebra

open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An explicit uniform constant for mixed scalar-vector derivative products through total order
five. -/
def mixedConstant : ℝ := 3 * 85 * cylinderEmbeddingConstant period

theorem mixedConstant_nonneg : 0 ≤ mixedConstant period := by
  unfold mixedConstant
  exact mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)

/-- Low scalar derivatives are bounded by the original H⁵ norm. -/
theorem scalar_word_pointwise {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 4)
    (f : LiftDomain period → ℝ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤ mixedConstant period * liftSobolevNorm period 5 f := by
  have h := real_cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : k+j ≤ 5) v w f hfL) x
  have h2 := mul_le_mul_of_nonneg_left (word_H3_le_Hq period (by omega : k+3 ≤ 5) w f)
    (cylinderEmbeddingConstant_nonneg period)
  apply h.trans (h2.trans _)
  unfold mixedConstant
  have hpos := mul_nonneg (cylinderEmbeddingConstant_nonneg period) (liftSobolevNorm_nonneg period
      5 f)
  nlinarith

/-- Low vector derivatives are bounded by the original H⁵ norm. -/
theorem vector_word_pointwise {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 4)
    (f : LiftDomain period → Vector3) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤ mixedConstant period * liftSobolevNorm period 5 f := by
  have h := vector_cylinder_pointwise_le_H3 period 3 (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : k+j ≤ 5) v w f hfL) x
  have h2 := mul_le_mul_of_nonneg_left (word_H3_le_Hq period (by omega : k+3 ≤ 5) w f)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (cylinderEmbeddingConstant_nonneg period))
  exact h.trans (h2.trans_eq (by unfold mixedConstant; ring))

/-- An actual pointwise L² domination gives both integrability and the corresponding norm estimate.
-/
theorem memLp_norm_of_domination {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : LiftDomain period → E) (g : LiftDomain period → F) (c : ℝ) (hc : 0 ≤ c)
    (hf : AEStronglyMeasurable f (liftMeasure period)) (hg : MemLp g 2 (liftMeasure period))
    (h : ∀ᵐ x ∂liftMeasure period, ‖f x‖ ≤ c * ‖g x‖) :
    MemLp f 2 (liftMeasure period) ∧
      (eLpNorm f 2 (liftMeasure period)).toReal ≤ c*(eLpNorm g 2 (liftMeasure period)).toReal := by
  have hm := hg.of_le_mul hf h
  refine ⟨hm, ?_⟩
  have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul h (2 : ℝ≥0∞)
  have hfin : ENNReal.ofReal c * eLpNorm g 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hh' := ENNReal.toReal_mono hfin hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hh'

/-- The literal product of two derivative words with at most five total derivatives is in L² with a
fixed H⁵ bound. -/
theorem mixed_product_bound {k l : ℕ} (hkl : k + l ≤ 5)
    (w : Fin k → Fin 4) (v : Fin l → Fin 4)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure
        period))
    (hgL : ∀ j ≤ 5, ∀ u : Fin j → Fin 4, MemLp (iteratedFieldDerivative period u g) 2 (liftMeasure
        period)) :
    MemLp (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x) 2
        (liftMeasure period) ∧
    (eLpNorm (fun x => iteratedFieldDerivative period w f x • iteratedFieldDerivative period v g x)
      2 (liftMeasure period)).toReal ≤ mixedConstant period * liftSobolevNorm period 5 f *
          liftSobolevNorm period 5 g := by
  have hmeas : AEStronglyMeasurable (fun x => iteratedFieldDerivative period w f x •
      iteratedFieldDerivative period v g x)
      (liftMeasure period) :=
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w f hf)).smul
      (smoothField_continuous period _ (iteratedFieldDerivative_smooth period v g
          hg))).aestronglyMeasurable
  by_cases hk : k ≤ 2
  · have h := memLp_norm_of_domination period _ (iteratedFieldDerivative period v g)
      (mixedConstant period * liftSobolevNorm period 5 f)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 f)) hmeas (hgL l
          (by
          omega) v)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (scalar_word_pointwise period hk w f hf hfL x)
            (norm_nonneg _)))
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (word_L2_le_liftSobolevNorm period (by
        omega : l ≤ 5) v g)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 f)))⟩
  · have hl : l ≤ 2 := by omega
    have h := memLp_norm_of_domination period _ (iteratedFieldDerivative period w f)
      (mixedConstant period * liftSobolevNorm period 5 g)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 g)) hmeas (hfL k
          (by
          omega) w)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (vector_word_pointwise period hl v g hg hgL x)
            (norm_nonneg _)).trans_eq (mul_comm _ _)))
    refine ⟨h.1, h.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (word_L2_le_liftSobolevNorm period (by omega : k ≤ 5) w f)
      (mul_nonneg (mixedConstant_nonneg period) (liftSobolevNorm_nonneg period 5 g))).trans_eq (by
          ring)

/-- The real L² norm obeys the triangle inequality whenever both actual fields are
square-integrable. -/
theorem fieldL2_add_le {E : Type*} [NormedAddCommGroup E]
    (f g : LiftDomain period → E) (hf : MemLp f 2 (liftMeasure period)) (hg : MemLp g 2
        (liftMeasure period)) :
    (eLpNorm (f+g) 2 (liftMeasure period)).toReal ≤
      (eLpNorm f 2 (liftMeasure period)).toReal+(eLpNorm g 2 (liftMeasure period)).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using h

end EulerMixedH5Product

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerBaseTransportCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
    EulerTransportDerivatives
  EulerCylinderSobolev
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
theorem scalarCommutator_recurrence {n : ℕ} (w : Fin (n + 1) → Fin 4)
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
theorem mixed_scalarCommutator_bound {n l : ℕ} (hnl : n + l ≤ 6)
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

end
end

end

section

/-! Actual fixed-H⁶ external scalar multiplication commutators with positive-order binomial bounds.
-/

@[expose] public section

noncomputable section

namespace EulerExternalScalarCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
    EulerTransportDerivatives
  EulerCylinderSobolev   EulerH6Nonlinear
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
  have h := (((hf x).differentiable (by
      simp)) 0).hasFDerivAt.sub (((hg x).differentiable (by simp)) 0).hasFDerivAt
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

/-- The actual external commutator has exactly the positive-coefficient-order binomial convolution.
-/
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerExternalTransportCommutator

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
    EulerTransportDerivatives
  EulerCylinderSobolev  EulerVectorCylinder EulerH6Nonlinear
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

/-- Positivity allows monotonicity of the coefficient sequence in the genuine commutator
convolution. -/
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

/-- The actual external transport commutator obeys the radius-loss bound with no cutoff-dependent
constant or cutoff-plus-one velocity. -/
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
