/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! Fixed H⁶ algebra estimates at every external derivative order, for actual nonlinear fields. -/

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

section FieldCalculus
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem fieldDerivative_add (a : LiftTangent) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f + g) = fieldDerivative period a f + fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.add
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] F => A a) h.fderiv

omit [Fact (0 < period)] in
theorem word_add {n : ℕ} (w : Fin n → Fin 4) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    iteratedFieldDerivative period w (f + g) =
      iteratedFieldDerivative period w f + iteratedFieldDerivative period w g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w), fieldDerivative_add period _ _ _
      (iteratedFieldDerivative_smooth period _ f hf) (iteratedFieldDerivative_smooth period _ g hg)]
    rfl

omit [Fact (0 < period)] in
theorem word_init_last {n : ℕ} (w : Fin (n + 1) → Fin 4) (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = iteratedFieldDerivative period (Fin.init w)
      (fieldDerivative period (standardDirection (w (Fin.last n))) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) =
      fieldDerivative period (standardDirection (w 0))
        (iteratedFieldDerivative period (Fin.tail (Fin.init w))
          (fieldDerivative period (standardDirection (w (Fin.last (n+1)))) f))
    rw [ih (Fin.tail w)]
    rfl

theorem derivative_all_memLp (f : LiftDomain period → F)
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (i : Fin 4) :
    ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) f))
        2 (liftMeasure period) := by
  intro j w
  let v : Fin 1 → Fin 4 := fun _ => i
  have h := word_memLp period (show 1+j ≤ 1+j by omega) w v f
    (fun r _ z => hfL2 r z)
  exact h

theorem word_all_memLp {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → F)
    (hfL2 : ∀ j, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period)) :
    ∀ j, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (iteratedFieldDerivative period w f))
        2 (liftMeasure period) := by
  intro j v
  exact word_memLp period (show n+j ≤ n+j by omega) v w f (fun r _ z => hfL2 r z)

theorem sobolev_add_le (q : ℕ) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) :
    liftSobolevNorm period q (f + g) ≤ liftSobolevNorm period q f + liftSobolevNorm period q g := by
  unfold liftSobolevNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [word_add period w f g hf hg]
  have hfj := hfL2 j (by have := Finset.mem_range.1 hj; omega) w
  have hgj := hgL2 j (by have := Finset.mem_range.1 hj; omega) w
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfj.eLpNorm_ne_top, hgj.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hfj.1 hgj.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [ENNReal.toReal_add hfj.eLpNorm_ne_top hgj.eLpNorm_ne_top] using he

/-- Sum of actual Hq norms of all external derivative words of exactly order n. -/
def wordSobolevNorm (q n : ℕ) (f : LiftDomain period → F) : ℝ :=
  ∑ w : Fin n → Fin 4, liftSobolevNorm period q (iteratedFieldDerivative period w f)

theorem wordSobolevNorm_nonneg (q n : ℕ) (f : LiftDomain period → F) :
    0 ≤ wordSobolevNorm period q n f :=
  Finset.sum_nonneg (fun _ _ => liftSobolevNorm_nonneg period q _)

@[simp] theorem wordSobolevNorm_zero (q : ℕ) (f : LiftDomain period → F) :
    wordSobolevNorm period q 0 f = liftSobolevNorm period q f := by simp [wordSobolevNorm]

theorem wordSobolevNorm_succ (q n : ℕ) (f : LiftDomain period → F) :
    wordSobolevNorm period q (n + 1) f =
      ∑ i : Fin 4, wordSobolevNorm period q n (fieldDerivative period (standardDirection i) f) := by
  unfold wordSobolevNorm
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (EulerSpatialSobolevInverse.SpatialJet.wordSnocEquiv n)
    (fun w => liftSobolevNorm period q (iteratedFieldDerivative period w f))
    (fun v => liftSobolevNorm period q (iteratedFieldDerivative period v.2
      (fieldDerivative period (standardDirection v.1) f)))
    (fun w => by
      change liftSobolevNorm period q (iteratedFieldDerivative period w f) =
        liftSobolevNorm period q (iteratedFieldDerivative period (Fin.init w)
          (fieldDerivative period (standardDirection (w (Fin.last n))) f))
      rw [word_init_last period w f])

theorem wordSobolevNorm_add_le (q n : ℕ) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    wordSobolevNorm period q n (f + g) ≤ wordSobolevNorm period q n f + wordSobolevNorm period q n
      g := by
  unfold wordSobolevNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [word_add period w f g hf hg]
  exact sobolev_add_le period q _ _ (iteratedFieldDerivative_smooth period w f hf)
    (iteratedFieldDerivative_smooth period w g hg)
    (fun j _ v => word_all_memLp period w f hfL2 j v)
    (fun j _ v => word_all_memLp period w g hgL2 j v)

end FieldCalculus

omit [Fact (0 < period)] in
theorem fieldDerivative_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : LiftTangent) (f : LiftDomain period → ℝ) (g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (fun x => f x • g x) =
      (fun x => fieldDerivative period a f x • g x) + (fun x => f x • fieldDerivative period a g x)
        := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.smul
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun A : LiftTangent →L[ℝ] F => A a) h.fderiv
  change fderiv ℝ (localFieldLift period f x • localFieldLift period g x) 0 a = _
  simpa [fieldDerivative, localFieldLift, add_comm] using he

/-- All actual derivative words of a smooth H-infinity scalar-vector product lie in L². -/
theorem product_all_memLp (q : ℕ) (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    ∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w (fun x => f x • g x)) 2 (liftMeasure period) := by
  intro j
  induction j generalizing f g with
  | zero =>
    intro w
    apply MemLp.of_eval_piLp
    intro i
    have h := real_product_word_memLp period (show 0 ≤ 6 by omega) w f (coordinate q i ∘ g)
      hf (postcomp_smooth period _ g hg) (fun r _ v => hfL2 r v)
      (fun r _ v => postcomp_word_memLp period (show r ≤ r by omega) _ g hg (fun a _ z => hgL2 a z)
        v)
    exact h
  | succ j ih =>
    intro w
    rw [word_init_last period w, fieldDerivative_smul period _ f g hf hg]
    rw [word_add period (Fin.init w)
      (fun x => fieldDerivative period (standardDirection (w (Fin.last j))) f x • g x)
      (fun x => f x • fieldDerivative period (standardDirection (w (Fin.last j))) g x)
      (fun x => (fieldDerivative_smooth period _ f hf x).smul (hg x))
      (fun x => (hf x).smul (fieldDerivative_smooth period _ g hg x))]
    exact (ih _ _ (fieldDerivative_smooth period _ f hf) hg
      (derivative_all_memLp period f hfL2 _) hgL2 (Fin.init w)).add
      (ih _ _ hf (fieldDerivative_smooth period _ g hg) hfL2
        (derivative_all_memLp period g hgL2 _) (Fin.init w))

/-- The H⁶ algebra constant is fixed, independently of the external derivative order. -/
def productConstant (q : ℕ) : ℝ := (q : ℝ) * (5461 * 128 * lowDerivativeConstant period)

theorem productConstant_nonneg (q : ℕ) : 0 ≤ productConstant period q :=
  mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (lowDerivativeConstant_nonneg period))

/-- Exact external-order binomial convolution for actual scalar-vector products in fixed H⁶. -/
theorem product_wordSobolevNorm_bound (q n : ℕ)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    wordSobolevNorm period 6 n (fun x => f x • g x) ≤
      productConstant period q * leibnizConvolution
        (fun l => wordSobolevNorm period 6 l f) (fun l => wordSobolevNorm period 6 l g) n := by
  induction n generalizing f g with
  | zero =>
    simpa [leibnizConvolution, productConstant, mul_assoc] using
      cylinder_H6_scalar_vector_product period q f g hf hg (fun j _ w => hfL2 j w) (fun j _ w =>
        hgL2 j w)
  | succ n ih =>
    rw [wordSobolevNorm_succ]
    calc
      _ ≤ ∑ i : Fin 4, productConstant period q *
          (leibnizConvolution
            (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) f))
            (fun l => wordSobolevNorm period 6 l g) n +
           leibnizConvolution
            (fun l => wordSobolevNorm period 6 l f)
            (fun l => wordSobolevNorm period 6 l (fieldDerivative period (standardDirection i) g))
              n) := by
        apply Finset.sum_le_sum
        intro i _
        rw [fieldDerivative_smul period _ f g hf hg]
        have hdf := fieldDerivative_smooth period (standardDirection i) f hf
        have hdg := fieldDerivative_smooth period (standardDirection i) g hg
        have hdfL2 := derivative_all_memLp period f hfL2 i
        have hdgL2 := derivative_all_memLp period g hgL2 i
        exact (wordSobolevNorm_add_le period 6 n
          (fun x => fieldDerivative period (standardDirection i) f x • g x)
          (fun x => f x • fieldDerivative period (standardDirection i) g x)
          (fun x => (hdf x).smul (hg x))
          (fun x => (hf x).smul (hdg x))
          (product_all_memLp period q _ g hdf hg hdfL2 hgL2)
          (product_all_memLp period q f _ hf hdg hfL2 hdgL2)).trans
          ((add_le_add (ih _ _ hdf hg hdfL2 hgL2) (ih _ _ hf hdg hfL2 hdgL2)).trans_eq (mul_add
            ..).symm)
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          sum_leibnizConvolution_left, sum_leibnizConvolution_right]
        simp_rw [← wordSobolevNorm_succ]
        rw [leibnizConvolution_succ, add_comm]

end EulerH6Nonlinear
