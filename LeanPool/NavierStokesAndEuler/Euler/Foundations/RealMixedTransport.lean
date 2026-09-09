/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderGradient

@[expose] public section

noncomputable section

/-! Real scalar and vector forms of the full mixed cylinder commutator estimate. -/

namespace EulerRealMixedTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerMixedCylinderTransport
open EulerRealCylinder EulerVectorCylinder EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of H⁵ norms of the four real coordinate derivatives of a scalar coefficient. -/
noncomputable def realGradientSobolevNorm (b : LiftDomain period → ℝ) : ℝ :=
  ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b)

theorem realGradientSobolevNorm_nonneg (b : LiftDomain period → ℝ) : 0 ≤ realGradientSobolevNorm
  period b :=
  Finset.sum_nonneg (fun _ _ => liftSobolevNorm_nonneg period 5 _)

omit [Fact (0 < period)] in
theorem complexField_fieldDerivative (i : Fin 4) (b : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x)) :
    fieldDerivative period (standardDirection i) (complexField period b) =
      complexField period (fieldDerivative period (standardDirection i) b) :=
  fieldDerivative_postcomp period Complex.ofRealCLM (standardDirection i) b hb

theorem complexField_gradientSobolevNorm (b : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x)) :
    gradientSobolevNorm period (complexField period b) = realGradientSobolevNorm period b := by
  apply Finset.sum_congr rfl
  intro i _
  rw [complexField_fieldDerivative period i b hb,
    complexField_sobolevNorm period 5 _ (fieldDerivative_smooth period _ b hb)]

omit [Fact (0 < period)] in
theorem complexField_mul (f g : LiftDomain period → ℝ) :
    complexField period f * complexField period g = complexField period (f*g) := by
  funext x
  exact (Complex.ofReal_mul _ _).symm

omit [Fact (0 < period)] in
theorem complexField_sub (f g : LiftDomain period → ℝ) :
    complexField period f - complexField period g = complexField period (f-g) := by
  funext x
  exact (Complex.ofReal_sub _ _).symm

omit [Fact (0 < period)] in
theorem complexField_commutator {n : ℕ} (w : Fin n → Fin 4) (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    iteratedFieldDerivative period w (complexField period b * complexField period h) -
      complexField period b * iteratedFieldDerivative period w (complexField period h) =
        complexField period (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative
          period w h) := by
  rw [complexField_mul, complexField_word period w (b*h) (fun x => (hb x).mul (hh x)),
    complexField_word period w h hh, complexField_mul, complexField_sub]

/-- The full real scalar mixed-word transport commutator bound. -/
theorem real_word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure
      period)) :
    (eLpNorm (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) 2
      (liftMeasure period)).toReal ≤
      (12*mixedProductConstant period) * realGradientSobolevNorm period b * liftSobolevNorm period
        5 h := by
  have hbC : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i)
        (complexField period b)))
        2 (liftMeasure period) := by
    intro i r hr v
    rw [complexField_fieldDerivative period i b hb,
      complexField_word period v _ (fieldDerivative_smooth period _ b hb)]
    exact complexField_memLp period _ (hbL2 i r hr v)
  have hhC : ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (complexField period h)) 2 (liftMeasure period) := by
    intro r hr v
    rw [complexField_word period v h hh]
    exact complexField_memLp period _ (hhL2 r hr v)
  have hA := word_transport_commutator_L2 period hn w (complexField period b) (complexField period
    h)
    (complexField_smooth period b hb) (complexField_smooth period h hh) hbC hhC
  rw [complexField_commutator period w b h hb hh, complexField_eLpNorm,
    complexField_gradientSobolevNorm period b hb, complexField_sobolevNorm period 5 h hh] at hA
  exact hA

/-- The corresponding real commutator is in L², not merely assigned an extended seminorm. -/
theorem real_word_commutator_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure
      period)) :
    MemLp (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) 2
      (liftMeasure period) := by
  have hbC : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i)
        (complexField period b)))
        2 (liftMeasure period) := by
    intro i r hr v
    rw [complexField_fieldDerivative period i b hb,
      complexField_word period v _ (fieldDerivative_smooth period _ b hb)]
    exact complexField_memLp period _ (hbL2 i r hr v)
  have hhC : ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (complexField period h)) 2 (liftMeasure period) := by
    intro r hr v
    rw [complexField_word period v h hh]
    exact complexField_memLp period _ (hhL2 r hr v)
  have hA := mixedCommutator_memLp period (List.ofFn w) (by simpa using hn)
    (complexField period b) (complexField period h) (complexField_smooth period b hb)
      (complexField_smooth period h hh) hbC hhC
  simp only [mixedCommutator, listDerivative_ofFn] at hA
  rw [complexField_commutator period w b h hb hh] at hA
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period
      (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) x) :=
    fun x => (iteratedFieldDerivative_smooth period w (b*h) (fun y => (hb y).mul (hh y)) x).sub
      ((hb x).mul (iteratedFieldDerivative_smooth period w h hh x))
  apply hA.of_le (smoothField_continuous period _ hs).aestronglyMeasurable
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

/-- The actual scalar-coefficient commutator acting on a real vector field. -/
noncomputable def vectorCommutator {n : ℕ} (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q) : LiftDomain period → Domain q :=
  iteratedFieldDerivative period w (fun x => b x • h x) -
    (fun x => b x • iteratedFieldDerivative period w h x)

omit [Fact (0 < period)] in
theorem coordinate_vectorCommutator {n : ℕ} (w : Fin n → Fin 4) (q : ℕ) (i : Fin q)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    coordinate q i ∘ vectorCommutator period w q b h =
      iteratedFieldDerivative period w (b*(coordinate q i ∘ h)) -
        b*iteratedFieldDerivative period w (coordinate q i ∘ h) := by
  rw [← coordinate_smul]
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => b y • h y) x) := fun x => (hb
    x).smul (hh x)
  rw [iteratedFieldDerivative_postcomp period (coordinate q i) w (fun x => b x • h x) hs,
    iteratedFieldDerivative_postcomp period (coordinate q i) w h hh]
  funext x
  simp [vectorCommutator, Function.comp_def, map_sub, map_smul, smul_eq_mul]

/-- The full mixed transport commutator for real vector fields on the cylinder. -/
theorem vector_word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure
      period)) :
    (eLpNorm (vectorCommutator period w q b h) 2 (liftMeasure period)).toReal ≤
      ((q : ℝ) * (12*mixedProductConstant period)) * realGradientSobolevNorm period b *
        liftSobolevNorm period 5 h := by
  have hcoords (i : Fin q) : MemLp (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure
    period) := by
    have hA := real_word_commutator_memLp period hn w b (coordinate q i ∘ h) hb (postcomp_smooth
      period _ h hh)
      hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2 v)
    rw [← coordinate_vectorCommutator period w q i b h hb hh] at hA
    exact hA
  have hA := vector_eLpNorm_le_sum_coordinates period q (vectorCommutator period w q b h) hcoords
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => (hcoords i).eLpNorm_ne_top)) hA
  rw [ENNReal.toReal_sum (fun i _ => (hcoords i).eLpNorm_ne_top)] at hB
  have hC (i : Fin q) : (eLpNorm (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure
    period)).toReal ≤
      (12*mixedProductConstant period) * realGradientSobolevNorm period b * liftSobolevNorm period
        5 h := by
    change (eLpNorm (coordinate q i ∘ vectorCommutator period w q b h) 2 (liftMeasure
      period)).toReal ≤ _
    rw [coordinate_vectorCommutator period w q i b h hb hh]
    have hbound := real_word_transport_commutator_L2 period hn w b (coordinate q i ∘ h) hb
      (postcomp_smooth period _ h hh) hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2
        v)
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 5 _ (coordinate_norm_le q i) h hh hhL2)
      (mul_nonneg (mul_nonneg (by norm_num) (mixedProductConstant_nonneg period))
        (realGradientSobolevNorm_nonneg period b)))
  have hD := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hC i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hD
  have he (q C A B : ℝ) : q*(C*A*B)=(q*C)*A*B := by ring
  exact hB.trans (hD.trans_eq (he _ _ _ _))

/-- The full real vector transport commutator belongs to L² under the same derivative hypotheses. -/
theorem vector_word_commutator_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2
        (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure
      period)) :
    MemLp (vectorCommutator period w q b h) 2 (liftMeasure period) := by
  have hcoords (i : Fin q) : MemLp (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure
    period) := by
    have hA := real_word_commutator_memLp period hn w b (coordinate q i ∘ h) hb (postcomp_smooth
      period _ h hh)
      hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2 v)
    rw [← coordinate_vectorCommutator period w q i b h hb hh] at hA
    exact hA
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (vectorCommutator period w q b h) x) := by
    intro x
    exact (iteratedFieldDerivative_smooth period w (fun y => b y • h y) (fun y => (hb y).smul (hh
      y)) x).sub
      ((hb x).smul (iteratedFieldDerivative_smooth period w h hh x))
  refine ⟨(smoothField_continuous period _ hs).aestronglyMeasurable, ?_⟩
  exact (vector_eLpNorm_le_sum_coordinates period q _ hcoords).trans_lt
    (ENNReal.sum_lt_top.2 (fun i _ => (hcoords i).eLpNorm_lt_top))

end EulerRealMixedTransport
