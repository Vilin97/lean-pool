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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedEulerAlgebra

@[expose] public section

noncomputable section

namespace EulerWeightedPressure

open Finset EulerPacketWeights EulerWeightedConvolution EulerGevrey

theorem lower_triangle_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - (l + 1))) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - (p.2 + 1))
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - (l + 1) = n' - (l' + 1) := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - (p.2 + 1)) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      sum_le_sum_of_injOn e hinj himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (ha p.1) (hb p.2))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem geometric_lower_triangle (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (N : ℕ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, q ^ (l + 1) * b (n - (l + 1))) ≤
      (2 * q) * ∑ j ∈ range (N + 1), b j := by
  let a : ℕ → ℝ := fun n => if n = 0 then 0 else q ^ n
  have ha : ∀ n, 0 ≤ a n := fun n => by dsimp [a]; split <;> positivity
  have h := lower_triangle_sum_le_product N a b ha hb
  have hsum : (∑ l ∈ range (N + 1), a l) ≤ 2 * q := by
    rw [sum_range_succ']
    simpa [a] using geometric_tail_le_two_mul q hq hhalf N
  simp only [a, Nat.add_one_ne_zero, ↓reduceIte] at h
  exact h.trans (mul_le_mul_of_nonneg_right hsum (sum_nonneg (fun j _ => hb j)))

theorem shifted_weight_kernel (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (j l : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) *
      (Rc ^ l * (l.factorial : ℝ) ^ 2) * Z ≤
    (ρ * Rc) ^ l * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * Z) := by
  have h := shifted_source_term ρ hρ j l (Rc ^ l * (l.factorial : ℝ) ^ 2) Z
    (by positivity) hZ
  have hw : weight ρ l * (Rc ^ l * (l.factorial : ℝ) ^ 2) = (ρ * Rc) ^ l := by
    unfold weight
    rw [mul_pow]
    field_simp [factorial_cast_ne_zero]
  simpa only [hw] using h

/-- A shifted Gevrey inverse estimate whose constant is independent of truncation.
The positive-order coefficient terms are absorbed, rather than accumulated with order. -/
theorem shifted_weighted_inverse (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hM : 1 ≤ M) (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (N : ℕ) (A F Z : ℕ → ℝ) (_hF : ∀ n, 0 ≤ F n) (hZ : ∀ n, 0 ≤ Z n)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hrec : ∀ n ≤ N, Z n ≤ M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)))) :
    (∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * Z n) ≤
      2 * M * ∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * F n := by
  let v : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1)
  have hv : ∀ n, 0 ≤ v n := fun n => mul_nonneg (Nat.cast_nonneg _) (weight_pos hρ _).le
  have hq : 0 ≤ ρ * Rc := mul_nonneg hρ.le hRc
  have hhalf : ρ * Rc ≤ 1 / 2 := by nlinarith
  have hcomm : (∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) ≤
      (2 * (ρ * Rc)) * ∑ j ∈ range (N + 1), v j * Z j := by
    calc
      _ = ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          v n * (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)) := by
        simp only [mul_sum, mul_assoc]
      _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          (ρ * Rc) ^ (l + 1) * (v (n - (l + 1)) * Z (n - (l + 1))) := by
        apply sum_le_sum
        intro n hn
        apply sum_le_sum
        intro l hl
        have hln := mem_range.mp hl
        have hnN : n ≤ N := by have := mem_range.mp hn; omega
        have hcoeff := hA (l + 1) (by omega) (by omega)
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff
            (mul_nonneg (hv n) (Nat.cast_nonneg (n.choose (l + 1))))) (hZ (n - (l + 1)))
        have h2 := shifted_weight_kernel ρ Rc hρ hRc (n - (l + 1)) (l + 1)
          (Z (n - (l + 1))) (hZ _)
        have he : n - (l + 1) + (l + 1) = n := by omega
        dsimp [v] at h1 ⊢
        exact h1.trans (by simpa only [he] using h2)
      _ ≤ _ := geometric_lower_triangle (ρ * Rc) hq hhalf N
        (fun j => v j * Z j) (fun j => mul_nonneg (hv j) (hZ j))
  have hs := sum_le_sum (s := range (N + 1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (hrec n (by have := mem_range.mp hn; omega)) (hv n))
  have hsumid : (∑ n ∈ range (N + 1), v n * (M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))))) =
      M * ((∑ n ∈ range (N + 1), v n * F n) +
        ∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
          (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) := by
    simp only [mul_add, sum_add_distrib, mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hsumid] at hs
  have hzsum : 0 ≤ ∑ n ∈ range (N + 1), v n * Z n :=
    sum_nonneg (fun n _ => mul_nonneg (hv n) (hZ n))
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hzsum
  have hcomm' := mul_le_mul_of_nonneg_left hcomm (show 0 ≤ M by linarith)
  change (∑ n ∈ range (N + 1), v n * Z n) ≤ 2 * M * ∑ n ∈ range (N + 1), v n * F n
  nlinarith

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds

/-- The shifted weighted operator bound for the pressure actually constructed in L². -/
theorem pressure_shifted_weighted_bound (period : ℝ) [Fact (0 < period)]
    {directions : Fin 4 → LiftTangent} {s : ℕ}
    {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A.coefficient x v) v)
    (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l) :
    (∑ n ∈ range (s + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) *
      levelNorm period (J.solvePressure K κ m c hc hpos) n) ≤
      2 * M * ∑ n ∈ range (s + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) *
        levelNorm period J n := by
  let P := J.solvePressure K κ m c hc hpos
  apply shifted_weighted_inverse ρ Rc M hρ hRc hM hsmall s
    (boundLevel period K) (levelNorm period J) (levelNorm period P)
    (fun _ => levelNorm_nonneg J) (fun _ => levelNorm_nonneg P)
  · intro l hl hs
    simpa only [majorant, Nat.add_zero] using hcoeff l hl hs
  · intro n hn
    apply (pressure_level_recurrence K J κ m c hc hpos hn).trans
    apply mul_le_mul_of_nonneg_right hcM
    apply add_nonneg (levelNorm_nonneg J)
    apply sum_nonneg
    intro l _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (boundLevel_nonneg K)) (levelNorm_nonneg P)

end EulerWeightedPressure
