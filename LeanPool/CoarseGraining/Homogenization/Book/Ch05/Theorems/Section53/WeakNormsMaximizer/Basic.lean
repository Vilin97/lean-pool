/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.Common

/-! # Basic -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Basic definitions for the weak-norm maximizer lemma

Named right-hand-side terms for manuscript Lemma
`l.weak.norms.maximizer.homogenization.scale`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The high-scale averaged-gradient term in the weak-norm maximizer estimate. -/
noncomputable def gradientAverageTermAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (s : ℝ) (p q p0 : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  ∑ n ∈ Finset.Icc (k + 1) m,
    Real.rpow (3 : ℝ) (-s * (Int.toNat (m - n) : ℝ)) *
      Real.sqrt
        (descendantsAverage Q (Int.toNat (m - n))
          (fun R =>
            vecNormSq
              (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)))

/-- The high-scale averaged-flux term in the weak-norm maximizer estimate. -/
noncomputable def fluxAverageTermAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (t : ℝ) (p q q0 : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  ∑ n ∈ Finset.Icc (k + 1) m,
    Real.rpow (3 : ℝ) (-t * (Int.toNat (m - n) : ℝ)) *
      Real.sqrt
        (descendantsAverage Q (Int.toNat (m - n))
          (fun R =>
            vecNormSq
              (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)))

/-- The parent-child response defect at a child scale. -/
noncomputable def responseDefectAverageAtScale {d : ℕ}
    (m n : ℤ) (p q : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  descendantsAverage Q (Int.toNat (m - n))
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) -
    Ch04.restrictionResponseJObservableCubeSet Q p q a

/-- The high-scale gradient mismatch term controlled by the lower ellipticity
quantity on the parent cube.  The dimensional constant is inserted by the final
RHS. -/
noncomputable def gradientMismatchTermAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (s s' : ℝ) (p q : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹) *
    ∑ n ∈ Finset.Icc (k + 1) m,
      Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) *
        Real.sqrt (responseDefectAverageAtScale m n p q a)

/-- The high-scale flux mismatch term controlled by the upper ellipticity
quantity on the parent cube.  The dimensional constant is inserted by the final
RHS. -/
noncomputable def fluxMismatchTermAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (t t' : ℝ) (p q : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a) *
    ∑ n ∈ Finset.Icc (k + 1) m,
      Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - n) : ℝ)) *
        Real.sqrt (responseDefectAverageAtScale m n p q a)

/-- The low-scale gradient tail in the weak-norm maximizer estimate. -/
noncomputable def gradientLowScaleTailAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (s s' : ℝ) (p q : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  (s - s')⁻¹ *
    Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) *
      Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)

/-- The low-scale flux tail in the weak-norm maximizer estimate. -/
noncomputable def fluxLowScaleTailAtScale {d : ℕ} [NeZero d]
    (m k : ℤ) (t t' : ℝ) (p q : Vec d) (a : RegCoeffField d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  (t - t')⁻¹ *
    Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - k) : ℝ)) *
      Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)

/-- The affine-gradient constant tail in the gradient weak-norm estimate. -/
noncomputable def gradientConstantTailAtScale {d : ℕ}
    (m k : ℤ) (s : ℝ) (p0 : Vec d) : ℝ :=
  s⁻¹ * Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ)) * ‖p0‖

/-- The affine-flux constant tail in the flux weak-norm estimate. -/
noncomputable def fluxConstantTailAtScale {d : ℕ}
    (m k : ℤ) (t : ℝ) (q0 : Vec d) : ℝ :=
  t⁻¹ * Real.rpow (3 : ℝ) (-t * (Int.toNat (m - k) : ℝ)) * ‖q0‖

/-- Manuscript right-hand side for the gradient estimate in
`l.weak.norms.maximizer.homogenization.scale`. -/
noncomputable def gradientRHSAtScale {d : ℕ} [NeZero d]
    (C : ℝ) (m k : ℤ) (s s' : ℝ)
    (p q p0 : Vec d) (a : RegCoeffField d) : ℝ :=
  gradientAverageTermAtScale m k s p q p0 a +
    C * gradientMismatchTermAtScale m k s s' p q a +
      C * gradientLowScaleTailAtScale m k s s' p q a +
        C * gradientConstantTailAtScale m k s p0

/-- Manuscript right-hand side for the flux estimate in
`l.weak.norms.maximizer.homogenization.scale`. -/
noncomputable def fluxRHSAtScale {d : ℕ} [NeZero d]
    (C : ℝ) (m k : ℤ) (t t' : ℝ)
    (p q q0 : Vec d) (a : RegCoeffField d) : ℝ :=
  fluxAverageTermAtScale m k t p q q0 a +
    C * fluxMismatchTermAtScale m k t t' p q a +
      C * fluxLowScaleTailAtScale m k t t' p q a +
        C * fluxConstantTailAtScale m k t q0

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
