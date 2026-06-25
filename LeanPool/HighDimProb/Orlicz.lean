/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Moment

/-!
# Orlicz vocabulary

This file records concrete Orlicz and psi-bound names without committing to a
general Orlicz-space or normed-space API.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Orlicz_space
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/--
A concrete Orlicz function on real scalars. Structural assumptions are separate.

Formula reference: Orlicz spaces are defined using a Young/Orlicz function
`Phi`; see https://en.wikipedia.org/wiki/Orlicz_space
-/
abbrev OrliczFunction := ℝ → ℝ

/--
The usual `exp(|x|^p) - 1` model family, with natural exponent for now.

Formula reference: exponential Orlicz functions are standard examples in
Orlicz-space random-variable norms; see
https://en.wikipedia.org/wiki/Orlicz_space
-/
def psiPower (p : ℕ) : OrliczFunction :=
  fun x => Real.exp (|x| ^ p) - 1

/-- The `psi_1` model function with exponential linear growth. -/
def psi1Function : OrliczFunction :=
  fun x => Real.exp |x| - 1

/-- The `psi_2` model function with exponential square growth. -/
def psi2Function : OrliczFunction :=
  fun x => Real.exp (|x| ^ 2) - 1

/--
An Orlicz-type Luxemburg bound at scale `K`.

Formula reference: Luxemburg-type bounds use
`integral Phi(|f|/K) dmu <= 1`; see
https://en.wikipedia.org/wiki/Orlicz_space

This is a predicate-level definition using `lintegral` and `ENNReal.ofReal`.
It is deliberately not a norm definition.
-/
def OrliczBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ψ : OrliczFunction) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    (∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / K)) ∂P) ≤ (1 : ENNReal)

/--
The `psi_2` Orlicz bound at scale `K`, expressed by an exponential-square
nonnegative integral bound.

Formula reference: this specializes the Luxemburg bound to
`Phi(x) = exp(x^2) - 1`; see https://en.wikipedia.org/wiki/Orlicz_space

This is not named subGaussian; equivalence with tail, moment, and MGF forms is
future theorem work.
-/
def Psi2Bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1) ∂P) ≤ (1 : ENNReal)

/--
The `psi_1` Orlicz bound at scale `K`, expressed by an exponential-linear
nonnegative integral bound.

Formula reference: this specializes the Luxemburg bound to
`Phi(x) = exp(x) - 1`; see https://en.wikipedia.org/wiki/Orlicz_space

This is not named subExponential; equivalence with tail, moment, and MGF forms is
future theorem work.
-/
def Psi1Bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K) - 1) ∂P) ≤ (1 : ENNReal)

/-- A real random variable has finite `psi_2` size if some positive scale satisfies `Psi2Bound`. -/
def HasFinitePsi2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  ∃ K : ℝ, Psi2Bound P X K

/-- A real random variable has finite `psi_1` size if some positive scale satisfies `Psi1Bound`. -/
def HasFinitePsi1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  ∃ K : ℝ, Psi1Bound P X K

@[simp]
theorem psiPower_apply (p : ℕ) (x : ℝ) :
    psiPower p x = Real.exp (|x| ^ p) - 1 :=
  rfl

@[simp]
theorem psi1Function_apply (x : ℝ) :
    psi1Function x = Real.exp |x| - 1 :=
  rfl

@[simp]
theorem psi2Function_apply (x : ℝ) :
    psi2Function x = Real.exp (|x| ^ 2) - 1 :=
  rfl

@[simp]
theorem hasFinitePsi2_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    HasFinitePsi2 P X ↔ ∃ K : ℝ, Psi2Bound P X K :=
  Iff.rfl

@[simp]
theorem hasFinitePsi1_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    HasFinitePsi1 P X ↔ ∃ K : ℝ, Psi1Bound P X K :=
  Iff.rfl

end

end HighDimProb
