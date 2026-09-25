/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigma
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiSigma
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.WeakOrlicz

/-! # Tails -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Public Chapter 4 weak-tail notation

This file re-exports the already-developed independent-sums tail vocabulary
under the `Book.Ch04` namespace.
-/

noncomputable section

open MeasureTheory

/-- The weak-Orlicz upper-tail relation `X ≤ O_Psi(A)`. -/
abbrev IsBigOWith {Ω : Type*} [MeasurableSpace Ω] :=
  IndependentSums.IsBigOWith (Ω := Ω)

/-- The upper-tail event `{X > a}` used by the weak-tail notation. -/
abbrev upperTailEvent {Ω : Type*} : (Ω → ℝ) → ℝ → Set Ω :=
  IndependentSums.upperTailEvent

/-- The absolute upper-tail event `{|X| > a}`. -/
abbrev absTailEvent {Ω : Type*} : (Ω → ℝ) → ℝ → Set Ω :=
  IndependentSums.absTailEvent

/-- The symmetric weak-Orlicz relation `X = O_Psi(A)`. -/
abbrev IsBigO {Ω : Type*} [MeasurableSpace Ω] :=
  IndependentSums.IsBigO (Ω := Ω)

/-- Admissible weak-tail functions. -/
abbrev AdmissiblePsi :=
  IndependentSums.AdmissiblePsi

/-- The Chapter 4 growth hypothesis `t Psi(t) ≤ Psi(K t)` for `t ≥ 1`. -/
abbrev HasPsiGrowth :=
  IndependentSums.HasPsiGrowth

/-- The abstract doubling package used in the finite-family weak-tail triangle
inequality. -/
abbrev HasPsiAbstractDoubling :=
  IndependentSums.HasPsiAbstractDoubling

/-- The stretched-exponential model class `Gamma_sigma`. -/
noncomputable abbrev gammaSigma (σ : ℝ) : ℝ → ℝ :=
  IndependentSums.gammaSigma σ

/-- The log-normal model class `Psi_sigma`. -/
noncomputable abbrev psiSigma (σ : ℝ) : ℝ → ℝ :=
  IndependentSums.psiSigma σ

/-- Witness-level `p^(1/sigma)` moment growth for the stretched-exponential
class. -/
abbrev HasGammaMomentGrowthWith {Ω : Type*} [MeasurableSpace Ω] :=
  IndependentSums.HasGammaMomentGrowthWith (Ω := Ω)

/-- Existential `p^(1/sigma)` moment growth for the stretched-exponential
class. -/
abbrev HasGammaMomentGrowth {Ω : Type*} [MeasurableSpace Ω] :=
  IndependentSums.HasGammaMomentGrowth (Ω := Ω)

end

end Ch04
end Book
end Homogenization
