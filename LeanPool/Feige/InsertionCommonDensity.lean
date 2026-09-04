/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.FiniteSignedExp

/-!
# Common densities on insertion edges

For a Boolean state, every unchanged low coordinate contributes a positive
scaled exponential and every unchanged high coordinate contributes a
negative scaled exponential.  This file packages those factors and applies
the finite-convolution TP2 theorem to the common part of any genuine edge.
-/

namespace Feige
namespace LikelihoodRatio

noncomputable section

/-- The signed exponential contributed by coordinate `i` in state `S`. -/
def stateFactor {ι : Type*} [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) : SignedExpFactor :=
  if i ∈ S then
    { direction := .negative
      scale := β i
      scale_pos := hβ i }
  else
    { direction := .positive
      scale := γ i
      scale_pos := hγ i }

/--
All signed exponential factors shared by the two endpoints of the edge
which changes `changed`.
-/
def commonFactors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : List SignedExpFactor :=
  (Finset.univ.erase changed).toList.map
    (stateFactor γ β hγ hβ S)

/-- Every genuine insertion-edge common density satisfies the exact
four-point hypothesis consumed by the likelihood-ratio proof. -/
theorem fourPointLogConcave_commonFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    FourPointLogConcave
      (finiteSignedExpSumDensity
        (commonFactors γ β hγ hβ S changed)) :=
  fourPointLogConcave_finiteSignedExpSumDensity _

/-- Translation-TP2 form of the same insertion-edge conclusion. -/
theorem translationTP2_commonFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    TranslationTP2
      (finiteSignedExpSumDensity
        (commonFactors γ β hγ hβ S changed)) :=
  translationTP2_finiteSignedExpSumDensity _

end
end LikelihoodRatio
end Feige
