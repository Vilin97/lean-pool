/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The nonvanishing consequence of Darboux asymptotics

In §§93 and 99 of Volume I, Chapter VI, Poincaré uses Darboux's method to obtain asymptotic
formulas for high-order coefficients.  The nonintegrability argument needs the consequence that
sufficiently high coefficients do not vanish.

This file verifies that consequence abstractly.  It also treats the leading model occurring in
Poincaré's §102 formula, an exponential factor times a nonzero inverse-power coefficient.  It does
not yet derive the asymptotic equivalence from complex singularities; that is the difficult
analytic content of §§93 and 95--101.
-/

noncomputable section

open Filter
open Asymptotics
open scoped Topology

namespace LeanPool.PoincareThreeBody

/-- If the ratio of a coefficient sequence to a model tends to one, then the coefficients are
eventually nonzero.  No separate nonvanishing hypothesis on the model is needed for this
direction. -/
theorem eventually_ne_zero_of_tendsto_div_one
    {ι : Type*} {filter : Filter ι} {coefficient model : ι → ℂ}
    (hasymptotic : Tendsto (coefficient / model) filter (𝓝 1)) :
    ∀ᶠ index in filter, coefficient index ≠ 0 := by
  have hratio : ∀ᶠ index in filter, (coefficient / model) index ≠ 0 :=
    hasymptotic.eventually_ne one_ne_zero
  filter_upwards [hratio] with index hindex
  intro hcoefficient
  apply hindex
  simp [hcoefficient]

/-- The leading Darboux model used here: exponential growth or decay multiplied by a nonzero
coefficient and one inverse power of the index.  The shift by one makes the sequence defined at
index zero without changing its large-index form. -/
def chapterVILeadingDarbouxModel (singularityInverse leadingCoefficient : ℂ)
    (index : ℕ) : ℂ :=
  singularityInverse ^ index * leadingCoefficient / (index + 1)

/-- Poincaré's leading Darboux model is nonzero at every index when its singularity and leading
coefficient are nonzero. -/
theorem chapterVILeadingDarbouxModel_ne_zero
    {singularityInverse leadingCoefficient : ℂ}
    (hsingularity : singularityInverse ≠ 0)
    (hleading : leadingCoefficient ≠ 0) (index : ℕ) :
    chapterVILeadingDarbouxModel singularityInverse leadingCoefficient index ≠ 0 := by
  unfold chapterVILeadingDarbouxModel
  have hindex : (index : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero index
  exact div_ne_zero (mul_ne_zero (pow_ne_zero index hsingularity) hleading) hindex

/-- A Darboux asymptotic equivalence to a nonzero leading model forces all sufficiently
high-order coefficients to be nonzero.  This formalizes the logical passage from the asymptotic
formula in §§99 and 102 to the coefficient nonvanishing used by the obstruction argument. -/
theorem eventually_coefficient_ne_zero_of_chapterVI_darboux_asymptotic
    {coefficient : ℕ → ℂ} {singularityInverse leadingCoefficient : ℂ}
    (hsingularity : singularityInverse ≠ 0)
    (hleading : leadingCoefficient ≠ 0)
    (hasymptotic : coefficient ~[atTop]
      chapterVILeadingDarbouxModel singularityInverse leadingCoefficient) :
    ∀ᶠ index in atTop, coefficient index ≠ 0 := by
  rcases (Asymptotics.isEquivalent_iff_exists_eq_mul
      (u := coefficient)
      (v := chapterVILeadingDarbouxModel singularityInverse leadingCoefficient)
      (l := atTop)).mp hasymptotic with ⟨ratio, hratio, hequality⟩
  have hratioNonzero : ∀ᶠ index in atTop, ratio index ≠ 0 :=
    hratio.eventually_ne one_ne_zero
  have hmodel : ∀ᶠ index in atTop,
      chapterVILeadingDarbouxModel singularityInverse leadingCoefficient index ≠ 0 :=
    Eventually.of_forall
      (chapterVILeadingDarbouxModel_ne_zero hsingularity hleading)
  filter_upwards [hratioNonzero, hmodel, hequality] with index hratioIndex hmodelIndex hequal
  rw [hequal]
  exact mul_ne_zero hratioIndex hmodelIndex

end LeanPool.PoincareThreeBody
