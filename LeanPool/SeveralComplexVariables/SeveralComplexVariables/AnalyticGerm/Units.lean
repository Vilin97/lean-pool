/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm

/-!
# Roots of unit germs

Every scalar analytic unit germ has an analytic root of each positive integral degree. We
normalize the value to one before using Mathlib's analytic complex power function; no global
choice of logarithm on the domain is required. These elementary local facts are used, for
example, when absorbing units into irreducible factorizations.

## Main results

`exists_isUnit_pow_eq` produces an analytic unit root of each positive integral degree.
`exists_analyticAt_pow_eq` is the corresponding statement for representatives.
-/

public noncomputable section

open Filter
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

/-- A nonvanishing analytic function has a local analytic root of every positive degree. -/
theorem exists_analyticAt_pow_eq {f : E → ℂ} (hf : AnalyticAt ℂ f x)
    (hx : f x ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g x ∧ (fun y => g y ^ n) =ᶠ[𝓝 x] f := by
  let g : E → ℂ := fun y => (f x ^ ((n : ℂ)⁻¹)) * ((f y / f x) ^ ((n : ℂ)⁻¹))
  refine ⟨g, ?_, .of_forall fun y => ?_⟩
  · apply AnalyticAt.mul analyticAt_const
    apply hf.div_const.cpow analyticAt_const
    simp [hx]
  · dsimp [g]
    rw [mul_pow, Complex.cpow_nat_inv_pow _ hn, Complex.cpow_nat_inv_pow _ hn]
    exact mul_div_cancel₀ _ hx

/-- Every unit germ has an `n`-th root which is itself a unit, for `n ≠ 0`. -/
theorem exists_isUnit_pow_eq (u : AnalyticGerm ℂ x) (hu : IsUnit u)
    {n : ℕ} (hn : n ≠ 0) : ∃ v : AnalyticGerm ℂ x, IsUnit v ∧ v ^ n = u := by
  obtain ⟨f, hf, rfl⟩ := exists_rep u
  obtain ⟨g, hg, he⟩ := exists_analyticAt_pow_eq hf ((isUnit_iff _).mp hu) hn
  have hp : ofAnalyticAt g hg ^ n = ofAnalyticAt f hf := by
    apply Subtype.ext
    exact Germ.coe_eq.mpr he
  refine ⟨ofAnalyticAt g hg, ?_, hp⟩
  apply (isUnit_iff _).mpr
  intro hz
  have hval := congrArg (eval x) hp
  have hnonzero := (isUnit_iff _).mp hu
  rw [map_pow, hz, zero_pow hn] at hval
  exact hnonzero hval.symm

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
