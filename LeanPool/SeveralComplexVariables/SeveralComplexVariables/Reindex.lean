/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchyIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Derivatives

/-!
# Reindexing finite complex coordinate spaces

Coordinate derivatives commute with renaming coordinates. The polydisc Cauchy formula is
transported along any enumeration of a finite index type; its value is independent of that
enumeration whenever the Cauchy hypotheses hold.

## Main results

`partialDeriv_reindex` and `iteratedPartialDeriv_reindex` transport coordinate derivatives along a
renaming of coordinates. `two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul_reindex` transports
the polydisc Cauchy formula along any enumeration of a finite index type.
-/

public section

open Complex Function MeasureTheory Set
open scoped Real

namespace SeveralComplexVariables

variable {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [Fintype ι] [Fintype κ] in
/-- Renaming coordinates renames a coordinate derivative by the inverse equivalence. -/
theorem partialDeriv_reindex (e : κ ≃ ι) (f : (κ → ℂ) → F) (z : ι → ℂ) (i : ι) :
    partialDeriv i (fun w => f (w ∘ e)) z = partialDeriv (e.symm i) f (z ∘ e) := by
  change deriv (fun w => f (update z i w ∘ e)) (z i) =
    deriv (fun w => f (update (z ∘ e) (e.symm i) w)) ((z ∘ e) (e.symm i))
  simp only [update_comp_equiv, comp_apply, e.apply_symm_apply]

omit [Fintype ι] [Fintype κ] in
/-- All iterated coordinate derivatives are natural under coordinate reindexing. -/
theorem iteratedPartialDeriv_reindex (e : κ ≃ ι) (f : (κ → ℂ) → F) (is : List ι)
    (z : ι → ℂ) :
    iteratedPartialDeriv is (fun w => f (w ∘ e)) z =
      iteratedPartialDeriv (is.map e.symm) f (z ∘ e) := by
  induction is generalizing z with
  | nil => rfl
  | cons i is ih =>
    simp only [iteratedPartialDeriv, List.map_cons]
    rw [show iteratedPartialDeriv is (fun w => f (w ∘ e)) =
      fun w => iteratedPartialDeriv (is.map e.symm) f (w ∘ e) by funext w; exact ih w]
    exact partialDeriv_reindex e _ z i

variable [CompleteSpace F]

omit [Fintype ι] in
/-- Cauchy's polydisc formula for an arbitrary finite index type, integrated using any enumeration
by `Fin n`. No nonemptiness or positive-dimension hypothesis is needed. -/
theorem two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul_reindex {n : ℕ} (e : Fin n ≃ ι)
    {f : (ι → ℂ) → F} {c w : ι → ℂ} {R : ι → ℝ}
    (hR : ∀ i, 0 < R i) (hw : ∀ i, ‖w i - c i‖ < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ((2 * π * I : ℂ) ^ n)⁻¹ • torusIntegral
      (fun z => (∏ i, (z i - w (e i))⁻¹) • f (z ∘ e.symm)) (c ∘ e) (R ∘ e) = f w := by
  have hm : MapsTo (fun z => z ∘ e.symm)
      (closedPolydisc (c ∘ e) (R ∘ e)) (closedPolydisc c R) := by
    intro z hz j hj
    simpa only [comp_apply, e.apply_symm_apply] using hz (e.symm j) (mem_univ _)
  have hc := hfc.comp (continuous_pi (fun j => continuous_apply (e.symm j))).continuousOn hm
  have ha : ∀ z ∈ closedPolydisc (c ∘ e) (R ∘ e), ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x ∘ e.symm)) (z i) := by
    intro z hz i
    simpa only [update_comp_equiv, Equiv.symm_symm, comp_apply, e.symm_apply_apply] using
      hfa (z ∘ e.symm) (hm hz) (e i)
  have hew : (w ∘ e) ∘ e.symm = w := by funext j; simp
  simpa only [comp_apply, hew] using
    two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul (f := fun z => f (z ∘ e.symm))
      (c := c ∘ e) (w := w ∘ e) (R := R ∘ e) (fun i => hR (e i))
      (fun i => hw (e i)) hc ha

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
