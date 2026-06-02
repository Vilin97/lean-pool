/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanPool.LeanModularForms.ForMathlib.Identities
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# q-expansions of modular forms (project-local extensions)

The bulk of the original `ForMathlib/QExpansion.lean` file has been upstreamed into
`Mathlib.NumberTheory.ModularForms.QExpansion` and
`Mathlib.Analysis.Complex.CauchyIntegral`.  This file now only keeps the project-local
variants that are parameterised by `Γ.width ∣ h` rather than `h ∈ Γ.strictPeriods`, which
the rest of the project still uses.
-/

open scoped Real NNReal MatrixGroups CongruenceSubgroup

noncomputable section

open ModularForm Complex Filter Function

open UpperHalfPlane hiding I

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {h : ℕ} (f : F)
  (τ : ℍ) {z q : ℂ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace SlashInvariantFormClass

variable [hF : SlashInvariantFormClass F Γ k]
include hF

theorem periodic_comp_ofComplex' (hΓ : Γ.width ∣ h) : Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + h) := by simp only [add_im, natCast_im, add_zero, hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw,
      ← vAdd_width_periodic f k (Nat.cast_dvd_cast hΓ) ⟨w, hw⟩]
    congr 1
    simp [UpperHalfPlane.ext_iff, add_comm]
  · have : im (w + h) ≤ 0 := by simpa only [add_im, natCast_im, add_zero, not_lt] using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

theorem eq_cuspFunction' {τ : ℍ} [NeZero h] (hΓ : Γ.width ∣ h) :
    cuspFunction h f (𝕢 h τ) = f τ := by
  simpa [UpperHalfPlane.cuspFunction] using
    (periodic_comp_ofComplex' f hΓ).eq_cuspFunction (NeZero.ne _) τ

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

variable [hF : ModularFormClass F Γ k]
include hF

/-- Differentiability of `⇑f ∘ ofComplex` at a point with positive imaginary part, recovering the
former `ModularFormClass.differentiableAt_comp_ofComplex` from the manifold-differentiability of a
modular form. -/
theorem differentiableAt_comp_ofComplex {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (⇑f ∘ ↑ofComplex) z :=
  UpperHalfPlane.mdifferentiableAt_iff.mp (holo f ⟨z, hz⟩)

variable [NeZero h] (hΓ : Γ.width ∣ h)
include hΓ

theorem differentiableAt_cuspFunction'
    (hc : IsCusp OnePoint.infty (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)))
    (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  have npos : 0 < (h : ℝ) := mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _))
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex' f hΓ).differentiableAt_cuspFunction_zero npos
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      ((OnePoint.isBoundedAt_infty_iff.mp (ModularFormClass.bdd_at_cusps f hc)).comp_tendsto
        tendsto_comap_im_ofComplex)
  · exact Periodic.qParam_right_inv npos.ne' hq' ▸
      (periodic_comp_ofComplex' f hΓ).differentiableAt_cuspFunction npos.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one npos hq hq'

end ModularFormClass

open ModularFormClass

namespace UpperHalfPlane.IsZeroAtImInfty

variable {f}

lemma zeroAtFilter_comp_ofComplex {α : Type*} [Zero α] [TopologicalSpace α] {f : ℍ → α}
    (hf : IsZeroAtImInfty f) : ZeroAtFilter I∞ (f ∘ ofComplex) :=
  hf.comp tendsto_comap_im_ofComplex

/-- A modular form which vanishes at the cusp `∞` actually must decay at least as fast as
`Real.exp (-2 * π * τ.im / n)`, if `n` divides the cusp with.

(Note that `Γ` need not be finite index here). -/
theorem exp_decay_atImInfty_of_width_dvd [ModularFormClass F Γ k]
    (hf : IsZeroAtImInfty f) (hΓ : Γ.width ∣ h) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  rcases eq_or_ne h 0 with rfl | hΓ'
  · simp only [Nat.cast_zero, div_zero, Real.exp_zero]
    exact hf.isBoundedAtImInfty
  · haveI : NeZero h := ⟨hΓ'⟩
    simpa [comp_def] using
      ((periodic_comp_ofComplex' f hΓ).exp_decay_of_zero_at_inf
        (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
        (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
          fun _ ↦ differentiableAt_comp_ofComplex f)
        (hf.zeroAtFilter_comp_ofComplex)).comp_tendsto tendsto_coe_atImInfty

end UpperHalfPlane.IsZeroAtImInfty

namespace ModularFormClass

/-- Recovers the former `ModularFormClass.hasFPowerSeries_cuspFunction`: the `q`-expansion of a
modular form is an `FPowerSeries` representing its `cuspFunction`, derived from the modular-form
instance (analyticity at `0` plus the `q`-expansion `HasSum`). -/
theorem hasFPowerSeries_cuspFunction {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} (f : F) [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction h f)
      (UpperHalfPlane.qExpansionFormalMultilinearSeries h f) 0 1 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.hasFPowerSeries_cuspFunction f hh
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (UpperHalfPlane.hasSum_qExpansion hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f))

end ModularFormClass
