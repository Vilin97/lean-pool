/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import LeanPool.LeanModularForms.ForMathlib.QExpansion
import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps
import LeanPool.LeanModularForms.ForMathlib.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace ModularFormClass

variable [ModularFormClass F Γ(1) k]

private theorem cuspFunction_eqOn_const_of_nonpos_wt (hk : k ≤ 0) (f : F) :
    Set.EqOn (cuspFunction 1 f) (const ℂ (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  refine eq_const_of_exists_le (fun q hq ↦ ?_) (exp_nonneg (-π)) ?_ (fun q hq ↦ ?_)
  · have hCusp : IsCusp OnePoint.infty (Γ(1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) := by
      rw [Gamma_one_top, ← MonoidHom.range_eq_map]
      exact Fact.out
    have key := (differentiableAt_cuspFunction' (h := 1) f
      (dvd_of_eq <| Subgroup.Gamma_width 1) hCusp (mem_ball_zero_iff.mp hq))
    -- the local `cuspFunction` takes `h : ℕ`, the outer goal expects `cuspFunction (1 : ℝ)`;
    -- they coincide once the `↑(1 : ℕ) = (1 : ℝ)` coercion is normalised
    simpa using key.differentiableWithinAt
  · simp only [exp_lt_one_iff, Left.neg_neg_iff, pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · have hpos : 0 < (invQParam 1 q).im :=
        im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'
      obtain ⟨ξ, hξ, hξ₂⟩ :=
        haveI : SlashInvariantFormClass F (Matrix.SpecialLinearGroup.mapGL ℝ).range k := by
          rw [← Gamma_one_coe_eq_SL]; infer_instance
        exists_one_half_le_im_and_norm_le hk f ⟨_, hpos⟩
      refine ⟨_, norm_qParam_le_of_one_half_le_im hξ, ?_⟩
      have e1 : cuspFunction 1 f q = f ⟨invQParam 1 q, hpos⟩ := by
        rw [← eq_cuspFunction' (Γ := Γ(1)) (τ := ⟨invQParam 1 q, hpos⟩) f
          (dvd_of_eq <| Subgroup.Gamma_width 1)]
        simp [Nat.cast_one, qParam_right_inv one_ne_zero hq']
      have e2 : cuspFunction 1 f (𝕢 1 ↑ξ) = f ξ := by
        have := eq_cuspFunction' (Γ := Γ(1)) (τ := ξ) f (dvd_of_eq <| Subgroup.Gamma_width 1)
        simpa [Nat.cast_one] using this
      rw [e1, e2]; exact hξ₂

private theorem levelOne_nonpos_wt_const (hk : k ≤ 0) (f : F) :
    ⇑f = Function.const _ (cuspFunction 1 f 0) := funext fun z ↦ by
  have hQ : 𝕢 1 z ∈ Metric.ball 0 1 := by simpa using (norm_qParam_lt_iff zero_lt_one 0 _).mpr z.2
  simpa [← eq_cuspFunction' f (dvd_of_eq <| Subgroup.Gamma_width 1)] using
    cuspFunction_eqOn_const_of_nonpos_wt hk f hQ


end ModularFormClass
