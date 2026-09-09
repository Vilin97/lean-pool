/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientProduct

@[expose] public section

/-! Physical spatial dilation preserves continuity of every actual L²
jet. The proof uses its explicit bounded action on differences. -/

noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open Set Filter MeasureTheory EulerSmoothLimit EulerPhysicalL2Scaling
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def subField (A B : SmoothL2Field V) : SmoothL2Field V where
  field := A.field-B.field
  smooth := A.smooth.sub B.smooth
  integrable n := ((A.integrable n).sub (B.integrable n)).ae_eq
    (Eventually.of_forall (fun x => (iteratedFDeriv_sub_apply (i := n) (x := x)
      (A.smooth.contDiffAt.of_le (by simp)) (B.smooth.contDiffAt.of_le (by simp))).symm))

@[simp] theorem subField_apply (A B : SmoothL2Field V) (x : Space) :
    (subField A B).field x=A.field x-B.field x := rfl

theorem jetLp_subField (A B : SmoothL2Field V) (n : ℕ) :
    (subField A B).jetLp n=A.jetLp n-B.jetLp n := by
  apply Lp.ext
  filter_upwards [(subField A B).jetLp_ae n,A.jetLp_ae n,B.jetLp_ae n,
    Lp.coeFn_sub (A.jetLp n) (B.jetLp n)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄,Pi.sub_apply,h₂,h₃]
  exact iteratedFDeriv_sub_apply (A.smooth.contDiffAt.of_le (by simp))
    (B.smooth.contDiffAt.of_le (by simp))

theorem norm_jetLp_scale_sub_le (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (A B : SmoothL2Field V) (n : ℕ) :
    ‖(scaleField ell hell A).jetLp n-(scaleField ell hell B).jetLp n‖ ≤
      (ell⁻¹)^n*‖A.jetLp n-B.jetLp n‖ := by
  rw [← jetLp_subField,← jetLp_subField]
  have he : (subField (scaleField ell hell A) (scaleField ell hell B)).field =
      (scaleField ell hell (subField A B)).field := by
    funext x
    simp only [subField_apply,scaleField_apply,smul_sub]
  rw [EulerLpSmoothCoefficientProduct.jetLp_congr _ _ he]
  exact norm_jetLp_scale_le ell hell hell1 (subField A B) n

theorem continuous_jetLp_scaleField {K : Type*} [TopologicalSpace K]
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (scaleField ell hell (A t)).jetLp n) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => norm_jetLp_scale_sub_le ell hell hell1 (A s) (A t) n)
  have hc : Continuous (fun s => (ell⁻¹)^n*‖(A s).jetLp n-(A t).jetLp n‖) :=
    continuous_const.mul (((hA n).sub continuous_const).norm)
  simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto t

end EulerLpTranslation.SmoothL2Field
