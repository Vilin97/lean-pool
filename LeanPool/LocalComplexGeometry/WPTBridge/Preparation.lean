/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.Regularization
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Main

/-!
# Regularized Weierstrass preparation for holomorphic germs

This module joins the Taylor-line regularization theorem to the pinned classical
Weierstrass preparation theorem.  It records the coordinate pullback as an
equality of raw function germs, so downstream commutative-algebra arguments do
not depend on a hidden choice of representative.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry.WPTBridge

open ClassicalComplexWPT

noncomputable section

/-- A representative of a nonzero holomorphic germ is not locally zero. -/
theorem representative_not_eventually_zero {n : ℕ}
    {f : HolomorphicGerm n} (hf : f ≠ 0)
    {F : ComplexEuclidean n → ℂ}
    (hrep : (F : FunctionGerm n) = (f : FunctionGerm n)) :
    ¬ F =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  intro hzero
  apply hf
  apply Subtype.ext
  change (f : FunctionGerm n) = 0
  rw [← hrep, ← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr hzero

/-- Evaluation of an analytic representative agrees with evaluation of its germ. -/
theorem representative_value_eq_evalAtOrigin {n : ℕ}
    {f : HolomorphicGerm n} {F : ComplexEuclidean n → ℂ}
    (hrep : (F : FunctionGerm n) = (f : FunctionGerm n)) :
    F 0 = evalAtOrigin f := by
  have h := congrArg Filter.Germ.value hrep
  change F 0 = Filter.Germ.value (f : FunctionGerm n)
  simpa using h

/--
Regularized preparation of a nonzero holomorphic germ.

`H` is written in WPT's product coordinates.  Composing it with the standard
successor-coordinate splitting represents exactly the coordinate pullback of
the original germ.  The equality `H 0 = evalAtOrigin f` makes the positive-order
corollary independent of representatives.
-/
theorem exists_regularized_weierstrassPreparation
    {n : ℕ} {f : HolomorphicGerm (n + 1)} (hf_ne : f ≠ 0) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
      (d : ℕ) (H : Ambient n → ℂ)
      (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      AnalyticAt ℂ H 0 ∧
      ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
          FunctionGerm (n + 1)) =
        (coordinatePullback L f : FunctionGerm (n + 1)) ∧
      H 0 = evalAtOrigin f ∧
      ExactOrderInLastVariable H d ∧
      IsWeierstrassPreparation H d a u := by
  obtain ⟨F, hF, hrep⟩ := HolomorphicGerm.exists_rep f
  have hF_ne : ¬ F =ᶠ[𝓝 0] (fun _ ↦ 0) :=
    representative_not_eventually_zero hf_ne hrep
  obtain ⟨L, d, horder⟩ := exists_regularizing_coordinateEquiv hF hF_ne
  let H : Ambient n → ℂ := fun x ↦ F (L ((wptAmbientEquiv n).symm x))
  have hH : AnalyticAt ℂ H 0 := by
    let A := L.toContinuousLinearMap.comp
      (wptAmbientEquiv n).symm.toContinuousLinearMap
    have hFA : AnalyticAt ℂ F (A 0) := by rw [map_zero]; exact hF
    have hcomp := hFA.compContinuousLinearMap (u := A) (x := 0)
    change AnalyticAt ℂ (F ∘ A) 0
    exact hcomp
  obtain ⟨a, u, hprep, hunique⟩ :=
    classicalComplexWeierstrassPreparation n d H hH horder
  refine ⟨L, d, H, a, u, hH, ?_, ?_, horder, hprep⟩
  · change ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
        FunctionGerm (n + 1)) =
      functionGermPullbackHom L (f : FunctionGerm (n + 1))
    rw [← hrep]
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro x
    exact congrArg (fun y ↦ F (L y)) ((wptAmbientEquiv n).symm_apply_apply x)
  · calc
      H 0 = F (L ((wptAmbientEquiv n).symm 0)) := rfl
      _ = F (L 0) := by rw [map_zero]
      _ = F 0 := by rw [map_zero]
      _ = evalAtOrigin f := representative_value_eq_evalAtOrigin hrep

/--
For a nonzero germ vanishing at the origin, the regularized prepared polynomial
has positive degree.
-/
theorem exists_regularized_weierstrassPreparation_pos
    {n : ℕ} {f : HolomorphicGerm (n + 1)}
    (hf_ne : f ≠ 0) (hf_zero : evalAtOrigin f = 0) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
      (d : ℕ) (H : Ambient n → ℂ)
      (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      0 < d ∧
      AnalyticAt ℂ H 0 ∧
      ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
          FunctionGerm (n + 1)) =
        (coordinatePullback L f : FunctionGerm (n + 1)) ∧
      H 0 = 0 ∧
      ExactOrderInLastVariable H d ∧
      IsWeierstrassPreparation H d a u := by
  obtain ⟨L, d, H, a, u, hH, hrep, hH0, horder, hprep⟩ :=
    exists_regularized_weierstrassPreparation hf_ne
  have hd : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    have hne : H 0 ≠ 0 := exactOrderInLastVariable_zero_iff.mp horder
    exact hne (hH0.trans hf_zero)
  exact ⟨L, d, H, a, u, hd, hH, hrep, hH0.trans hf_zero, horder, hprep⟩

end

end LocalComplexGeometry.WPTBridge
