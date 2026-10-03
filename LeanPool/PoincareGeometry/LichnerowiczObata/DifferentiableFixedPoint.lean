/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Differentiable dependence of a parameterized fixed point

This analytic step is intended for the Picard equation on a Banach space of
paths. It does not assume differentiability of the selected fixed points.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The linearized fixed-point equation is invertible when its state
derivative has norm less than one. -/
theorem isInvertible_id_sub_of_norm_lt_one {B : F →L[ℝ] F} (hB : ‖B‖ < 1) :
    (ContinuousLinearMap.id ℝ F - B).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hB
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ F u, ?_⟩
  ext z
  change (ContinuousLinearEquiv.unitsEquiv ℝ F u) z = _
  rw [ContinuousLinearEquiv.unitsEquiv_apply, hu]
  rfl

/-- A continuous selection of fixed points is strictly differentiable when
the joint fixed-point operator is strictly differentiable and its state
derivative is a contraction. The derivative solves the linearized equation. -/
theorem hasStrictFDerivAt_fixedPoint
    {T : E × F → F} {φ : E → F} {x : E}
    {A : E →L[ℝ] F} {B : F →L[ℝ] F}
    (hT : HasStrictFDerivAt T (A.coprod B) (x, φ x)) (hB : ‖B‖ < 1)
    (hφ : ContinuousAt φ x) (hfix : ∀ᶠ y in 𝓝 x, T (y, φ y) = φ y) :
    HasStrictFDerivAt φ ((ContinuousLinearMap.id ℝ F - B).inverse ∘L A) x := by
  let G : E × F → F := fun z => z.2 - T z
  let D : E × F →L[ℝ] F := ContinuousLinearMap.snd ℝ E F - A.coprod B
  have hG : HasStrictFDerivAt G D (x, φ x) := hasStrictFDerivAt_snd.sub hT
  have hD₂ : D ∘L ContinuousLinearMap.inr ℝ E F = ContinuousLinearMap.id ℝ F - B := by
    ext z
    simp [D]
  have hD₁ : D ∘L ContinuousLinearMap.inl ℝ E F = -A := by
    ext z
    simp [D]
  have hinv : (D ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hD₂]
    exact isInvertible_id_sub_of_norm_lt_one hB
  let ψ := hG.implicitFunctionOfProdDomain hinv
  have he : ψ =ᶠ[𝓝 x] φ := by
    have ht : Tendsto (fun y => (y, φ y)) (𝓝 x) (𝓝 (x, φ x)) :=
      continuousAt_id.prodMk hφ
    have hlocal := ht (hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv)
    filter_upwards [hlocal, hfix] with y hy hfy
    apply hy.mp
    simp only [G, hfy, hfix.self_of_nhds, sub_self]
  have hψ := hG.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  rw [hD₂, hD₁] at hψ
  have hd : -(ContinuousLinearMap.id ℝ F - B).inverse ∘L (-A) =
      (ContinuousLinearMap.id ℝ F - B).inverse ∘L A := by
    ext z
    simp
  rw [hd] at hψ
  exact hψ.congr_of_eventuallyEq he

/-- Higher smoothness also transfers from the fixed-point operator to any
continuous local solution, without assuming that solution is differentiable. -/
theorem contDiffAt_fixedPoint {n : ℕ∞ω} (hn : n ≠ 0)
    {T : E × F → F} {φ : E → F} {x : E}
    {A : E →L[ℝ] F} {B : F →L[ℝ] F}
    (hTc : ContDiffAt ℝ n T (x, φ x))
    (hT : HasStrictFDerivAt T (A.coprod B) (x, φ x)) (hB : ‖B‖ < 1)
    (hφ : ContinuousAt φ x) (hfix : ∀ᶠ y in 𝓝 x, T (y, φ y) = φ y) :
    ContDiffAt ℝ n φ x := by
  let G : E × F → F := fun z => z.2 - T z
  let D : E × F →L[ℝ] F := ContinuousLinearMap.snd ℝ E F - A.coprod B
  have hG : HasStrictFDerivAt G D (x, φ x) := hasStrictFDerivAt_snd.sub hT
  have hGc : ContDiffAt ℝ n G (x, φ x) := contDiffAt_snd.sub hTc
  have hinv : (fderiv ℝ G (x, φ x) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hG.hasFDerivAt.fderiv]
    have he : D ∘L ContinuousLinearMap.inr ℝ E F = ContinuousLinearMap.id ℝ F - B := by
      ext z
      simp [D]
    rw [he]
    exact isInvertible_id_sub_of_norm_lt_one hB
  let ψ := hGc.implicitFunction hn hinv
  have he : ψ =ᶠ[𝓝 x] φ := by
    have ht : Tendsto (fun y => (y, φ y)) (𝓝 x) (𝓝 (x, φ x)) :=
      continuousAt_id.prodMk hφ
    have hlocal := ht (hGc.eventually_apply_eq_iff_implicitFunction hn hinv)
    filter_upwards [hlocal, hfix] with y hy hfy
    apply hy.mp
    simp only [G, hfy, hfix.self_of_nhds, sub_self]
  exact (hGc.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq he.symm

end LichnerowiczObata
