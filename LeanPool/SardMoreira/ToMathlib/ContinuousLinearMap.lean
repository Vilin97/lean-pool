/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# Auxiliary theorems about `ContinuousLinearMap`

Mostly about `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse`.
-/

open Filter Function Asymptotics Topology

namespace ContinuousLinearMap

namespace IsInvertible

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} {l : Filter α}

/-- If a family of continuous linear maps converges to an invertible continuous linear map,
then the maps are eventually invertible as well. -/
protected theorem eventually [CompleteSpace E]
    {f₀ : E →L[𝕜] F} {f : α → E →L[𝕜] F} (hf₀ : f₀.IsInvertible) (hf : Tendsto f l (𝓝 f₀)) :
    ∀ᶠ x in l, (f x).IsInvertible :=
  hf.eventually <| ContinuousLinearEquiv.isOpen.mem_nhds hf₀

end IsInvertible

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} {l : Filter α}

/-- Consider two families of continuous linear maps, `f a` and `g a`.

Suppose that both of them are eventually invertible along a filter `l`,
and the norms of their inverses are bounded.
Then $$f^{-1}_a - g^{-1}_a = O(f_a - g_a)$$. -/
theorem isBigO_inverse_sub_inverse
    {l : Filter α} {f g : α → E →L[𝕜] F}
    (hf_inv : ∀ᶠ a in l, (f a).IsInvertible)
    (hf_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(f a).inverse‖))
    (hg_inv : ∀ᶠ a in l, (g a).IsInvertible)
    (hg_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(g a).inverse‖)) :
    (fun a ↦ (f a).inverse - (g a).inverse) =O[l] (fun a ↦ f a - g a) := calc
  _ =ᶠ[l] fun a ↦ (f a).inverse ∘L (g a - f a) ∘L (g a).inverse := by
    filter_upwards [hf_inv, hg_inv] with a hfa hga
    simp [hfa, hga, ← comp_assoc]
  _ =O[l] fun a ↦ ‖(f a).inverse‖ * ‖g a - f a‖ * ‖(g a).inverse‖ := .of_norm_le fun a ↦ by
    grw [opNorm_comp_le, opNorm_comp_le, mul_assoc]
  _ =O[l] (fun a ↦ f a - g a) := by
    simpa [norm_sub_rev] using (hf_bdd.isBigO_one ℝ).norm_left.mul
      (isBigO_refl (fun a ↦ ‖g a - f a‖) _) |>.mul (hg_bdd.isBigO_one ℝ).norm_left

theorem apply_sub_apply_isBigO {α 𝕜 𝕝 E F G : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕝]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕝 F]
    [NormedAddCommGroup G]
    {σ : 𝕜 →+* 𝕝} [RingHomIsometric σ]
    {f₁ f₂ : α → E →SL[σ] F} {g₁ g₂ : α → E} {B : α → G} {l : Filter α}
    (hf_bdd : l.IsBoundedUnder (· ≤ ·) (‖f₁ ·‖))
    (hf_sub : (fun a ↦ f₁ a - f₂ a) =O[l] B)
    (hg_bdd : l.IsBoundedUnder (· ≤ ·) (‖g₂ ·‖))
    (hg_sub : (fun a ↦ g₁ a - g₂ a) =O[l] B) :
    (fun a ↦ f₁ a (g₁ a) - f₂ a (g₂ a)) =O[l] B := calc
  _ = (fun a ↦ (f₁ a (g₁ a) - f₁ a (g₂ a)) + (f₁ a (g₂ a) - f₂ a (g₂ a))) := by simp
  _ =O[l] B := by
    refine .add ?_ ?_
    · simp only [← map_sub]
      refine .trans (.of_norm_le fun _ ↦ le_opNorm _ _) ?_
      simpa using hf_bdd.isBigO_one ℝ |>.norm_left |>.mul hg_sub.norm_norm
    · simp only [← sub_apply]
      refine .trans (.of_norm_le fun _ ↦ le_opNorm _ _) ?_
      simpa using hf_sub.norm_norm.mul (hg_bdd.isBigO_one ℝ).norm_left

end ContinuousLinearMap
