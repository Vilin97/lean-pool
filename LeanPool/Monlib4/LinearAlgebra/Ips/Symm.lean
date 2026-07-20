/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!

# some obvious lemmas on self-adjoint operators

This file provides the polarization identity for self adjoint continuous linear maps
  over `is_R_or_C`.

-/


variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y

namespace ContinuousLinearMap
namespace IsSelfAdjoint

/-- Given a self-adjoint continuous linear operator $T$ on $E$, we get
  $\langle T x, x \rangle = 0$ for any $x\in E$ if and only if $T=0$. -/
theorem inner_map_self_eq_zero [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    (∀ x, ⟪T x,x⟫ = 0) ↔ T = 0 := by
  rw [isSelfAdjoint_iff_isSymmetric] at hT
  simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← LinearMap.ext_iff,
    ContinuousLinearMap.toLinearMap_zero]
  exact hT.inner_map_self_eq_zero

open RCLike

/-- The polarization identity for self-adjoint operators. -/
theorem inner_map_polarization [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (x y : E) :
    ⟪T x,y⟫ =
      (⟪T (x + y),x + y⟫ - ⟪T (x - y),x - y⟫ - I * ⟪T (x + (I : 𝕜) • y),x + (I : 𝕜) • y⟫ +
          I * ⟪T (x - (I : 𝕜) • y),x - (I : 𝕜) • y⟫) /
        4 := by
  rw [← ContinuousLinearMap.coe_coe,
    LinearMap.IsSymmetric.inner_map_polarization (IsSelfAdjoint.isSymmetric hT)]


end IsSelfAdjoint
end ContinuousLinearMap
