/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle

/-! # Double Angle Gap Bound -/

open TauCeti.DavisKahanExt

/-!
# The double-angle sine dominates the directed gap on the close branch

The `sin 2Θ` theorem bounds `‖sin 2Θ‖` from *above*.  A bootstrap that recovers
the gap from a double-angle bound needs the reverse comparison, and this module
supplies it: away from the quarter turn,

`‖sin 2Θ(U, V)‖ ≥ √2 · directedGap V U`   whenever `directedGap V U ≤ √2 / 2`.

The pointwise mechanism is `‖sin 2Θ‖ ≥ 2 cos Θ · sin Θ`: the directed sine maps
into the source subspace, where the directed cosine is coercive with constant
`√(1 - g²)`, so `‖cos Θ (sin Θ x)‖ ≥ √(1 - g²) ‖sin Θ x‖`; taking the supremum
over `x` turns `‖sin Θ‖ = g` into the bound.  The closed quarter branch
`g ≤ √2 / 2` is exactly where `√(1 - g²) ≥ √2 / 2`.

The module is the only place the two spellings of the double-angle sine meet:
the `Geometry/Angle` operator `sin 2Θ_C` and the `InfiniteDimensional`
operator `sin 2Θ = 2 P_{Uᗮ} P_V P_U`, which have the same norm with the roles
of the two subspaces exchanged.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan

universe u

/-! ## 1. Two scalar facts about `√2 / 2` -/

/-- The quarter-turn threshold squares to one half. -/
theorem sqrt_two_div_two_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The quarter-turn threshold is positive. -/
theorem sqrt_two_div_two_pos : (0 : ℝ) < Real.sqrt 2 / 2 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- On the closed quarter branch the cosine is at least `√2 / 2`. -/
theorem sqrt_two_div_two_le_sqrt_one_sub_sq {g : ℝ} (hg : g ≤ Real.sqrt 2 / 2)
    (hg0 : 0 ≤ g) : Real.sqrt 2 / 2 ≤ Real.sqrt (1 - g ^ 2) := by
  have hsq : (Real.sqrt 2 / 2) ^ 2 ≤ 1 - g ^ 2 := by
    rw [sqrt_two_div_two_sq]
    nlinarith [sqrt_two_div_two_sq, sq_nonneg g]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq sqrt_two_div_two_pos.le] at h

/-! ## 2. The `sin 2Θ` lower bound on the close branch

The `sin 2Θ` theorem bounds `‖sin 2Θ‖` from above; the bootstrap needs the
reverse comparison with the gap.  Away from the quarter turn,
`‖sin 2Θ‖ ≥ 2 cos Θ · sin Θ` pointwise on the source subspace, and the
existing acute coercivity of the directed cosine supplies `cos Θ`. -/

section Bridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The directed sine lands in the source subspace, for *every* vector: it
kills the orthogonal complement and preserves the source. -/
theorem directedSinAngleOperatorC_apply_mem_source (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    directedSinAngleOperatorC U V x ∈ U := by
  have hsplit : x = U.starProjection x + Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal_apply]; abel
  rw [hsplit, map_add,
    directedSinAngleOperatorC_apply_eq_zero_of_mem_orthogonal U V
      (Uᗮ.starProjection_apply_mem x), add_zero]
  exact directedSinAngleOperatorC_apply_mem U V (U.starProjection_apply_mem x)

/-- **The double-angle sine dominates `2 cos Θ sin Θ`.**

`‖sin 2Θ(U,V)‖ ≥ 2 √(1 - directedGap²) · directedGap`.  Pointwise: the
directed sine maps into `U`, where the directed cosine is coercive with
constant `√(1 - directedGap²)`, so `‖cos Θ (sin Θ x)‖ ≥ √(1-g²) ‖sin Θ x‖`;
taking the supremum over `x` turns `‖sin Θ‖ = g` into the claim. -/
theorem two_mul_sqrt_mul_directedGap_le_norm_directedSinTwoAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    2 * Real.sqrt (1 - U.directedProjectionGap V ^ 2) * U.directedProjectionGap V ≤
      ‖directedSinTwoAngleOperatorC U V‖ := by
  set g : ℝ := U.directedProjectionGap V with hgdef
  set c0 : ℝ := Real.sqrt (1 - g ^ 2) with hc0
  set S : E →L[ℂ] E := directedSinAngleOperatorC U V with hS
  set C : E →L[ℂ] E := directedCosAngleOperatorC U V with hC
  have hSnorm : ‖S‖ = g := norm_directedSinAngleOperatorC U V
  have hc0nonneg : 0 ≤ c0 := Real.sqrt_nonneg _
  have hM : ‖directedSinTwoAngleOperatorC U V‖ = 2 * ‖C * S‖ := by
    have hcomm : Commute S C :=
      commute_directedSinAngleOperatorC_directedCosAngleOperatorC U V
    rw [directedSinTwoAngleOperatorC, norm_smul, hcomm.eq]
    norm_num
  rcases eq_or_lt_of_le hc0nonneg with h0 | hpos
  · rw [← h0]
    simp only [mul_zero, zero_mul]
    positivity
  · have hpt : ∀ x : E, c0 * ‖S x‖ ≤ ‖(C * S) x‖ := fun x =>
      norm_directedCosAngleOperatorC_apply_ge U V
        (directedSinAngleOperatorC_apply_mem_source U V x)
    have hSle : ‖S‖ ≤ ‖C * S‖ / c0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      have h1 := hpt x
      have h2 : ‖(C * S) x‖ ≤ ‖C * S‖ * ‖x‖ := (C * S).le_opNorm x
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [norm_nonneg (S x), norm_nonneg x]
    rw [hM, hSnorm] at *
    rw [le_div_iff₀ hpos] at hSle
    nlinarith [hSle]

/-- The two spellings of the double-angle sine agree in norm, with the roles
of the two subspaces exchanged: the `DoubleAngle` operator
`sin 2Θ(U,V) = 2 P_{Uᗮ} P_V P_U` has the norm of the `Geometry` operator
`sin 2Θ_C(V,U)`. -/
theorem norm_sinTwoAngleOperator_eq_norm_directedSinTwoAngleOperatorC_swap
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperator U V‖ = ‖directedSinTwoAngleOperatorC V U‖ := by
  rw [norm_directedSinTwoAngleOperatorC V U, sinTwoAngleOperator, norm_smul]
  norm_num

/-- **The bootstrap comparison.**  On the closed quarter branch the
double-angle sine dominates `√2` times the directed gap. -/
theorem sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hclose : V.directedProjectionGap U ≤ Real.sqrt 2 / 2) :
    Real.sqrt 2 * V.directedProjectionGap U ≤ ‖sinTwoAngleOperator U V‖ := by
  have hg0 : 0 ≤ V.directedProjectionGap U := norm_nonneg _
  have hcos := sqrt_two_div_two_le_sqrt_one_sub_sq hclose hg0
  calc Real.sqrt 2 * V.directedProjectionGap U
      = 2 * (Real.sqrt 2 / 2) * V.directedProjectionGap U := by ring
    _ ≤ 2 * Real.sqrt (1 - V.directedProjectionGap U ^ 2) * V.directedProjectionGap U := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        nlinarith [hcos, hg0]
    _ ≤ ‖directedSinTwoAngleOperatorC V U‖ :=
        two_mul_sqrt_mul_directedGap_le_norm_directedSinTwoAngleOperatorC V U
    _ = ‖sinTwoAngleOperator U V‖ :=
        (norm_sinTwoAngleOperator_eq_norm_directedSinTwoAngleOperatorC_swap U V).symm

end Bridge

end DavisKahan.Angle
end TauCeti
