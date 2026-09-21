/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace

/-!
# Transporting Davis--Kahan hypotheses across real complexification

The real half of standing assumption 1 of Davis--Kahan 1970 ("real or complex")
is reached by complexifying: state the real configuration, push it to
`RealComplexification E`, apply the proved complex theorem, and pull the
conclusion back.  The geometry (`subspaceGap_complexifySubmodule`,
`isAcute_complexifySubmodule_iff`, `isQuarterAcute_complexifySubmodule_iff`) and
the norms (`SymmetricNormingFunction.gauge_complexify`) already transport.  What
was missing is the *hypothesis* side: the quadratic-form gaps and the
invariance/off-diagonality conditions that every Davis--Kahan theorem assumes.

This module supplies that layer.  There is no perturbation theory here.  The only
input is that the complexification is the orthogonal direct sum of two copies of
`E`, so that

* `‖z‖² = ‖re z‖² + ‖im z‖²` (`norm_sq`), and
* `Re ⟪z, w⟫_ℂ = ⟪re z, re w⟫_ℝ + ⟪im z, im w⟫_ℝ` (`inner_apply`),

and that a complexified operator acts coordinatewise (`re_complexify`,
`im_complexify`, both `rfl`).  A real form bound therefore transports by applying
it to `re z` and to `im z` and adding, and a real invariance condition transports
coordinatewise.

The bounds are *exactly* preserved -- no constant is lost -- which matters,
because these feed the ordered-gap hypotheses of the quarter-angle and
double-angle theorems, where a lossy transport would not close the gap.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

open scoped InnerProductSpace
open TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form of a complexified operator is the sum of the real
quadratic forms on the two coordinates. -/
theorem re_inner_complexify (A : E →L[ℝ] E) (z : RealComplexification E) :
    RCLike.re ⟪complexify A z, z⟫_ℂ =
      ⟪A (re z), re z⟫_ℝ + ⟪A (im z), im z⟫_ℝ :=
  rfl

/-- A real upper form bound on a subspace transports to the complexification with
the same constant. -/
theorem re_inner_le_of_mem_complexifySubmodule
    {A : E →L[ℝ] E} {U : Submodule ℝ E} {a : ℝ}
    (h : ∀ x ∈ U, ⟪A x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule U) :
    RCLike.re ⟪complexify A z, z⟫_ℂ ≤ a * ‖z‖ ^ 2 := by
  rw [mem_complexifySubmodule] at hz
  rw [re_inner_complexify, norm_sq]
  calc ⟪A (re z), re z⟫_ℝ + ⟪A (im z), im z⟫_ℝ
      ≤ a * ‖re z‖ ^ 2 + a * ‖im z‖ ^ 2 := add_le_add (h _ hz.1) (h _ hz.2)
    _ = a * (‖re z‖ ^ 2 + ‖im z‖ ^ 2) := by ring

/-- A real lower form bound on a subspace transports to the complexification with
the same constant. -/
theorem le_re_inner_of_mem_complexifySubmodule
    {A : E →L[ℝ] E} {U : Submodule ℝ E} {b : ℝ}
    (h : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule U) :
    b * ‖z‖ ^ 2 ≤ RCLike.re ⟪complexify A z, z⟫_ℂ := by
  rw [mem_complexifySubmodule] at hz
  rw [re_inner_complexify, norm_sq]
  calc b * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
      = b * ‖re z‖ ^ 2 + b * ‖im z‖ ^ 2 := by ring
    _ ≤ ⟪A (re z), re z⟫_ℝ + ⟪A (im z), im z⟫_ℝ :=
        add_le_add (h _ hz.1) (h _ hz.2)

/-- A real "maps `U` into `V`" condition transports coordinatewise. -/
theorem mapsTo_complexifySubmodule
    {A : E →L[ℝ] E} {U V : Submodule ℝ E} (h : ∀ x ∈ U, A x ∈ V)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule U) :
    complexify A z ∈ complexifySubmodule V := by
  rw [mem_complexifySubmodule] at hz ⊢
  exact ⟨h _ hz.1, h _ hz.2⟩

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

omit [U.HasOrthogonalProjection] in
/-- Off-diagonality transports: if a real operator carries `U` into `Uᗮ`, its
complexification carries `complexifySubmodule U` into the orthogonal complement
of `complexifySubmodule U`. -/
theorem mapsTo_orthogonal_complexifySubmodule
    {A : E →L[ℝ] E} (h : ∀ x ∈ U, A x ∈ Uᗮ)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule U) :
    complexify A z ∈ (complexifySubmodule U)ᗮ := by
  rw [← complexifySubmodule_orthogonal]
  exact mapsTo_complexifySubmodule h hz

omit [U.HasOrthogonalProjection] in
/-- The companion of `mapsTo_orthogonal_complexifySubmodule` on the complement:
if a real operator carries `Uᗮ` into `U`, its complexification carries the
orthogonal complement of `complexifySubmodule U` into `complexifySubmodule U`. -/
theorem mapsTo_of_mem_orthogonal_complexifySubmodule
    {A : E →L[ℝ] E} (h : ∀ x ∈ Uᗮ, A x ∈ U)
    {z : RealComplexification E} (hz : z ∈ (complexifySubmodule U)ᗮ) :
    complexify A z ∈ complexifySubmodule U := by
  rw [← complexifySubmodule_orthogonal] at hz
  exact mapsTo_complexifySubmodule h hz

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
