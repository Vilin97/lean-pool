/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.BilateralShiftExample
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Proposition32 -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Proposition 3.2 and its Remark

Proposition 3.2 is the nonacute existence criterion: a direct rotation of the
pair `(U, V)` exists exactly when the two crossed intersections `U ⊓ Vᗮ` and
`Uᗮ ⊓ V` have the same dimension -- printed as (3.5) and rendered here in the
cardinal-free form `CrossedDefectsEquivalent`, a linear isometric equivalence
of the two spaces.  The proposition's second printed sentence is that such a
rotation is never unique in the nonacute case, and its proof records in passing
that every paper direct rotation squares to `-1` on each crossed defect.

The Remark printed after the proposition supplies the example separating (1.5)
from (3.5): on the two-sided square-summable sequences the bilateral shift is a
unitary satisfying (1.4), so the shift-related half-spaces have equal ambient
dimension data, yet one crossed intersection is a line and the other is zero,
so (3.5) fails and the pair admits no direct rotation whatever.

The mathematics is owned upstream.  `Geometry/Polar/Section3Nonacute.lean`
carries the nonacute construction and its injective parameterization,
`Geometry/Halmos/CrossedDefectGap.lean` the crossed-defect bookkeeping, and
`Geometry/Halmos/BilateralShiftExample.lean` the shift pair; this module states
the paper's sentences against them.

Everything is stated over an arbitrary `RCLike` field.  Nothing in the nonacute
construction is complex-specific: the crossed-defect quarter turn is built out
of the polar factor of `Q P + Qᗮ Pᗮ`, and the only field-dependent ingredient
is the continuous functional calculus that the modulus runs on, carried as a
hypothesis exactly as `ForTauCeti`'s modulus API carries it.  Typeclass
inference discharges it at `𝕜 = ℂ` and, through
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, at
`𝕜 = ℝ`, so the real-scalar section at the end is inhabited rather than vacuous.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970


open TauCeti.DavisKahan

universe u

section NonacuteExistence

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]
/-! The real functional calculus on `H →L[𝕜] H`, and the two scalar-action facts Mathlib
pairs it with, are theorems at every `RCLike` field
(`ContinuousLinearMap.continuousFunctionalCalculusReal`), so they are activated here rather
than quantified over.  Until 2026-09-04 they were section `variable`s, and every theorem in
this section therefore asked its caller for three instances that instance search finds.  They
are `local instance 100` rather than global because a global `Algebra ℝ (E →L[𝕜] E)` makes
Lean's `•` elaborator drop an author-written `((r : ℝ) : 𝕜) •` coercion. -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal


/-- **Davis--Kahan 1970, Proposition 3.2.**

A nonacute direct rotation exists exactly when the crossed defect spaces have
equal Hilbert dimension, expressed constructively by a linear isometric
equivalence. -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent :
    (∃ T : H →L[𝕜] H, IsDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  TauCeti.DavisKahan.proposition3_2_completed U V

/-- **Davis--Kahan 1970, Proposition 3.2, the explicit parameterization of the
freedom.**

Distinct unitaries between the crossed defect spaces must produce distinct
direct rotations. -/
theorem proposition3_2_parameterized_nonuniqueness
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) →
          (H →L[𝕜] H),
      (∀ J, IsDirectRotation U V (build J)) ∧
      Function.Injective build :=
  TauCeti.DavisKahan.proposition3_2_parameterization_completed U V hdefect

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence: "It is not
unique."**

In the nonacute case a direct rotation, once it exists, is never unique.  The
witnesses are produced by feeding an isometry `J` of the crossed defect spaces
and its negation `-J` through the injective parameterization
`proposition3_2_parameterized_nonuniqueness`.  Over a field of characteristic
zero `J ≠ -J` requires a nonzero defect space, and that is supplied by the
nonacute hypothesis rather than assumed separately: the paper's acute case is
precisely the vanishing of both crossed intersections.

This is the paper's own reason for the nonuniqueness -- "This extension is not
unique (even if `dim Null(C₀) = 1`), and the nonuniqueness will survive" -- with
the arbitrary unitary extension replaced by the single sign change, which is
enough to refute uniqueness. -/
theorem proposition3_2_not_unique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ∃ T₁ T₂ : H →L[𝕜] H,
      IsDirectRotation U V T₁ ∧ IsDirectRotation U V T₂ ∧ T₁ ≠ T₂ := by
  obtain ⟨build, hbuild, hinj⟩ :=
    proposition3_2_parameterized_nonuniqueness U V hdefect
  obtain ⟨J⟩ := hdefect
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.ne_bot_iff _ |>.mp
      (halmosSourceDefect_ne_bot_of_not_isAcute U V ⟨J⟩ hnonacute)
  refine ⟨build J, build (J.trans (LinearIsometryEquiv.neg 𝕜)), hbuild _, hbuild _, ?_⟩
  intro hEq
  have hJJ : J = J.trans (LinearIsometryEquiv.neg 𝕜) := hinj hEq
  have hval : J ⟨x, hxmem⟩ = -J ⟨x, hxmem⟩ :=
    congrArg (fun e : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V =>
      e ⟨x, hxmem⟩) hJJ
  have hsrc : (⟨x, hxmem⟩ : halmosSourceDefect U V) = -⟨x, hxmem⟩ := by
    refine J.injective ?_
    rw [map_neg]
    exact hval
  have htwo : (2 : 𝕜) • (⟨x, hxmem⟩ : halmosSourceDefect U V) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hsrc
  rcases smul_eq_zero.mp htwo with h2 | hx0
  · exact absurd h2 two_ne_zero
  · exact hxne (congrArg Subtype.val hx0)

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form.** -/
theorem proposition3_2_not_existsUnique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ¬ ∃! T : H →L[𝕜] H, IsDirectRotation U V T := by
  rintro ⟨T, _, huniq⟩
  obtain ⟨T₁, T₂, h₁, h₂, hne⟩ := proposition3_2_not_unique U V hdefect hnonacute
  exact hne ((huniq T₁ h₁).trans (huniq T₂ h₂).symm)

/-- **Davis--Kahan 1970, Proposition 3.2, crossing-space property.**

The proof of the proposition records a property of every direct rotation on the
two crossed defect spaces: applying the rotation twice gives minus the original
vector.  No acuteness or finite-dimensional hypothesis is added. -/
theorem proposition3_2_crossing_square_minus_one
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) :
    (∀ x : halmosSourceDefect U V, T (T (x : H)) = -(x : H)) ∧
      (∀ y : halmosTargetDefect U V, T (T (y : H)) = -(y : H)) := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · exact TauCeti.DavisKahan.directRotation_sq_apply_sourceDefect U V T hT x.property
  · exact TauCeti.DavisKahan.directRotation_sq_apply_targetDefect U V T hT y.property

end NonacuteExistence

/-! ## The Remark after Proposition 3.2

Davis--Kahan attach a Remark to Proposition 3.2 whose only job is to show that
the standing dimension hypothesis (1.5) does **not** imply the crossed defect
hypothesis (3.5).  The witness is a pair of shift-related half-space subspaces
of the two-sided square-summable sequences:

* `H` is the space of square-summable sequences `(…, a₋₁, a₀, a₁, …)`;
* `P H` is the subspace of those with `aₙ = 0` for `n < 0`;
* `Q H` is the subspace of those with `aₙ = 0` for `n ≤ 0`.

Then (1.5) holds -- the bilateral shift is a unitary carrying `P H` onto `Q H`,
so it satisfies (1.4), and (1.5) follows -- while `P H ∩ Qtilde H` is the line of
sequences supported at `n = 0` and `Ptilde H ∩ Q H` is zero, so (3.5) fails.  By
Proposition 3.2 the pair therefore admits no direct rotation at all.

The Hilbert space is presented as an arbitrary Hilbert space over an `RCLike`
field carrying a Hilbert basis indexed by `ℤ`; that is the same object as the
sequence space of the Remark, and it is how the paper's coordinates
`aₙ = ⟪bₙ, x⟫` are named in `Geometry/Halmos/BilateralShiftExample.lean`, where
the pair and its computations live.
-/

section Remark

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal


/-- **Davis--Kahan 1970, the Remark after Proposition 3.2.**

For the shift pair on the two-sided square-summable sequences, the bilateral
shift is a unitary satisfying (1.4), hence (1.5) holds; but the two crossed
intersections are a line and zero, so (3.5) fails, and by Proposition 3.2 the
pair admits no direct rotation whatever.

This is the source's own separation of (1.5) from (3.5). -/
theorem remark3_2_bilateralShift_separates_dimensionHypotheses
    (b : HilbertBasis ℤ 𝕜 H) :
    (bilateralShiftL b ∈ unitary (H →L[𝕜] H) ∧
        bilateralShiftL b * Submodule.starProjection (coordinateHalfSpace b 0) =
          Submodule.starProjection (coordinateHalfSpace b 1) * bilateralShiftL b) ∧
      (Nonempty (coordinateHalfSpace b 0 ≃ₗᵢ[𝕜] coordinateHalfSpace b 1) ∧
        Nonempty ((coordinateHalfSpace b 0)ᗮ ≃ₗᵢ[𝕜]
          (coordinateHalfSpace b 1)ᗮ)) ∧
      halmosSourceDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) ≠ ⊥ ∧
      halmosTargetDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) = ⊥ ∧
      ¬ ∃ T : H →L[𝕜] H,
        IsDirectRotation (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) T := by
  refine ⟨⟨bilateralShiftL_mem_unitary b, ?_⟩, ?_,
    halmosSourceDefect_coordinateHalfSpace_ne_bot b,
    halmosTargetDefect_coordinateHalfSpace b, ?_⟩
  · have h := bilateralShiftL_intertwines b 0
    rwa [zero_add] at h
  · have h := coordinateHalfSpace_dimensions_agree b 0
    rwa [zero_add] at h
  · intro h
    exact not_crossedDefectsEquivalent_coordinateHalfSpace b
      ((proposition3_2_exists_iff_crossedDefectsEquivalent _ _).mp h)

end Remark

/-! ## Proposition 3.2 and its Remark over a real Hilbert space

Standing assumption 1 of Davis--Kahan 1970 admits real Hilbert spaces.  The
statements below are the `𝕜 = ℝ` instances of the generic theorems above, each
grounded by `:=` on the generic theorem and each carrying exactly the generic
theorem's hypotheses.  In particular the real forms assume no finite dimension,
no separability and no compactness, and they do **not** add a nondegeneracy
hypothesis on the crossed defects: `¬ TauCeti.IsAcute U V` already forces one of
them to be nonzero, by `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`.

They are *not* obtained by descending the complex theorem.  That route is
refuted -- transporting the forward direction produces an isometry of the
complexified defect spaces, and nothing recovers a real one from it -- so the
whole polar and direct-rotation stack under `DavisKahan/Geometry/Polar/` was
made `RCLike`-generic instead, which is what these instances read off.

Over `ℝ` the ambient space of the Remark is the two-sided real square-summable
sequences, presented, as over `ℂ`, as any real Hilbert space carrying a
`HilbertBasis ℤ ℝ`.
-/

section RealScalars

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.2, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_exists_iff_crossedDefectsEquivalent`: a
direct rotation of the pair exists exactly when the two crossed intersections
admit a linear isometric equivalence, which is the cardinal-free form of the
paper's equal-dimension condition (3.5). -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent_real :
    (∃ T : E →L[ℝ] E, IsDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  proposition3_2_exists_iff_crossedDefectsEquivalent U V

/-- **Davis--Kahan 1970, Proposition 3.2, the injective parameterization, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_parameterized_nonuniqueness`. -/
theorem proposition3_2_parameterized_nonuniqueness_real
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V) →
          (E →L[ℝ] E),
      (∀ J, IsDirectRotation U V (build J)) ∧
      Function.Injective build :=
  proposition3_2_parameterized_nonuniqueness U V hdefect

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence, over a real
Hilbert space: "It is not unique."**

The `𝕜 = ℝ` instance of `proposition3_2_not_unique`.  Over `ℝ` the two witnesses
are still `build J` and `build (-J)`; the sign change is available because the
scalar field has characteristic zero, which `RCLike` supplies. -/
theorem proposition3_2_not_unique_real
    (hdefect : CrossedDefectsEquivalent U V)
    (hnonacute : ¬ TauCeti.IsAcute U V) :
    ∃ T₁ T₂ : E →L[ℝ] E,
      IsDirectRotation U V T₁ ∧ IsDirectRotation U V T₂ ∧
        T₁ ≠ T₂ :=
  proposition3_2_not_unique U V hdefect hnonacute

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `proposition3_2_not_existsUnique`. -/
theorem proposition3_2_not_existsUnique_real
    (hdefect : CrossedDefectsEquivalent U V)
    (hnonacute : ¬ TauCeti.IsAcute U V) :
    ¬ ∃! T : E →L[ℝ] E, IsDirectRotation U V T :=
  proposition3_2_not_existsUnique U V hdefect hnonacute

/-- **Davis--Kahan 1970, the Remark after Proposition 3.2, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of
`remark3_2_bilateralShift_separates_dimensionHypotheses`: the bilateral shift
witnesses (1.4), hence (1.5), while the crossed intersections are a line and
zero, so (3.5) fails and the pair admits no direct rotation. -/
theorem remark3_2_bilateralShift_separates_dimensionHypotheses_real
    (b : HilbertBasis ℤ ℝ E) :
    (bilateralShiftL b ∈ unitary (E →L[ℝ] E) ∧
        bilateralShiftL b * Submodule.starProjection (coordinateHalfSpace b 0) =
          Submodule.starProjection (coordinateHalfSpace b 1) * bilateralShiftL b) ∧
      (Nonempty (coordinateHalfSpace b 0 ≃ₗᵢ[ℝ] coordinateHalfSpace b 1) ∧
        Nonempty ((coordinateHalfSpace b 0)ᗮ ≃ₗᵢ[ℝ]
          (coordinateHalfSpace b 1)ᗮ)) ∧
      halmosSourceDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) ≠ ⊥ ∧
      halmosTargetDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) = ⊥ ∧
      ¬ ∃ T : E →L[ℝ] E,
        IsDirectRotation (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) T :=
  remark3_2_bilateralShift_separates_dimensionHypotheses b

end RealScalars

end DavisKahan1970
end TauCeti
