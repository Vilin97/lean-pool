/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed

/-!
# Sylvester equations for partial linear maps

The domain-aware equation `A X - X B = C`, semibounds, and bounded-everywhere
inverse data stated directly for Mathlib `LinearPMap` operators.  Analytic
properties such as closedness, dense domain, and self-adjointness remain
separate hypotheses for the theorems that require them.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Sylvester/ClosedSylvesterEquation.lean`.
* Extraction class: **representation migration and generalization** from the
  bundled DKPS `PartialMap` to raw Mathlib `LinearPMap`.
* Spectra influence: none.  This module depends only on Mathlib and the
  dependency-clean `LinearPMap` domain API.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Lower semibound for a partial linear map. -/
def SemiboundedBelow (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜

/-- Upper semibound for a partial linear map. -/
def SemiboundedAbove (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2

/-- Unfolds the lower semibound through a stable public API: `SemiboundedBelow`
is kept abstract across module boundaries, so consumers use this rather than
definitional transparency. -/
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔
      ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 :=
  Iff.rfl

/-- Unfolds the upper semibound through a stable public API. -/
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔
      ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2 :=
  Iff.rfl

/-- A lower semibound remains valid after decreasing the constant. -/
theorem SemiboundedBelow.mono {A : E →ₗ.[𝕜] E} {c d : ℝ}
    (hA : SemiboundedBelow A c) (hdc : d ≤ c) :
    SemiboundedBelow A d := by
  intro x
  exact (mul_le_mul_of_nonneg_right hdc (sq_nonneg ‖(x : E)‖)).trans (hA x)

/-- An upper semibound remains valid after increasing the constant. -/
theorem SemiboundedAbove.mono {A : E →ₗ.[𝕜] E} {c d : ℝ}
    (hA : SemiboundedAbove A c) (hcd : c ≤ d) :
    SemiboundedAbove A d := by
  intro x
  exact (hA x).trans
    (mul_le_mul_of_nonneg_right hcd (sq_nonneg ‖(x : E)‖))

/-- Domain-aware Sylvester equation `A X - X B = C` for partial linear maps. -/
structure SylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X C : F →L[𝕜] E) : Prop where
  mapsTo_domain : MapsDomainTo A B X
  equation : ∀ x : B.domain,
    A ⟨X (x : F), mapsTo_domain x⟩ - X (B x) = C (x : F)

namespace SylvesterEquation

/-- Extract domain transport from a Sylvester equation. -/
theorem mapsTo {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E} (h : SylvesterEquation A B X C) :
    MapsDomainTo A B X :=
  h.mapsTo_domain

/-- A bounded Sylvester equation is a full-domain partial-map equation. -/
theorem ofBounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    SylvesterEquation
      (A.toLinearMap.toPMap ⊤) (B.toLinearMap.toPMap ⊤) X C := by
  refine { mapsTo_domain := ?_, equation := ?_ }
  · intro x
    simp
  · intro x
    have hx := congrArg (fun T : F →L[𝕜] E => T (x : F)) hEq
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (X (x : F)) - X (B (x : F)) = C (x : F)
    simpa only [ContinuousLinearMap.comp_apply, sub_apply] using hx

/-- The zero map solves the homogeneous domain-aware equation. -/
theorem zero (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    SylvesterEquation A B 0 0 := by
  refine ⟨?_, ?_⟩
  · intro x
    simp
  · intro x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (0 : A.domain) - 0 = (0 : E)
    simp

/-- Domain-aware Sylvester equations add. -/
theorem add {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X + Y) (C + D) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    have hxY : Y (x : F) ∈ A.domain := hY.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    let uY : A.domain := ⟨Y (x : F), hxY⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    have hEqY : A uY - Y (B x) = D (x : F) := by
      simpa [uY] using hY.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (uX + uY) - (X (B x) + Y (B x)) =
      C (x : F) + D (x : F)
    calc
      A (uX + uY) - (X (B x) + Y (B x)) =
          (A uX - X (B x)) + (A uY - Y (B x)) := by
            rw [_root_.LinearPMap.map_add A uX uY]
            abel
      _ = C (x : F) + D (x : F) := by rw [hEqX, hEqY]

/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) :
    SylvesterEquation A B (-X) (-C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.neg_mem (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (-uX) - (-X (B x)) = -C (x : F)
    calc
      A (-uX) - (-X (B x)) = -(A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_neg A uX]
        abel
      _ = -C (x : F) := by rw [hEqX]

/-- Domain-aware Sylvester equations subtract. -/
theorem sub {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X - Y) (C - D) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

/-- Domain-aware Sylvester equations commute with scalar multiplication. -/
theorem smul {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) (c : 𝕜) :
    SylvesterEquation A B (c • X) (c • C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.smul_mem c (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (c • uX) - c • X (B x) = c • C (x : F)
    calc
      A (c • uX) - c • X (B x) = c • (A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_smul A c uX, smul_sub]
      _ = c • C (x : F) := by rw [hEqX]

end SylvesterEquation

/-- A Sylvester equation with a partial left block and a bounded right block.
This is the ordinary partial-map equation with the right block embedded on its
full domain. -/
abbrev UnboundedBoundedSylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  SylvesterEquation A (B.toLinearMap.toPMap ⊤) X C

/-- A partial linear map whose inverse is everywhere defined and bounded. -/
structure HasBoundedEverywhereInverse (A : E →ₗ.[𝕜] E) where
  /-- The bounded everywhere-defined inverse, whose range lies in the partial operator's domain. -/
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y, A ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)

namespace HasBoundedEverywhereInverse

/-- A partial map with an everywhere-defined two-sided inverse is injective. -/
theorem injective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Injective A := by
  intro x y hxy
  apply Subtype.ext
  calc
    (x : E) = hA.inv (A x) := (hA.inv_apply x).symm
    _ = hA.inv (A y) := congrArg hA.inv hxy
    _ = (y : E) := hA.inv_apply y

/-- A partial map with an everywhere-defined two-sided inverse is surjective
onto the ambient codomain. -/
theorem surjective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Surjective A := by
  intro y
  exact ⟨⟨hA.inv y, hA.inv_mapsTo_domain y⟩, hA.apply_inv y⟩

end HasBoundedEverywhereInverse

end LinearPMap
end TauCeti

end
