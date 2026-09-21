/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-!
# Finite-dimensional spectral-gap predicates

Canonical separation hypotheses used by the sine, tangent, double-angle, and
Sylvester theorem families.

## Sources

The spectral-gap predicates are the hypotheses of Davis--Kahan's `sin Θ` theorem in
the form the theorem consumes; see
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/SpectralGap.lean`
before the dependency-closed base of the sin-Θ core moved into the staging
layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Two restricted spectra are separated by at least `δ`. -/
@[expose]
def PointSpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedPointSpectrum A U → μ ∈ restrictedPointSpectrum B V →
    δ ≤ |lam - μ|

/-- The mixed separation used by the `sin Θ` theorem: the selected block of
`A` is separated from the complementary block of `B`. -/
@[expose]
def HybridGap (A B : E →ₗ[𝕜] E) (U V : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  PointSpectraSeparated A U B Vᗮ δ

/-- Invariance of `U` and separation of the point spectra on `U` and its complement.

This predicate is appropriate for the `sin Θ` and `sin (2Θ)` families and for
the general disjoint-spectrum Sylvester estimate.  It is not sufficient for
the sharp `tan (2Θ)` theorem: interlacing spectra can satisfy absolute
separation while an off-diagonal perturbation produces a quarter-turn angle.
That theorem requires `OrderedInternalGap` (or an equivalent two-sided form
ordering). -/
@[expose]
def PointInternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  IsInvariant A U ∧ PointSpectraSeparated A U A Uᗮ δ

/-- Ordered quadratic-form separation between the two blocks of `A`.

The selected block `U` lies above `b`, while its orthogonal complement lies
below `a`.  Together with `a < b`, this is the sharp constant-one hypothesis
used by the finite-dimensional `sin (2 Θ)` theorem. -/
def TwoBlockFormGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (a b : ℝ) : Prop :=
  (∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) ∧
    (∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)

/-- Point spectra in an interval and its enlarged exterior, on possibly different spaces.
The complementary subspace, when needed, is supplied explicitly by the caller. -/
@[expose]
def PointIntervalExteriorGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (a b δ : ℝ) : Prop :=
  PointSpectrumIn A U (Set.Icc a b) ∧
    PointSpectrumIn B V {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- The one-sided gap used by the tangent theorems. -/
@[expose]
def OrderedGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedPointSpectrum A U → μ ∈ restrictedPointSpectrum B V →
    lam + δ ≤ μ

/-- Ordered separation of the two diagonal blocks of `A`, in either
orientation.  This stronger predicate is useful when reducing a double-angle
argument to the elementary ordered Sylvester theorem. -/
def OrderedInternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  OrderedGap A U A Uᗮ δ ∨ OrderedGap A Uᗮ A U δ

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The conversion between the two primitives, and the reason both are named: a theorem
family stated against the weaker hypothesis applies to a caller holding the stronger one. -/
theorem PointSpectraSeparated.of_orderedGap {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →ₗ[𝕜] F} {V : Submodule 𝕜 F} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : OrderedGap A U B V δ) : PointSpectraSeparated A U B V δ := by
  intro lam μ hlam hμ
  have hle : lam + δ ≤ μ := h lam μ hlam hμ
  rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ μ - lam)]
  linarith

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Spectral inclusion on opposite sides of a cut gives ordered separation: the bridge that
turns a hypothesis a caller can check into the one the theorems consume. -/
theorem orderedGap_of_restrictedPointSpectrum_subset {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →ₗ[𝕜] F} {V : Submodule 𝕜 F} {a δ : ℝ}
    (hA : restrictedPointSpectrum A U ⊆ Set.Iic a)
    (hB : restrictedPointSpectrum B V ⊆ Set.Ici (a + δ)) :
    OrderedGap A U B V δ := by
  intro lam μ hlam hμ
  have h1 : lam ≤ a := hA hlam
  have h2 : a + δ ≤ μ := hB hμ
  linarith

omit [FiniteDimensional 𝕜 E] in
/-- Spectral inclusion on opposite sides of a cut gives the corresponding
ordered internal gap. -/
theorem orderedInternalGap_of_pointSpectrumIn_Iic_Ici
    {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {a b : ℝ}
    (hUa : PointSpectrumIn A U (Set.Iic a))
    (hUb : PointSpectrumIn A Uᗮ (Set.Ici b)) :
    OrderedInternalGap A U (b - a) := by
  left
  intro lam μ hlam hμ
  have hlam_le : lam ≤ a := hUa hlam
  have hb_le_hμ : b ≤ μ := hUb hμ
  linarith

omit [FiniteDimensional 𝕜 E] in
/-- Ordered block separation implies absolute block separation.
-/
theorem OrderedInternalGap.pointInternalGap {A : E →ₗ[𝕜] E}
    {U : Submodule 𝕜 E} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : OrderedInternalGap A U δ) (hU : IsInvariant A U) :
    PointInternalGap A U δ := by
  refine ⟨hU, ?_⟩
  intro lam μ hlam hμ
  rcases h with hlow | hhigh
  · have hle := hlow lam μ hlam hμ
    have hlam_le : lam ≤ μ := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hlam_le)]
    linarith
  · have hle := hhigh μ lam hμ hlam
    have hμ_le : μ ≤ lam := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hμ_le)]
    linarith


end TauCeti
