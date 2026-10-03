/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Complex direct rotation, the attribution-preserving bridge

This module connects the proof-complete complex polar-factor construction to
Davis--Kahan's established direct-rotation namespace and theorem interfaces.
`SpectraBridge` is the attribution-preserving name for that boundary: the
construction it wraps came from the vendored Spectra package, which was retired
on 2026-07-29, and the polar factor it names is now native
(`Geometry/Polar/DirectRotationSquare.lean`).
The scalar-generic declarations remain independent; these declarations provide
the completed complex specialization without weakening or replacing the real
and general `RCLike` program.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The completed complex direct rotation, the polar factor of the canonical
intertwiner. -/
noncomputable abbrev complexDirectRotation
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : H →L[ℂ] H :=
  _root_.TauCeti.DavisKahan.spectraDirectRotation U V hacute

/-- The complex direct rotation is norm-preserving and onto. -/
theorem complexDirectRotation_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    TauCeti.LinearPMap.IsUnitaryOperator (complexDirectRotation U V hacute) :=
  ⟨_root_.TauCeti.DavisKahan.norm_spectraDirectRotation_apply
      U V hacute,
    _root_.TauCeti.DavisKahan.spectraDirectRotation_surjective
      U V hacute⟩

/-- The complex direct rotation is the unique unitary square root of the
ordered reflection product whose numerical real part is nonnegative.  No
separate commutation hypothesis is needed: it follows from the square
identity. -/
theorem complexDirectRotation_unique
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V)
    (W : H →L[ℂ] H)
    (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hsq : W * W = V.reflectionOperator * U.reflectionOperator)
    (hre : ∀ x, 0 ≤ Complex.re ⟪W x, x⟫_ℂ) :
    W = complexDirectRotation U V hacute :=
  _root_.TauCeti.DavisKahan.spectraDirectRotation_unique_of_sq
    U V hacute W hWunit hsq hre

/-- The complex direct rotation intertwines the source and target
projections. -/
theorem complexDirectRotation_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    complexDirectRotation U V hacute ∘L U.starProjection =
      V.starProjection ∘L complexDirectRotation U V hacute := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_intertwines
      U V hacute

/-- The complex direct rotation maps the source subspace onto the target
subspace. -/
theorem complexDirectRotation_maps_subspace
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    U.map (complexDirectRotation U V hacute).toLinearMap = V :=
  _root_.TauCeti.DavisKahan.spectraDirectRotation_maps_subspace
    U V hacute

/-- The complex direct rotation maps orthogonal complements onto orthogonal
complements. -/
theorem complexDirectRotation_maps_orthogonalComplement
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Uᗮ.map (complexDirectRotation U V hacute).toLinearMap = Vᗮ :=
  _root_.TauCeti.DavisKahan.spectraDirectRotation_maps_orthogonalComplement
    U V hacute

/-- The foundational direct-rotation properties are simultaneously realized
in the complex acute case. -/
theorem exists_complexDirectRotation
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L U.starProjection = V.starProjection ∘L W ∧
      U.map W.toLinearMap = V :=
  ⟨complexDirectRotation U V hacute,
    complexDirectRotation_unitary U V hacute,
    complexDirectRotation_intertwines U V hacute,
    complexDirectRotation_maps_subspace U V hacute⟩


/-- The complete foundational complex package, including transport of the
orthogonal complements. -/
theorem exists_complexDirectRotation_with_complements
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L U.starProjection = V.starProjection ∘L W ∧
      U.map W.toLinearMap = V ∧
      Uᗮ.map W.toLinearMap = Vᗮ :=
  ⟨complexDirectRotation U V hacute,
    complexDirectRotation_unitary U V hacute,
    complexDirectRotation_intertwines U V hacute,
    complexDirectRotation_maps_subspace U V hacute,
    complexDirectRotation_maps_orthogonalComplement U V hacute⟩


/-! ## Elementary adjoint and reflection consequences -/

/-- The complex direct rotation is a unitary element of the bounded operator
algebra. -/
theorem complexDirectRotation_mem_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    complexDirectRotation U V hacute ∈ unitary (H →L[ℂ] H) :=
  _root_.TauCeti.DavisKahan.spectraDirectRotation_mem_unitary
    U V hacute

/-- The adjoint of the complex direct rotation is its left inverse. -/
theorem star_complexDirectRotation_comp_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (complexDirectRotation U V hacute) ∘L
        complexDirectRotation U V hacute = 1 := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.star_spectraDirectRotation_mul_self
      U V hacute

/-- The adjoint of the complex direct rotation is its right inverse. -/
theorem complexDirectRotation_comp_star_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    complexDirectRotation U V hacute ∘L
        star (complexDirectRotation U V hacute) = 1 := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_mul_star_self
      U V hacute

/-- The adjoint intertwines the target projection back to the source
projection. -/
theorem star_complexDirectRotation_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (complexDirectRotation U V hacute) ∘L V.starProjection =
      U.starProjection ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.star_spectraDirectRotation_intertwines
      U V hacute

/-- The adjoint also intertwines complementary target and source projections. -/
theorem star_complexDirectRotation_intertwines_complementary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (complexDirectRotation U V hacute) ∘L (Vᗮ).starProjection =
      (Uᗮ).starProjection ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.star_spectraDirectRotation_intertwines_complementary
      U V hacute

/-- Conjugation by the complex direct rotation carries the source projection
to the target projection. -/
theorem complexDirectRotation_conjugates_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (complexDirectRotation U V hacute ∘L U.starProjection) ∘L
        star (complexDirectRotation U V hacute) = V.starProjection := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_conjugates_projection
      U V hacute

/-- Conjugation by the adjoint carries the target projection back to the source projection. -/
theorem star_complexDirectRotation_conjugates_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (star (complexDirectRotation U V hacute) ∘L V.starProjection) ∘L
        complexDirectRotation U V hacute = U.starProjection := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.star_spectraDirectRotation_conjugates_projection
      U V hacute

/-- Conjugation by the complex direct rotation carries complementary source projection to the
complementary target projection. -/
theorem complexDirectRotation_conjugates_complementaryProjection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (complexDirectRotation U V hacute ∘L (Uᗮ).starProjection) ∘L
        star (complexDirectRotation U V hacute) = (Vᗮ).starProjection := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_conjugates_complementaryProjection
      U V hacute

/-- The complex direct rotation intertwines the source and target
reflections. -/
theorem complexDirectRotation_intertwines_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    complexDirectRotation U V hacute ∘L U.reflectionOperator =
      V.reflectionOperator ∘L complexDirectRotation U V hacute := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_intertwines_reflection
      U V hacute

/-- The adjoint intertwines the target reflection back to the source reflection. -/
theorem star_complexDirectRotation_intertwines_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (complexDirectRotation U V hacute) ∘L V.reflectionOperator =
      U.reflectionOperator ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.star_spectraDirectRotation_intertwines_reflection
      U V hacute

/-- Conjugation by the complex direct rotation carries the source reflection
to the target reflection. -/
theorem complexDirectRotation_conjugates_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (complexDirectRotation U V hacute ∘L U.reflectionOperator) ∘L
        star (complexDirectRotation U V hacute) = V.reflectionOperator := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.TauCeti.DavisKahan.spectraDirectRotation_conjugates_reflection
      U V hacute

/-- The adjoint of the complex direct rotation maps the target subspace back
onto the source subspace. -/
theorem star_complexDirectRotation_maps_subspace
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    V.map ((star (complexDirectRotation U V hacute) :
      H →L[ℂ] H).toLinearMap) = U :=
  _root_.TauCeti.DavisKahan.star_spectraDirectRotation_maps_subspace
    U V hacute

/-- The adjoint of the complex direct rotation maps the target orthogonal
complement back onto the source orthogonal complement. -/
theorem star_complexDirectRotation_maps_orthogonalComplement
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Vᗮ.map ((star (complexDirectRotation U V hacute) :
      H →L[ℂ] H).toLinearMap) = Uᗮ :=
  _root_.TauCeti.DavisKahan.star_spectraDirectRotation_maps_orthogonalComplement
    U V hacute


/-- The complex direct rotation minimizes operator-norm displacement from the
identity among unitary projection intertwiners. -/
theorem complexDirectRotation_minimal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V)
    (W : H →L[ℂ] H) (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hintertwine : W ∘L U.starProjection = V.starProjection ∘L W) :
    ‖complexDirectRotation U V hacute - 1‖ ≤ ‖W - 1‖ := by
  apply _root_.TauCeti.DavisKahan.spectraDirectRotation_minimal
    U V hacute W hWunit
  simpa only [ContinuousLinearMap.mul_def] using hintertwine

end DavisKahanExt
end TauCeti
