/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Reflection
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Direct Rotation -/

@[expose] public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-!
# The pre-polar canonical intertwiner and its polar factor

For two orthogonally complemented subspaces of a Hilbert space over an
arbitrary `RCLike` field, this module introduces

`S = Q P + Qᗮ Pᗮ`.

The operator `S` is the pre-polar canonical intertwiner in the Davis--Kahan
direct-rotation construction.  The main result of this slice is that acuteness
makes `S` a unit.  The proof uses the exact factorization

`S - 1 = (Q - P) J_P`,

where `J_P` is the reflection through the first subspace.  Since the reflection
is contractive, the projection gap bounds `‖S - 1‖`; the acute hypothesis then
places `S` in the open unit ball around the identity, where the Neumann-series
inverse is available.

The polar factor is then shown to be unitary in the acute regime, to
intertwine the two orthogonal projections, and to carry the source subspace
onto the target subspace.

## The scalar field

Everything here is stated over an arbitrary `RCLike` field.  The real scalar structure and
self-adjoint continuous functional calculus used by the modulus are supplied by `ForTauCeti`
and activated locally in this module, so they do not appear in the public theorem signatures.

The remaining `spectra*` prefixes and `_complex` suffixes are historical names from the
Spectra-backed and complex-only eras.  They name Davis--Kahan-specific composites rather than a
second modulus or polar-factor implementation; their eventual naming cleanup is independent of
the canonical polar API used here.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


/-- The canonical pre-polar intertwiner `Q P + Qᗮ Pᗮ`. -/
noncomputable def spectraCanonicalIntertwiner
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  V.starProjection * U.starProjection +
    (Vᗮ).starProjection * (Uᗮ).starProjection

omit [CompleteSpace H] in
/-- The canonical intertwiner sends the `U` block into the `V` block. -/
theorem spectraCanonicalIntertwiner_mul_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V * U.starProjection =
      V.starProjection * spectraCanonicalIntertwiner U V := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) * U.starProjection =
      V.starProjection *
        (V.starProjection * U.starProjection +
          Vᗮ.starProjection * Uᗮ.starProjection)
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  have hQ : V.starProjection * V.starProjection = V.starProjection :=
    V.isIdempotentElem_starProjection
  noncomm_ring [hP, hQ]
  rw [← mul_assoc, hQ]
  module

/-- The adjoint of the canonical intertwiner is obtained by reversing the
ordered pair of subspaces. -/
theorem star_spectraCanonicalIntertwiner
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner V U := by
  change
    star (V.starProjection * U.starProjection +
      Vᗮ.starProjection * Uᗮ.starProjection) =
      U.starProjection * V.starProjection +
        Uᗮ.starProjection * Vᗮ.starProjection
  simp only [star_add, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq]

omit [CompleteSpace H] in
/-- Reflection through `U` written in the projection algebra. -/
theorem reflectionOperator_eq_projection_add_projection_sub_one
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    U.reflectionOperator = U.starProjection + U.starProjection - 1 := by
  ext x
  rw [Submodule.reflectionOperator_apply]
  simp only [add_apply, sub_apply, one_apply_eq_self]
  module

omit [CompleteSpace H] in
/-- Exact factorization of the displacement of the canonical intertwiner from
the identity. -/
theorem spectraCanonicalIntertwiner_sub_one
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V - 1 =
      (V.starProjection - U.starProjection) * U.reflectionOperator := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) - 1 =
      (V.starProjection - U.starProjection) * U.reflectionOperator
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  rw [show U.reflectionOperator =
    U.starProjection + U.starProjection - 1 by
      exact reflectionOperator_eq_projection_add_projection_sub_one U]
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  noncomm_ring [hP]

omit [CompleteSpace H] in
/-- The displacement of the canonical intertwiner is bounded by the symmetric
projection gap. -/
theorem norm_spectraCanonicalIntertwiner_sub_one_le_gap
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖spectraCanonicalIntertwiner U V - 1‖ ≤ U.projectionGap V := by
  rw [spectraCanonicalIntertwiner_sub_one]
  calc
    ‖(V.starProjection - U.starProjection) * U.reflectionOperator‖
        ≤ ‖V.starProjection - U.starProjection‖ * ‖U.reflectionOperator‖ :=
      norm_mul_le _ _
    _ ≤ ‖V.starProjection - U.starProjection‖ * 1 :=
      mul_le_mul_of_nonneg_left (Submodule.norm_reflectionOperator_le_one U)
        (norm_nonneg (V.starProjection - U.starProjection))
    _ = U.projectionGap V := by
      rw [mul_one]
      change ‖V.starProjection - U.starProjection‖ =
        ‖U.starProjection - V.starProjection‖
      rw [show V.starProjection - U.starProjection =
        -(U.starProjection - V.starProjection) by abel, norm_neg]

omit [CompleteSpace H] in
/-- Equivalent one-sided norm estimate, in the form consumed by
`Units.oneSub`. -/
theorem norm_one_sub_spectraCanonicalIntertwiner_le_gap
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖1 - spectraCanonicalIntertwiner U V‖ ≤ U.projectionGap V := by
  rw [show 1 - spectraCanonicalIntertwiner U V =
    -(spectraCanonicalIntertwiner U V - 1) by abel, norm_neg]
  exact norm_spectraCanonicalIntertwiner_sub_one_le_gap U V

omit [CompleteSpace H] in
/-- Acuteness places the canonical intertwiner strictly inside the unit ball
around the identity. -/
theorem norm_one_sub_spectraCanonicalIntertwiner_lt_one
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    ‖1 - spectraCanonicalIntertwiner U V‖ < 1 :=
  (norm_one_sub_spectraCanonicalIntertwiner_le_gap U V).trans_lt hacute

/-- The canonical intertwiner bundled as a unit in the acute regime. -/
noncomputable def spectraCanonicalIntertwinerUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : (H →L[𝕜] H)ˣ :=
  Units.oneSub (1 - spectraCanonicalIntertwiner U V)
    (norm_one_sub_spectraCanonicalIntertwiner_lt_one U V hacute)

/-- The bundled unit has the intended underlying canonical intertwiner. -/
@[simp]
theorem coe_spectraCanonicalIntertwinerUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (spectraCanonicalIntertwinerUnit U V hacute : H →L[𝕜] H) =
      spectraCanonicalIntertwiner U V := by
  simp [spectraCanonicalIntertwinerUnit]

/-- The polar factor of the canonical intertwiner. -/
noncomputable def spectraCanonicalPolarFactor
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  (spectraCanonicalIntertwiner U V).polarPartial

/-- Spectra-backed direct-rotation candidate in the acute regime.  The acute
witness records the intended branch; the underlying polar factor is defined
for every pair. -/
noncomputable def spectraDirectRotation
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsUniformlyAcute U V) : H →L[𝕜] H :=
  spectraCanonicalPolarFactor U V

/-- Polar decomposition of the canonical intertwiner. -/
theorem spectraCanonicalPolarFactor_decomposition
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalPolarFactor U V ∘L
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V :=
  ContinuousLinearMap.polarPartial_comp_modulus (spectraCanonicalIntertwiner U V)

/-- Polar decomposition stated through the acute direct-rotation candidate. -/
theorem spectraDirectRotation_decomposition
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute ∘L
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V :=
  spectraCanonicalPolarFactor_decomposition U V

end DavisKahan
end TauCeti
namespace TauCeti
namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


/-- The absolute value of the acute canonical intertwiner is invertible. -/
theorem isUnit_spectraCanonicalAbsoluteValue
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    IsUnit (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) := by
  rw [← isUnit_mul_self_iff]
  rw [ContinuousLinearMap.modulus_mul_self_eq_star_mul_self]
  have hS : IsUnit (spectraCanonicalIntertwiner U V) := by
    rw [← coe_spectraCanonicalIntertwinerUnit U V hacute]
    exact (spectraCanonicalIntertwinerUnit U V hacute).isUnit
  exact hS.star.mul hS

/-- The absolute value of the acute canonical intertwiner, bundled as a unit. -/
noncomputable def spectraCanonicalAbsoluteValueUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : (H →L[𝕜] H)ˣ :=
  Classical.choose (isUnit_spectraCanonicalAbsoluteValue U V hacute)

/-- The absolute-value unit has the expected underlying operator. -/
@[simp]
theorem coe_spectraCanonicalAbsoluteValueUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (spectraCanonicalAbsoluteValueUnit U V hacute : H →L[𝕜] H) =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) :=
  Classical.choose_spec (isUnit_spectraCanonicalAbsoluteValue U V hacute)

/-- The absolute-value unit is fixed by the star operation. -/
theorem star_spectraCanonicalAbsoluteValueUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraCanonicalAbsoluteValueUnit U V hacute) =
      spectraCanonicalAbsoluteValueUnit U V hacute := by
  apply Units.ext
  simp only [Units.coe_star]
  rw [coe_spectraCanonicalAbsoluteValueUnit]
  exact (ContinuousLinearMap.modulus_isSelfAdjoint
    (spectraCanonicalIntertwiner U V)).star_eq

/-- The Gram units of the canonical intertwiner and its absolute value agree. -/
theorem star_intertwinerUnit_mul_self_eq_absoluteValueUnit_mul_self
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraCanonicalIntertwinerUnit U V hacute) *
        spectraCanonicalIntertwinerUnit U V hacute =
      spectraCanonicalAbsoluteValueUnit U V hacute *
        spectraCanonicalAbsoluteValueUnit U V hacute := by
  apply Units.ext
  simp only [Units.val_mul, Units.coe_star]
  rw [coe_spectraCanonicalIntertwinerUnit,
    coe_spectraCanonicalAbsoluteValueUnit]
  exact (ContinuousLinearMap.modulus_mul_self_eq_star_mul_self
    (spectraCanonicalIntertwiner U V)).symm

/-- The Spectra polar factor bundled as a unit, using the invertible polar
formula `S |S|⁻¹`. -/
noncomputable def spectraCanonicalPolarFactorUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : (H →L[𝕜] H)ˣ :=
  spectraCanonicalIntertwinerUnit U V hacute *
    (spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹

/-- The algebraic unit formula agrees with Spectra's polar factor. -/
@[simp]
theorem coe_spectraCanonicalPolarFactorUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (spectraCanonicalPolarFactorUnit U V hacute : H →L[𝕜] H) =
      spectraCanonicalPolarFactor U V := by
  let AUnit := spectraCanonicalAbsoluteValueUnit U V hacute
  let SUnit := spectraCanonicalIntertwinerUnit U V hacute
  let A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  let S := spectraCanonicalIntertwiner U V
  let W := spectraCanonicalPolarFactor U V
  have hA : (AUnit : H →L[𝕜] H) = A :=
    coe_spectraCanonicalAbsoluteValueUnit U V hacute
  have hS : (SUnit : H →L[𝕜] H) = S :=
    coe_spectraCanonicalIntertwinerUnit U V hacute
  have hdecomp : W * A = S := by
    simpa only [ContinuousLinearMap.mul_def] using
      spectraCanonicalPolarFactor_decomposition U V
  change ((SUnit * AUnit⁻¹ : (H →L[𝕜] H)ˣ) : H →L[𝕜] H) = W
  symm
  calc
    W = W * 1 := (mul_one W).symm
    _ = W * ((AUnit : H →L[𝕜] H) * (↑(AUnit⁻¹) : H →L[𝕜] H)) := by
      rw [AUnit.mul_inv]
    _ = (W * (AUnit : H →L[𝕜] H)) * (↑(AUnit⁻¹) : H →L[𝕜] H) := by
      rw [mul_assoc]
    _ = (W * A) * (↑(AUnit⁻¹) : H →L[𝕜] H) := by rw [hA]
    _ = S * (↑(AUnit⁻¹) : H →L[𝕜] H) := by rw [hdecomp]
    _ = (SUnit : H →L[𝕜] H) * (↑(AUnit⁻¹) : H →L[𝕜] H) := by rw [hS]
    _ = ((SUnit * AUnit⁻¹ : (H →L[𝕜] H)ˣ) : H →L[𝕜] H) := rfl

/-- The acute canonical polar factor is a unitary element of the bounded
operator algebra. -/
noncomputable def spectraCanonicalPolarFactorUnitary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : unitary (H →L[𝕜] H) := by
  let SUnit := spectraCanonicalIntertwinerUnit U V hacute
  let AUnit := spectraCanonicalAbsoluteValueUnit U V hacute
  have hGram : star SUnit * SUnit = star AUnit * AUnit := by
    rw [star_spectraCanonicalAbsoluteValueUnit U V hacute]
    exact star_intertwinerUnit_mul_self_eq_absoluteValueUnit_mul_self U V hacute
  have hmem : (((SUnit * AUnit⁻¹ : (H →L[𝕜] H)ˣ) : H →L[𝕜] H)) ∈
      unitary (H →L[𝕜] H) :=
    (Units.mul_inv_mem_unitary SUnit AUnit).2 hGram
  refine ⟨spectraCanonicalPolarFactor U V, ?_⟩
  rw [← coe_spectraCanonicalPolarFactorUnit U V hacute]
  exact hmem

/-- The unitary subtype has the intended underlying polar factor. -/
@[simp]
theorem coe_spectraCanonicalPolarFactorUnitary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    ((spectraCanonicalPolarFactorUnitary U V hacute :
        unitary (H →L[𝕜] H)) : H →L[𝕜] H) =
      spectraCanonicalPolarFactor U V := rfl

/-- The canonical polar factor preserves every vector norm. -/
theorem norm_spectraCanonicalPolarFactor_apply
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (x : H) :
    ‖spectraCanonicalPolarFactor U V x‖ = ‖x‖ := by
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute]
  exact Unitary.norm_map
    (spectraCanonicalPolarFactorUnitary U V hacute) x

/-- The canonical polar factor is onto. -/
theorem spectraCanonicalPolarFactor_surjective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Surjective (spectraCanonicalPolarFactor U V) := by
  let u := spectraCanonicalPolarFactorUnitary U V hacute
  let e := Unitary.linearIsometryEquiv u
  intro y
  obtain ⟨x, hx⟩ := e.surjective y
  refine ⟨x, ?_⟩
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute]
  have hcoe : (e : H →L[𝕜] H) = (u : H →L[𝕜] H) := by
    simp [e]
  exact (congrArg (fun T : H →L[𝕜] H => T x) hcoe).symm.trans hx

/-- The canonical polar factor is one-to-one. -/
theorem spectraCanonicalPolarFactor_injective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Injective (spectraCanonicalPolarFactor U V) := by
  let u := spectraCanonicalPolarFactorUnitary U V hacute
  let e := Unitary.linearIsometryEquiv u
  intro x y hxy
  apply e.injective
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute] at hxy
  have hcoe : (e : H →L[𝕜] H) = (u : H →L[𝕜] H) := by
    simp [e]
  have hx : e x = (u : H →L[𝕜] H) x :=
    congrArg (fun T : H →L[𝕜] H => T x) hcoe
  have hy : e y = (u : H →L[𝕜] H) y :=
    congrArg (fun T : H →L[𝕜] H => T y) hcoe
  exact hx.trans (hxy.trans hy.symm)

/-- The Gram operator of the canonical intertwiner commutes with the source
projection. -/
theorem star_spectraCanonicalIntertwiner_mul_self_commute_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V)
      (U.starProjection) := by
  have hSP := spectraCanonicalIntertwiner_mul_projection U V
  have hPSstar :
      U.starProjection * star (spectraCanonicalIntertwiner U V) =
        star (spectraCanonicalIntertwiner U V) * V.starProjection := by
    have h := congrArg star hSP
    simpa only [star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] using h
  change
    (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V) * U.starProjection =
      U.starProjection *
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V)
  calc
    (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V) * U.starProjection =
      star (spectraCanonicalIntertwiner U V) *
        (spectraCanonicalIntertwiner U V * U.starProjection) := by
          rw [mul_assoc]
    _ = star (spectraCanonicalIntertwiner U V) *
        (V.starProjection * spectraCanonicalIntertwiner U V) := by rw [hSP]
    _ = (star (spectraCanonicalIntertwiner U V) * V.starProjection) *
        spectraCanonicalIntertwiner U V := by rw [← mul_assoc]
    _ = (U.starProjection * star (spectraCanonicalIntertwiner U V)) *
        spectraCanonicalIntertwiner U V := by rw [← hPSstar]
    _ = U.starProjection *
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V) := by rw [mul_assoc]

/-- The absolute value of the canonical intertwiner commutes with the source
projection. -/
theorem spectraCanonicalAbsoluteValue_commute_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V))
      (U.starProjection) := by
  have hGram :
      Commute
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V)
        (U.starProjection) :=
    star_spectraCanonicalIntertwiner_mul_self_commute_projection U V
  change Commute
    (CFC.abs (spectraCanonicalIntertwiner U V))
    (U.starProjection)
  rw [CFC.abs, CFC.sqrt_eq_real_sqrt
    (star (spectraCanonicalIntertwiner U V) *
      spectraCanonicalIntertwiner U V)
    (star_mul_self_nonneg (spectraCanonicalIntertwiner U V))]
  exact hGram.cfcₙ_real Real.sqrt

/-- The inverse absolute-value unit also commutes with the source projection. -/
theorem spectraCanonicalAbsoluteValueUnit_inv_commute_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Commute
      (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)
      (U.starProjection) := by
  have h := spectraCanonicalAbsoluteValue_commute_projection U V
  rw [← coe_spectraCanonicalAbsoluteValueUnit U V hacute] at h
  exact h.units_inv_left

/-- The polar factor is the canonical intertwiner followed by the inverse of
its absolute value. -/
theorem spectraCanonicalPolarFactor_eq_intertwiner_mul_absoluteValueUnit_inv
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraCanonicalPolarFactor U V =
      spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H) := by
  rw [← coe_spectraCanonicalPolarFactorUnit U V hacute]
  change
    (spectraCanonicalIntertwinerUnit U V hacute : H →L[𝕜] H) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H) =
      spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)
  rw [coe_spectraCanonicalIntertwinerUnit]

/-- The acute Spectra polar factor intertwines the two orthogonal projections. -/
theorem spectraCanonicalPolarFactor_intertwines
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraCanonicalPolarFactor U V * U.starProjection =
      V.starProjection * spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor_eq_intertwiner_mul_absoluteValueUnit_inv
    U V hacute]
  have hInv :=
    spectraCanonicalAbsoluteValueUnit_inv_commute_projection U V hacute
  calc
    (spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)) *
        U.starProjection =
      spectraCanonicalIntertwiner U V *
        ((↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H) *
          U.starProjection) := by rw [mul_assoc]
    _ = spectraCanonicalIntertwiner U V *
        (U.starProjection *
          (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)) := by
            rw [hInv.eq]
    _ = (spectraCanonicalIntertwiner U V * U.starProjection) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H) := by
          rw [← mul_assoc]
    _ = (V.starProjection * spectraCanonicalIntertwiner U V) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H) := by
          rw [spectraCanonicalIntertwiner_mul_projection]
    _ = V.starProjection *
        (spectraCanonicalIntertwiner U V *
          (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)) := by
            rw [mul_assoc]

/-- The acute Spectra direct rotation preserves norms. -/
theorem norm_spectraDirectRotation_apply
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (x : H) :
    ‖spectraDirectRotation U V hacute x‖ = ‖x‖ :=
  norm_spectraCanonicalPolarFactor_apply U V hacute x

/-- The acute Spectra direct rotation is onto. -/
theorem spectraDirectRotation_surjective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Surjective (spectraDirectRotation U V hacute) :=
  spectraCanonicalPolarFactor_surjective U V hacute

/-- The acute Spectra direct rotation is one-to-one. -/
theorem spectraDirectRotation_injective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Injective (spectraDirectRotation U V hacute) :=
  spectraCanonicalPolarFactor_injective U V hacute

/-- The acute Spectra direct rotation intertwines the two orthogonal
projections. -/
theorem spectraDirectRotation_intertwines
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * U.starProjection =
      V.starProjection * spectraDirectRotation U V hacute :=
  spectraCanonicalPolarFactor_intertwines U V hacute

/-- The acute Spectra direct rotation also intertwines the complementary
orthogonal projections. -/
theorem spectraDirectRotation_intertwines_complementary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * (Uᗮ).starProjection =
      (Vᗮ).starProjection * spectraDirectRotation U V hacute := by
  rw [Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  rw [mul_sub, mul_one, sub_mul, one_mul,
    spectraDirectRotation_intertwines U V hacute]

/-- The acute Spectra direct rotation carries the source subspace onto the
target subspace. -/
theorem spectraDirectRotation_maps_subspace
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    U.map (spectraDirectRotation U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      U.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    apply spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      V.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-- The acute Spectra direct rotation also carries the orthogonal complement
of the source subspace onto the orthogonal complement of the target. -/
theorem spectraDirectRotation_maps_orthogonalComplement
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Uᗮ.map (spectraDirectRotation U V hacute).toLinearMap = Vᗮ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply Vᗮ.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Uᗮ.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply Uᗮ.starProjection_eq_self_iff.mp
    apply spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Vᗮ.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-! ## The complementary pair carries the same direct rotation

Davis--Kahan Proposition 4.3 needs Proposition 4.1 for `(Uᗮ, Vᗮ)` as well as for `(U, V)`,
because the pinched squared displacement has one block on each.  That is not a second
theorem: the canonical intertwiner `P_V P_U + P_Vᗮ P_Uᗮ` is *symmetric under swapping a
subspace for its complement*, so the whole polar construction returns literally the same
operator.  Only the double-complement identity `Uᗮᗮ = U` is involved, and it is available
here as `starProjection_orthogonal'` applied twice. -/

omit [CompleteSpace H] in
/-- The star projection of a double orthogonal complement is the original one. -/
theorem starProjection_orthogonal_orthogonal (U : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] :
    (Uᗮ)ᗮ.starProjection = U.starProjection := by
  rw [Submodule.starProjection_orthogonal' Uᗮ, Submodule.starProjection_orthogonal' U]
  abel

omit [CompleteSpace H] in
/-- **The canonical intertwiner of the complementary pair is the same operator.**

`P_Vᗮ P_Uᗮ + P_Vᗮᗮ P_Uᗮᗮ = P_Vᗮ P_Uᗮ + P_V P_U`, which is the original sum with its two
terms exchanged. -/
theorem spectraCanonicalIntertwiner_orthogonal (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner Uᗮ Vᗮ = spectraCanonicalIntertwiner U V := by
  simp only [spectraCanonicalIntertwiner,
    starProjection_orthogonal_orthogonal]
  exact add_comm _ _

omit [CompleteSpace H] in
/-- The symmetric projection gap is unchanged by passing to complements, since
`P_Uᗮ − P_Vᗮ = P_V − P_U`. -/
theorem subspaceGap_orthogonal (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Uᗮ.projectionGap Vᗮ = U.projectionGap V := by
  change ‖Uᗮ.starProjection - Vᗮ.starProjection‖ = ‖U.starProjection - V.starProjection‖
  rw [Submodule.starProjection_orthogonal' U, Submodule.starProjection_orthogonal' V,
    show (1 - U.starProjection) - (1 - V.starProjection)
      = V.starProjection - U.starProjection from by abel]
  exact norm_sub_rev _ _

omit [CompleteSpace H] in
/-- Acuteness passes to the complementary pair: it is literally the same number. -/
theorem isUniformlyAcute_orthogonal {U V : Submodule 𝕜 H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : IsUniformlyAcute U V) :
    IsUniformlyAcute Uᗮ Vᗮ := by
  unfold IsUniformlyAcute at h ⊢
  rwa [subspaceGap_orthogonal]

/-- **The direct rotation of the complementary pair is the same operator.**

The polar factor depends only on the canonical intertwiner, and the acute witness is a
`Prop` the definition discards, so this is `spectraCanonicalIntertwiner_orthogonal`
transported through `ContinuousLinearMap.polarPartial`. -/
theorem spectraDirectRotation_orthogonal (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation Uᗮ Vᗮ (isUniformlyAcute_orthogonal hacute) =
      spectraDirectRotation U V hacute := by
  simp only [spectraDirectRotation, spectraCanonicalPolarFactor,
    spectraCanonicalIntertwiner_orthogonal]

/-! ## Elementary unitary, adjoint, and reflection consequences -/

/-- The acute Spectra direct rotation is a unitary element of the bounded
operator algebra. -/
theorem spectraDirectRotation_mem_unitary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute ∈ unitary (H →L[𝕜] H) := by
  change spectraCanonicalPolarFactor U V ∈ unitary (H →L[𝕜] H)
  exact (spectraCanonicalPolarFactorUnitary U V hacute).property

/-- The adjoint is a left inverse of the acute Spectra direct rotation. -/
theorem star_spectraDirectRotation_mul_self
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraDirectRotation U V hacute) *
        spectraDirectRotation U V hacute = 1 :=
  Unitary.star_mul_self_of_mem
    (spectraDirectRotation_mem_unitary U V hacute)

/-- The adjoint is a right inverse of the acute Spectra direct rotation. -/
theorem spectraDirectRotation_mul_star_self
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute *
        star (spectraDirectRotation U V hacute) = 1 :=
  Unitary.mul_star_self_of_mem
    (spectraDirectRotation_mem_unitary U V hacute)

/-- The adjoint of the acute Spectra direct rotation intertwines the target
projection back to the source projection. -/
theorem star_spectraDirectRotation_intertwines
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraDirectRotation U V hacute) * V.starProjection =
      U.starProjection * star (spectraDirectRotation U V hacute) := by
  have h := congrArg star (spectraDirectRotation_intertwines U V hacute)
  simpa only [star_mul, star_star,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] using h.symm

/-- The adjoint also intertwines the complementary target projection back to
the complementary source projection. -/
theorem star_spectraDirectRotation_intertwines_complementary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraDirectRotation U V hacute) * (Vᗮ).starProjection =
      (Uᗮ).starProjection * star (spectraDirectRotation U V hacute) := by
  rw [Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  rw [mul_sub, mul_one, sub_mul, one_mul,
    star_spectraDirectRotation_intertwines U V hacute]

/-- Conjugation by the acute Spectra direct rotation carries the source
projection to the target projection. -/
theorem spectraDirectRotation_conjugates_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * U.starProjection *
        star (spectraDirectRotation U V hacute) = V.starProjection := by
  calc
    spectraDirectRotation U V hacute * U.starProjection *
        star (spectraDirectRotation U V hacute) =
      (V.starProjection * spectraDirectRotation U V hacute) *
        star (spectraDirectRotation U V hacute) := by
          rw [spectraDirectRotation_intertwines U V hacute]
    _ = V.starProjection *
        (spectraDirectRotation U V hacute *
          star (spectraDirectRotation U V hacute)) := by rw [mul_assoc]
    _ = V.starProjection := by
      rw [spectraDirectRotation_mul_star_self U V hacute, mul_one]

/-- Conjugation by the adjoint carries the target projection back to the
source projection. -/
theorem star_spectraDirectRotation_conjugates_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraDirectRotation U V hacute) * V.starProjection *
        spectraDirectRotation U V hacute = U.starProjection := by
  calc
    star (spectraDirectRotation U V hacute) * V.starProjection *
        spectraDirectRotation U V hacute =
      (U.starProjection * star (spectraDirectRotation U V hacute)) *
        spectraDirectRotation U V hacute := by
          rw [star_spectraDirectRotation_intertwines U V hacute]
    _ = U.starProjection *
        (star (spectraDirectRotation U V hacute) *
          spectraDirectRotation U V hacute) := by rw [mul_assoc]
    _ = U.starProjection := by
      rw [star_spectraDirectRotation_mul_self U V hacute, mul_one]

/-- Conjugation by the acute Spectra direct rotation carries complementary
source projection to the complementary target projection. -/
theorem spectraDirectRotation_conjugates_complementaryProjection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * (Uᗮ).starProjection *
        star (spectraDirectRotation U V hacute) = (Vᗮ).starProjection := by
  calc
    spectraDirectRotation U V hacute * (Uᗮ).starProjection *
        star (spectraDirectRotation U V hacute) =
      ((Vᗮ).starProjection * spectraDirectRotation U V hacute) *
        star (spectraDirectRotation U V hacute) := by
          rw [spectraDirectRotation_intertwines_complementary U V hacute]
    _ = (Vᗮ).starProjection *
        (spectraDirectRotation U V hacute *
          star (spectraDirectRotation U V hacute)) := by rw [mul_assoc]
    _ = (Vᗮ).starProjection := by
      rw [spectraDirectRotation_mul_star_self U V hacute, mul_one]

/-- The acute Spectra direct rotation intertwines the two reflection
operators. -/
theorem spectraDirectRotation_intertwines_reflection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * U.reflectionOperator =
      V.reflectionOperator * spectraDirectRotation U V hacute := by
  simp only [reflectionOperator_eq_projection_add_projection_sub_one,
    mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul,
    spectraDirectRotation_intertwines U V hacute]

/-- The adjoint intertwines the target reflection back to the source
reflection. -/
theorem star_spectraDirectRotation_intertwines_reflection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    star (spectraDirectRotation U V hacute) * V.reflectionOperator =
      U.reflectionOperator * star (spectraDirectRotation U V hacute) := by
  simp only [reflectionOperator_eq_projection_add_projection_sub_one,
    mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul,
    star_spectraDirectRotation_intertwines U V hacute]

/-- Conjugation by the acute Spectra direct rotation carries the source
reflection to the target reflection. -/
theorem spectraDirectRotation_conjugates_reflection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * U.reflectionOperator *
        star (spectraDirectRotation U V hacute) = V.reflectionOperator := by
  calc
    spectraDirectRotation U V hacute * U.reflectionOperator *
        star (spectraDirectRotation U V hacute) =
      (V.reflectionOperator * spectraDirectRotation U V hacute) *
        star (spectraDirectRotation U V hacute) := by
          rw [spectraDirectRotation_intertwines_reflection U V hacute]
    _ = V.reflectionOperator *
        (spectraDirectRotation U V hacute *
          star (spectraDirectRotation U V hacute)) := by rw [mul_assoc]
    _ = V.reflectionOperator := by
      rw [spectraDirectRotation_mul_star_self U V hacute, mul_one]

/-- The adjoint of the acute Spectra direct rotation is onto. -/
theorem star_spectraDirectRotation_surjective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Surjective
      (star (spectraDirectRotation U V hacute) : H →L[𝕜] H) := by
  intro y
  refine ⟨spectraDirectRotation U V hacute y, ?_⟩
  have h := congrArg (fun T : H →L[𝕜] H => T y)
    (star_spectraDirectRotation_mul_self U V hacute)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- The adjoint of the acute Spectra direct rotation is one-to-one. -/
theorem star_spectraDirectRotation_injective
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Function.Injective
      (star (spectraDirectRotation U V hacute) : H →L[𝕜] H) := by
  intro x y hxy
  have hmap := congrArg (fun z => spectraDirectRotation U V hacute z) hxy
  have hx := congrArg (fun T : H →L[𝕜] H => T x)
    (spectraDirectRotation_mul_star_self U V hacute)
  have hy := congrArg (fun T : H →L[𝕜] H => T y)
    (spectraDirectRotation_mul_star_self U V hacute)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hx hy
  exact hx.symm.trans (hmap.trans hy)

/-- The adjoint carries the target subspace back onto the source subspace. -/
theorem star_spectraDirectRotation_maps_subspace
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    V.map ((star (spectraDirectRotation U V hacute) :
      H →L[𝕜] H).toLinearMap) = U := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (star_spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      V.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := star_spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    apply star_spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (star_spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      U.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-- The adjoint carries the target orthogonal complement back onto the source
orthogonal complement. -/
theorem star_spectraDirectRotation_maps_orthogonalComplement
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Vᗮ.map ((star (spectraDirectRotation U V hacute) :
      H →L[𝕜] H).toLinearMap) = Uᗮ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply Uᗮ.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (star_spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Vᗮ.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := star_spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply Vᗮ.starProjection_eq_self_iff.mp
    apply star_spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (star_spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Uᗮ.starProjection_eq_self_iff.mpr hy] at h
    exact h


/-! ## Reflection-product reduction for the square theorem -/

/-- A subspace reflection is self-adjoint in the complex bounded-operator
algebra. -/
theorem star_reflectionOperator_complex
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    star (U.reflectionOperator) = U.reflectionOperator := by
  rw [reflectionOperator_eq_projection_add_projection_sub_one]
  simp only [star_sub, star_add, star_one,
    (isSelfAdjoint_starProjection U).star_eq]

/-- A subspace reflection is a unitary element of the complex bounded-operator
algebra. -/
theorem reflectionOperator_mem_unitary_complex
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    U.reflectionOperator ∈ unitary (H →L[𝕜] H) := by
  have hstar : star (U.reflectionOperator) = U.reflectionOperator :=
    star_reflectionOperator_complex U
  have hinv : U.reflectionOperator * U.reflectionOperator = 1 := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      Submodule.reflectionOperator_involutive U
  exact ⟨by rw [hstar, hinv], by rw [hstar, hinv]⟩

omit [CompleteSpace H] in
/-- Reflections square to the identity in the bounded-operator algebra. -/
theorem reflectionOperator_mul_self_complex
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    U.reflectionOperator * U.reflectionOperator = 1 := by
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
    Submodule.reflectionOperator_involutive U

omit [CompleteSpace H] in
/-- Doubling identity: `C + C = 1 + Rᵥ Rᵤ`.  Because each reflection is degree
one in a single projection, this expands with no idempotent reduction. -/
theorem spectraCanonicalIntertwiner_add_self
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V =
      1 + V.reflectionOperator * U.reflectionOperator := by
  change
    (V.starProjection * U.starProjection +
          Vᗮ.starProjection * Uᗮ.starProjection) +
        (V.starProjection * U.starProjection +
          Vᗮ.starProjection * Uᗮ.starProjection) =
      1 + V.reflectionOperator * U.reflectionOperator
  rw [reflectionOperator_eq_projection_add_projection_sub_one U,
    reflectionOperator_eq_projection_add_projection_sub_one V,
    Submodule.starProjection_orthogonal' U, Submodule.starProjection_orthogonal' V]
  noncomm_ring

omit [CompleteSpace H] in
/-- Additive doubling is injective in a torsion-free bounded-operator algebra. -/
private theorem add_self_cancel_complex {w z : H →L[𝕜] H} (h : w + w = z + z) :
    w = z := by
  have hw : w + w = (2 : 𝕜) • w := by module
  have hz : z + z = (2 : 𝕜) • z := by module
  rw [hw, hz] at h
  exact smul_right_injective (H →L[𝕜] H) (by norm_num) h

omit [CompleteSpace H] in
/-- Additive quadrupling is injective in a torsion-free bounded-operator
algebra. -/
private theorem add_four_cancel_complex {w z : H →L[𝕜] H}
    (h : w + w + w + w = z + z + z + z) : w = z := by
  have hw : w + w + w + w = (4 : 𝕜) • w := by module
  have hz : z + z + z + z = (4 : 𝕜) • z := by module
  rw [hw, hz] at h
  exact smul_right_injective (H →L[𝕜] H) (by norm_num) h

/-- The canonical intertwiner `C = Q P + Qᗮ Pᗮ` is **normal**: `C⋆ C = C C⋆`.
Since `2 C = 1 + Rᵥ Rᵤ` is one plus a product of two reflections (a unitary),
both Gram products equal `2 + Rᵥ Rᵤ + Rᵤ Rᵥ` after clearing the factor of four,
forcing normality. -/
theorem spectraCanonicalIntertwiner_normal
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V =
      spectraCanonicalIntertwiner U V * star (spectraCanonicalIntertwiner U V) := by
  set C := spectraCanonicalIntertwiner U V with hCdef
  set a := U.reflectionOperator with hadef
  set b := V.reflectionOperator with hbdef
  have hRU : a * a = 1 := reflectionOperator_mul_self_complex U
  have hRV : b * b = 1 := reflectionOperator_mul_self_complex V
  have hGG' : (b * a) * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc a, hRU, one_mul, hRV]
  have hG'G : (a * b) * (b * a) = 1 := by
    rw [mul_assoc, ← mul_assoc b, hRV, one_mul, hRU]
  have hC : C + C = 1 + b * a := spectraCanonicalIntertwiner_add_self U V
  have hCs : star C + star C = 1 + a * b := by
    have h := congrArg star hC
    rwa [star_add, star_add, star_one, star_mul,
      star_reflectionOperator_complex U, star_reflectionOperator_complex V] at h
  refine add_four_cancel_complex ?_
  have e1 : star C * C + star C * C + star C * C + star C * C =
      (star C + star C) * (C + C) := by noncomm_ring
  have e2 : C * star C + C * star C + C * star C + C * star C =
      (C + C) * (star C + star C) := by noncomm_ring
  rw [e1, e2, hC, hCs]
  have hlhs : (1 + a * b) * (1 + b * a) = 1 + a * b + b * a + (a * b) * (b * a) := by
    noncomm_ring
  have hrhs : (1 + b * a) * (1 + a * b) = 1 + b * a + a * b + (b * a) * (a * b) := by
    noncomm_ring
  rw [hlhs, hrhs, hGG', hG'G]
  abel

/-- The canonical intertwiner satisfies `C + C⋆ = 2 C⋆C`; its Hermitian part is
its Gram operator.  With `2C = 1 + G`, `G = Rᵥ Rᵤ` unitary, both sides equal
`2 + G + G⋆`. -/
theorem spectraCanonicalIntertwiner_add_star
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V) =
      star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V +
        star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V := by
  set C := spectraCanonicalIntertwiner U V with hCdef
  set a := U.reflectionOperator with hadef
  set b := V.reflectionOperator with hbdef
  have hRU : a * a = 1 := reflectionOperator_mul_self_complex U
  have hRV : b * b = 1 := reflectionOperator_mul_self_complex V
  have hG'G : (a * b) * (b * a) = 1 := by
    rw [mul_assoc, ← mul_assoc b, hRV, one_mul, hRU]
  have hC : C + C = 1 + b * a := spectraCanonicalIntertwiner_add_self U V
  have hCs : star C + star C = 1 + a * b := by
    have h := congrArg star hC
    rwa [star_add, star_add, star_one, star_mul,
      star_reflectionOperator_complex U, star_reflectionOperator_complex V] at h
  refine add_self_cancel_complex ?_
  have eL : (C + star C) + (C + star C) = (C + C) + (star C + star C) := by abel
  have eR : (star C * C + star C * C) + (star C * C + star C * C) =
      (star C + star C) * (C + C) := by noncomm_ring
  rw [eL, eR, hC, hCs]
  have hprod : (1 + a * b) * (1 + b * a) = 1 + a * b + b * a + (a * b) * (b * a) := by
    noncomm_ring
  rw [hprod, hG'G]
  abel

/-- The Gram operator `C⋆C` commutes with the source projection `P`.  This
follows purely from the intertwining `C P = Q C` and its adjoint, with no
coordinate computation. -/
theorem commute_projection_spectraCanonicalIntertwiner_star_mul_self
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (U.starProjection)
      (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V) := by
  set C := spectraCanonicalIntertwiner U V with hCdef
  have h1 : C * U.starProjection = V.starProjection * C :=
    spectraCanonicalIntertwiner_mul_projection U V
  have h2 : star C * V.starProjection = U.starProjection * star C := by
    have h := congrArg star h1
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] at h
    exact h.symm
  change U.starProjection * (star C * C) = star C * C * U.starProjection
  rw [← mul_assoc, ← h2, mul_assoc, ← h1, ← mul_assoc]

/-- The ordered product of the target and source reflections.  The direct
rotation square theorem identifies this operator with the square of the polar
factor. -/
noncomputable abbrev spectraReflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  V.reflectionOperator * U.reflectionOperator

/-- The ordered reflection product is unitary. -/
theorem spectraReflectionProduct_mem_unitary
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraReflectionProduct U V ∈ unitary (H →L[𝕜] H) :=
  (unitary (H →L[𝕜] H)).mul_mem
    (reflectionOperator_mem_unitary_complex V)
    (reflectionOperator_mem_unitary_complex U)

omit [CompleteSpace H] in
/-- Twice the canonical intertwiner is the identity plus the ordered
reflection product.  Thus the pre-polar operator is the algebraic midpoint of
`1` and `J_V J_U`, without introducing division by two into later rewrites. -/
theorem spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V =
      1 + spectraReflectionProduct U V := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) +
      (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) =
      1 + V.reflectionOperator * U.reflectionOperator
  rw [show V.reflectionOperator =
      V.starProjection + V.starProjection - 1 by
        exact reflectionOperator_eq_projection_add_projection_sub_one V,
    show U.reflectionOperator =
      U.starProjection + U.starProjection - 1 by
        exact reflectionOperator_eq_projection_add_projection_sub_one U,
    Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  noncomm_ring

omit [CompleteSpace H] in
/-- The canonical intertwiner commutes with the ordered reflection product. -/
theorem spectraCanonicalIntertwiner_commute_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (spectraCanonicalIntertwiner U V)
      (spectraReflectionProduct U V) := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) *
      (V.reflectionOperator * U.reflectionOperator) =
    (V.reflectionOperator * U.reflectionOperator) *
      (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection)
  rw [show V.reflectionOperator =
      V.starProjection + V.starProjection - 1 by
        exact reflectionOperator_eq_projection_add_projection_sub_one V,
    show U.reflectionOperator =
      U.starProjection + U.starProjection - 1 by
        exact reflectionOperator_eq_projection_add_projection_sub_one U,
    Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  noncomm_ring

/-- The canonical intertwiner also commutes with the adjoint of the ordered
reflection product.  This follows from the midpoint identity and unitarity of
the reflection product, avoiding a second projection-polynomial expansion. -/
theorem spectraCanonicalIntertwiner_commute_star_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (spectraCanonicalIntertwiner U V)
      (star (spectraReflectionProduct U V)) := by
  let S : H →L[𝕜] H := spectraCanonicalIntertwiner U V
  let R : H →L[𝕜] H := spectraReflectionProduct U V
  have hmid : S + S = 1 + R :=
    spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hunit : R ∈ unitary (H →L[𝕜] H) :=
    spectraReflectionProduct_mem_unitary U V
  have hRstar : R * star R = 1 := hunit.2
  have hstarR : star R * R = 1 := hunit.1
  have hdouble : (S + S) * star R = star R * (S + S) := by
    rw [hmid]
    noncomm_ring [hRstar, hstarR]
  have hscaled : (2 : 𝕜) • (S * star R) = (2 : 𝕜) • (star R * S) := by
    simpa only [add_mul, mul_add, two_smul 𝕜] using hdouble
  let twoUnit : 𝕜ˣ := Units.mk0 2 (by norm_num)
  apply smul_left_cancel twoUnit
  change (2 : 𝕜) • (S * star R) = (2 : 𝕜) • (star R * S)
  exact hscaled

/-- The absolute value of the canonical intertwiner commutes with the ordered
reflection product.  This is the functional-calculus step that turns the
midpoint identity into a one-variable unitary problem. -/
theorem spectraCanonicalAbsoluteValue_commute_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V))
      (spectraReflectionProduct U V) := by
  change Commute (CFC.abs (spectraCanonicalIntertwiner U V))
    (spectraReflectionProduct U V)
  exact
    (spectraCanonicalIntertwiner_commute_reflectionProduct U V).cfcAbs_left
      (spectraCanonicalIntertwiner_commute_star_reflectionProduct U V)

/-- The inverse absolute-value unit commutes with the ordered reflection
product in the acute case. -/
theorem spectraCanonicalAbsoluteValueUnit_inv_commute_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Commute
      (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[𝕜] H)
      (spectraReflectionProduct U V) := by
  have h := spectraCanonicalAbsoluteValue_commute_reflectionProduct U V
  rw [← coe_spectraCanonicalAbsoluteValueUnit U V hacute] at h
  exact h.units_inv_left

/-- The acute canonical polar factor commutes with the ordered reflection
product. -/
theorem spectraCanonicalPolarFactor_commute_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Commute (spectraCanonicalPolarFactor U V)
      (spectraReflectionProduct U V) := by
  rw [spectraCanonicalPolarFactor_eq_intertwiner_mul_absoluteValueUnit_inv
    U V hacute]
  exact
    (spectraCanonicalIntertwiner_commute_reflectionProduct U V).mul_left
      (spectraCanonicalAbsoluteValueUnit_inv_commute_reflectionProduct
        U V hacute)

/-- The acute Spectra direct rotation commutes with the ordered reflection
product whose preferred square root it is intended to realize. -/
theorem spectraDirectRotation_commute_reflectionProduct
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    Commute (spectraDirectRotation U V hacute)
      (spectraReflectionProduct U V) :=
  spectraCanonicalPolarFactor_commute_reflectionProduct U V hacute

end DavisKahan
end TauCeti
