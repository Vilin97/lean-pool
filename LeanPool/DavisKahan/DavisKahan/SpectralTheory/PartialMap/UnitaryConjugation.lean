/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Unitary conjugation for unbounded operators

This module states unitary conjugation for a partial map `H →ₗ.[ℂ] H`.  The source and target Hilbert spaces may differ, which is important
when conjugating operators restricted to spectral subspaces.  The construction
came from the vendored Spectra package, retired on 2026-07-29; it is now built
on Mathlib's `LinearPMap`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u v

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugate a self-adjoint partial map by a linear isometry equivalence.

The self-adjointness hypothesis is not used by the construction -- `unitaryConj`
transports any partial map -- but it is retained so that this name and
`unitaryConjugate_isSelfAdjoint` take the same arguments at every call site. -/
noncomputable def unitaryConjugate
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (_hA : IsSelfAdjoint A) : K →ₗ.[ℂ] K :=
  TauCeti.LinearPMap.unitaryConj W A

omit [CompleteSpace K] in
/-- The domain of a unitary conjugate is the image of the original domain. -/
@[simp] theorem unitaryConjugate_domain
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    (unitaryConjugate W A hA).domain =
      A.domain.comap (W.symm.toLinearEquiv : K →ₗ[ℂ] H) := rfl

omit [CompleteSpace K] in
/-- Membership in the transported domain is the expected inverse-image
condition. -/
theorem mem_unitaryConjugate_domain_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {x : K} :
    x ∈ (unitaryConjugate W A hA).domain ↔ W.symm x ∈ A.domain := Iff.rfl

omit [CompleteSpace K] in
/-- The transported domain is also the direct image of the original domain. -/
theorem unitaryConjugate_domain_eq_map
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    (unitaryConjugate W A hA).domain =
      A.domain.map (W.toLinearEquiv : H →ₗ[ℂ] K) := by
  ext x
  constructor
  · intro hx
    refine ⟨W.symm x, hx, ?_⟩
    exact W.apply_symm_apply x
  · rintro ⟨z, hz, rfl⟩
    change W.symm (W z) ∈ A.domain
    simpa using hz

omit [CompleteSpace K] in
/-- The unitary conjugate acts by transporting, applying, and transporting back. -/
@[simp] theorem unitaryConjugate_apply
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : (unitaryConjugate W A hA).domain) :
    (unitaryConjugate W A hA) x =
      W (A ⟨W.symm (x : K), x.property⟩) := rfl

omit [CompleteSpace K] in
/-- The unitary sends every original-domain vector into the transported
 domain. -/
theorem unitaryConjugate_map_mem_domain
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : A.domain) :
    W (x : H) ∈ (unitaryConjugate W A hA).domain := by
  rw [mem_unitaryConjugate_domain_iff, W.symm_apply_apply]
  exact x.property

omit [CompleteSpace K] in
/-- Conjugation acts by the expected formula on transported domain vectors. -/
theorem unitaryConjugate_apply_map
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : A.domain) :
    (unitaryConjugate W A hA)
        ⟨W (x : H), unitaryConjugate_map_mem_domain W A hA x⟩ =
      W (A x) := by
  rw [unitaryConjugate_apply]
  congr 1
  exact congrArg A
    (Subtype.ext (W.symm_apply_apply (x : H)))

/-- Transport a bounded operator through a unitary equivalence. -/
noncomputable def unitaryConjugateBounded
    (W : H ≃ₗᵢ[ℂ] K) (R : H →L[ℂ] H) : K →L[ℂ] K :=
  W.toLinearIsometry.toContinuousLinearMap ∘L R ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace H] [CompleteSpace K] in
/-- The bounded unitary conjugate, unfolded. -/
@[simp] theorem unitaryConjugateBounded_apply
    (W : H ≃ₗᵢ[ℂ] K) (R : H →L[ℂ] H) (x : K) :
    unitaryConjugateBounded W R x = W (R (W.symm x)) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- A resolvent of a partial operator transports to its unitary conjugate. -/
theorem mem_resolventSet_unitaryConj_of_mem
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) {z : ℂ}
    (hz : z ∈ TauCeti.LinearPMap.resolventSet A) :
    z ∈ TauCeti.LinearPMap.resolventSet
      (TauCeti.LinearPMap.unitaryConj W A) := by
  obtain ⟨R, hR⟩ := hz
  -- `IsResolventAt` has three fields: the domain condition, the right inverse, and the
  -- left inverse.  Each transports by conjugating with `W`.
  refine ⟨unitaryConjugateBounded W R, fun φ => ?_, fun φ => ?_, fun ψ => ?_⟩
  · rw [unitaryConjugateBounded_apply,
      TauCeti.LinearPMap.mem_unitaryConj_domain_iff, W.symm_apply_apply]
    exact hR.mem_domain _
  · have hφ := congrArg W (hR.smul_sub_apply (W.symm φ))
    simpa only [TauCeti.LinearPMap.unitaryConj_apply,
      unitaryConjugateBounded_apply, map_sub, map_smul,
      W.symm_apply_apply, W.apply_symm_apply] using hφ
  · let x : A.domain := ⟨W.symm (ψ : K), ψ.property⟩
    have hx := congrArg W (hR.apply_smul_sub x)
    simpa only [x, unitaryConjugateBounded_apply,
      TauCeti.LinearPMap.unitaryConj_apply, map_sub, map_smul,
      W.symm_apply_apply, W.apply_symm_apply] using hx

omit [CompleteSpace H] [CompleteSpace K] in
/-- Conjugation first by `W` and then by `W⁻¹` returns the original partial
operator. -/
theorem unitaryConj_symm_unitaryConj
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) :
    TauCeti.LinearPMap.unitaryConj W.symm
        (TauCeti.LinearPMap.unitaryConj W A) = A := by
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext x
    simp only [TauCeti.LinearPMap.mem_unitaryConj_domain_iff,
      LinearIsometryEquiv.symm_symm, W.symm_apply_apply]
  · intro x hx hy
    rw [TauCeti.LinearPMap.unitaryConj_apply,
      TauCeti.LinearPMap.unitaryConj_apply]
    simp only [LinearIsometryEquiv.symm_symm, W.symm_apply_apply]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Resolvent membership is invariant under unitary conjugation. -/
theorem mem_resolventSet_unitaryConj_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) {z : ℂ} :
    z ∈ TauCeti.LinearPMap.resolventSet
        (TauCeti.LinearPMap.unitaryConj W A) ↔
      z ∈ TauCeti.LinearPMap.resolventSet A := by
  constructor
  · intro hz
    have hz' := mem_resolventSet_unitaryConj_of_mem
      W.symm (TauCeti.LinearPMap.unitaryConj W A) hz
    rwa [unitaryConj_symm_unitaryConj W A] at hz'
  · exact mem_resolventSet_unitaryConj_of_mem W A

omit [CompleteSpace K] in
/-- A resolvent of the original DK operator transports to a resolvent of the
unitarily conjugated DK operator. -/
theorem mem_resolventSet_unitaryConjugate_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {z : ℂ} :
    z ∈ TauCeti.LinearPMap.resolventSet
        (unitaryConjugate W A hA) ↔
      z ∈ TauCeti.LinearPMap.resolventSet A := by
  change z ∈ TauCeti.LinearPMap.resolventSet
      (TauCeti.LinearPMap.unitaryConj W A) ↔
    z ∈ TauCeti.LinearPMap.resolventSet A
  exact mem_resolventSet_unitaryConj_iff W A

/-- The conjugated DK operator is self-adjoint. -/
theorem unitaryConjugate_isSelfAdjoint
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) : _root_.IsSelfAdjoint (unitaryConjugate W A hA) := by
  change IsSelfAdjoint (TauCeti.LinearPMap.unitaryConj W A)
  exact TauCeti.LinearPMap.isSelfAdjoint_unitaryConj hA

omit [CompleteSpace K] in
/-- The real spectrum is invariant under unitary conjugation. -/
theorem unitaryConjugate_spectrum_eq
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    TauCeti.LinearPMap.spectrum (unitaryConjugate W A hA) =
      TauCeti.LinearPMap.spectrum A := by
  ext lam
  change ((lam : ℂ) ∉ TauCeti.LinearPMap.resolventSet
      (unitaryConjugate W A hA)) ↔
    ((lam : ℂ) ∉ TauCeti.LinearPMap.resolventSet A)
  exact not_congr (mem_resolventSet_unitaryConjugate_iff W A hA)

/-- Restriction of an ambient unitary to a submodule and its transported
image.  This same-ambient-space form is exactly what reflection transport
needs; it does not impose completeness on an arbitrary submodule. -/
noncomputable def unitarySubmoduleMapIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) :
    U ≃ₗᵢ[ℂ] U.map (W.toLinearEquiv : E →ₗ[ℂ] E) where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := by
    have hcoe :
        (((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)) = W (x : E) := rfl
    rw [show ‖W.toLinearEquiv.submoduleMap U x‖ =
        ‖((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)‖ from rfl,
      hcoe, W.norm_map]
    rfl

/-- The induced submodule isometry acts as the underlying map. -/
@[simp] theorem unitarySubmoduleMapIsometry_coe_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) (x : U) :
    ((unitarySubmoduleMapIsometry W U x :
      U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) = W (x : E) := rfl

/-- Its inverse acts as the inverse map. -/
@[simp] theorem unitarySubmoduleMapIsometry_symm_coe_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E)
    (x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
    (((unitarySubmoduleMapIsometry W U).symm x : U) : E) = W.symm (x : E) := rfl


end DavisKahan
end TauCeti
