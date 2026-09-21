/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# Unitary transport of the domain-aware spectral vocabulary

`unitaryConj U A = U A U⁻¹` already exists for partial linear maps, together with
its domain description, its intertwining law and the transfer of
self-adjointness.  What was missing is that the rest of the unbounded spectral
vocabulary travels with it.

This module proves that a unitary equivalence transports

* the real resolvent set, hence the real spectrum, as an *equality* of sets;
* the two operator-form semibounds, in both directions;
* the reducing-subspace property, onto the image subspace;
* and the reducing restriction itself, as an *equality* of partial maps
  `A|U` conjugated by the restricted unitary and `(U A U⁻¹)|(U '' U)`.

The last one is the reason the module exists.  A reducing restriction is built
from a domain, a linear map and an invariance proof, so two restrictions of
visibly different operators are not interchangeable by `congr`; the equality has
to be proved once, and then every spectral hypothesis about the restriction can
be moved across the unitary by rewriting.

Everything is stated over an arbitrary `RCLike` scalar field and for a unitary
between two *different* Hilbert spaces, because that is what a restricted
unitary `U ≃ₗᵢ U.map W` is.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new reusable mathematics**.  Written for the ambient
  double-angle sine theorem, where the perturbed operator is the reflection
  conjugate of the unperturbed one and every spectral hypothesis has to cross
  that reflection.
* Spectra influence: none.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H H' : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-! ### Conjugating back -/

/-- Conjugating by `W` and then by `W⁻¹` returns the original partial map.  This
is what makes every transport statement below an equivalence rather than a
one-way implication. -/
theorem unitaryConj_symm_unitaryConj (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) :
    unitaryConj W.symm (unitaryConj W A) = A := by
  refine _root_.LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext x
    simp only [mem_unitaryConj_domain_iff, LinearIsometryEquiv.symm_symm,
      W.symm_apply_apply]
  · intro x hx _
    rw [unitaryConj_apply, unitaryConj_apply]
    simp only [LinearIsometryEquiv.symm_symm, W.symm_apply_apply]

/-! ### The real resolvent set and the real spectrum -/

/-- A real resolvent point of `A` is a real resolvent point of `W A W⁻¹`: the
inverse conjugates. -/
theorem mem_realResolventSet_unitaryConj_of_mem
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {lam : ℝ}
    (h : lam ∈ realResolventSet A) :
    lam ∈ realResolventSet (unitaryConj W A) := by
  obtain ⟨R, hleft, hright⟩ := mem_realResolventSet_iff.mp h
  refine mem_realResolventSet_iff.mpr
    ⟨W.toLinearIsometry.toContinuousLinearMap ∘L R ∘L
      W.symm.toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
  · intro x
    have hx : W.symm (x : H') ∈ A.domain := x.2
    have h := congrArg W (hleft ⟨W.symm (x : H'), hx⟩)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    rw [unitaryConj_apply]
    rw [(by rw [map_sub, map_smul, W.symm_apply_apply] :
      W.symm (W (A ⟨W.symm (x : H'), hx⟩) - (lam : 𝕜) • (x : H')) =
        A ⟨W.symm (x : H'), hx⟩ - (lam : 𝕜) • W.symm (x : H'))]
    rw [h, W.apply_symm_apply]
  · intro y
    have hy := hright (W.symm y)
    obtain ⟨hmem, heq⟩ := hy
    refine ⟨?_, ?_⟩
    · change W.symm (W (R (W.symm y))) ∈ A.domain
      rw [W.symm_apply_apply]
      exact hmem
    · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rw [unitaryConj_apply]
      have hcongr : (⟨W.symm (W (R (W.symm y))), by
            rw [W.symm_apply_apply]; exact hmem⟩ : A.domain) =
          ⟨R (W.symm y), hmem⟩ := Subtype.ext (W.symm_apply_apply _)
      rw [hcongr]
      rw [(map_smul W (lam : 𝕜) (R (W.symm y))).symm, ← map_sub, heq,
        W.apply_symm_apply]

/-- The real resolvent set is invariant under unitary conjugation. -/
theorem realResolventSet_unitaryConj (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) :
    realResolventSet (unitaryConj W A) = realResolventSet A := by
  ext lam
  refine ⟨fun h => ?_, mem_realResolventSet_unitaryConj_of_mem W⟩
  have h' := mem_realResolventSet_unitaryConj_of_mem W.symm h
  rwa [unitaryConj_symm_unitaryConj] at h'

/-- The real spectrum is invariant under unitary conjugation. -/
theorem realSpectrum_unitaryConj (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) :
    realSpectrum (unitaryConj W A) = realSpectrum A := by
  ext lam
  rw [mem_realSpectrum_iff, mem_realSpectrum_iff, realResolventSet_unitaryConj]

/-! ### Operator-form semibounds -/

/-- A lower form bound transports to the unitary conjugate. -/
theorem semiboundedBelow_unitaryConj_of
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {c : ℝ}
    (h : SemiboundedBelow A c) : SemiboundedBelow (unitaryConj W A) c := by
  rw [semiboundedBelow_iff] at h ⊢
  intro x
  have hx : W.symm (x : H') ∈ A.domain := x.2
  have hnorm : ‖(x : H')‖ = ‖W.symm (x : H')‖ := (W.symm.norm_map _).symm
  have hinner : ⟪(unitaryConj W A) x, (x : H')⟫_𝕜 =
      ⟪A ⟨W.symm (x : H'), hx⟩, W.symm (x : H')⟫_𝕜 := by
    rw [unitaryConj_apply]
    rw [← W.symm.inner_map_map (W (A ⟨W.symm (x : H'), hx⟩)) (x : H'),
      W.symm_apply_apply]
  rw [hnorm, hinner]
  exact h ⟨W.symm (x : H'), hx⟩

/-- An upper form bound transports to the unitary conjugate. -/
theorem semiboundedAbove_unitaryConj_of
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {c : ℝ}
    (h : SemiboundedAbove A c) : SemiboundedAbove (unitaryConj W A) c := by
  rw [semiboundedAbove_iff] at h ⊢
  intro x
  have hx : W.symm (x : H') ∈ A.domain := x.2
  have hnorm : ‖(x : H')‖ = ‖W.symm (x : H')‖ := (W.symm.norm_map _).symm
  have hinner : ⟪(unitaryConj W A) x, (x : H')⟫_𝕜 =
      ⟪A ⟨W.symm (x : H'), hx⟩, W.symm (x : H')⟫_𝕜 := by
    rw [unitaryConj_apply]
    rw [← W.symm.inner_map_map (W (A ⟨W.symm (x : H'), hx⟩)) (x : H'),
      W.symm_apply_apply]
  rw [hnorm, hinner]
  exact h ⟨W.symm (x : H'), hx⟩

/-- Lower form bounds are invariant under unitary conjugation. -/
theorem semiboundedBelow_unitaryConj_iff
    (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (c : ℝ) :
    SemiboundedBelow (unitaryConj W A) c ↔ SemiboundedBelow A c := by
  refine ⟨fun h => ?_, semiboundedBelow_unitaryConj_of W⟩
  have h' := semiboundedBelow_unitaryConj_of W.symm h
  rwa [unitaryConj_symm_unitaryConj] at h'

/-- Upper form bounds are invariant under unitary conjugation. -/
theorem semiboundedAbove_unitaryConj_iff
    (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (c : ℝ) :
    SemiboundedAbove (unitaryConj W A) c ↔ SemiboundedAbove A c := by
  refine ⟨fun h => ?_, semiboundedAbove_unitaryConj_of W⟩
  have h' := semiboundedAbove_unitaryConj_of W.symm h
  rwa [unitaryConj_symm_unitaryConj] at h'

/-! ### Reducing subspaces -/

section Reducing

variable (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (U : Submodule 𝕜 H)
  [U.HasOrthogonalProjection]

/-- The image subspace of a reducing subspace reduces the conjugated operator.

Both halves of `ReducesSubspace` transport for the same two reasons: the
orthogonal projection onto `U.map W` is `W ∘ P_U ∘ W⁻¹`
(`Submodule.starProjection_map_apply`) and the orthogonal complement of an image
is the image of the complement (`Submodule.map_orthogonal_equiv`). -/
theorem reducesSubspace_unitaryConj (hred : ReducesSubspace A U) :
    ReducesSubspace (unitaryConj W A)
      (U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) := by
  have hperp : (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))ᗮ =
      Uᗮ.map (W.toLinearEquiv : H →ₗ[𝕜] H') :=
    (Submodule.map_orthogonal_equiv U W).symm
  refine ReducesSubspace.of_components ?_ ?_ ?_ ?_
  · intro x
    rw [Submodule.starProjection_map_apply, mem_unitaryConj_domain_iff,
      W.symm_apply_apply]
    exact hred.projection_mem_domain ⟨W.symm (x : H'), x.2⟩
  · intro x
    rw [Submodule.starProjection_congr_apply hperp, Submodule.starProjection_map_apply,
      mem_unitaryConj_domain_iff, W.symm_apply_apply]
    exact hred.orthogonalProjection_mem_domain ⟨W.symm (x : H'), x.2⟩
  · intro x hx
    have hpre : W.symm (x : H') ∈ U := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hzz : W.symm (x : H') = z := by rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    rw [unitaryConj_apply]
    exact Submodule.mem_map.mpr
      ⟨A ⟨W.symm (x : H'), x.2⟩, hred.invariant ⟨W.symm (x : H'), x.2⟩ hpre, rfl⟩
  · intro x hx
    rw [hperp] at hx ⊢
    have hpre : W.symm (x : H') ∈ Uᗮ := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hzz : W.symm (x : H') = z := by rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    rw [unitaryConj_apply]
    exact Submodule.mem_map.mpr
      ⟨A ⟨W.symm (x : H'), x.2⟩,
        hred.orthogonal_invariant ⟨W.symm (x : H'), x.2⟩ hpre, rfl⟩

/-- The restriction of a unitary equivalence to a subspace and its image. -/
noncomputable def submoduleMapIsometry :
    U ≃ₗᵢ[𝕜] U.map (W.toLinearEquiv : H →ₗ[𝕜] H') where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := W.norm_map (x : H)

omit [U.HasOrthogonalProjection] in
/-- The restricted isometry acts by the ambient unitary. -/
@[simp] private theorem submoduleMapIsometry_coe_apply (x : U) :
    ((submoduleMapIsometry W U x :
      U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') = W (x : H) := rfl

omit [U.HasOrthogonalProjection] in
/-- Its inverse acts by the inverse unitary. -/
@[simp] private theorem submoduleMapIsometry_symm_coe_apply
    (x : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) :
    (((submoduleMapIsometry W U).symm x : U) : H) = W.symm (x : H') := rfl

/-- **The reducing restriction commutes with unitary conjugation.**

Restricting `W A W⁻¹` to the image subspace is the same partial map as
conjugating the restriction of `A` to `U` by the restricted unitary
`U ≃ₗᵢ U.map W`.  Both sides have domain `{x ∈ U.map W | W⁻¹ x ∈ dom A}` and both
send `x` to `W (A (W⁻¹ x))`, so this is an equality on the nose. -/
theorem reducingRestriction_unitaryConj (hred : ReducesSubspace A U) :
    reducingRestriction (unitaryConj W A) (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
        (reducesSubspace_unitaryConj W A U hred) =
      unitaryConj (submoduleMapIsometry W U) (reducingRestriction A U hred) := by
  refine _root_.LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext z
    rw [mem_reducingRestriction_domain_iff, mem_unitaryConj_domain_iff,
      mem_unitaryConj_domain_iff, mem_reducingRestriction_domain_iff,
      submoduleMapIsometry_symm_coe_apply]
  · rintro u hx hy
    apply Subtype.ext
    have hxA : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') ∈ A.domain :=
      (mem_reducingRestriction_domain_iff _ _ _ u).mp hx
    have hxU : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') ∈ U := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp u.2
      have hzz : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') = z := by
        rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    have hxD : (⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩ : U) ∈
        (reducingRestriction A U hred).domain :=
      (mem_reducingRestriction_domain_iff A U hred _).mpr hxA
    have hL : ((reducingRestriction (unitaryConj W A)
          (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
          (reducesSubspace_unitaryConj W A U hred) ⟨u, hx⟩ :
            U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') =
        W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) :=
      coe_reducingRestriction_apply (unitaryConj W A)
        (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
        (reducesSubspace_unitaryConj W A U hred) u hxA
    have hR : ((unitaryConj (submoduleMapIsometry W U)
          (reducingRestriction A U hred) ⟨u, hy⟩ :
            U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') =
        W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
      have hstep : ((reducingRestriction A U hred
            ⟨⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩,
              hxD⟩ : U) : H) =
          A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩ :=
        coe_reducingRestriction_apply A U hred
          ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩ hxA
      calc ((unitaryConj (submoduleMapIsometry W U)
            (reducingRestriction A U hred) ⟨u, hy⟩ :
              U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H')
          = W (((reducingRestriction A U hred
              ⟨⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩,
                hxD⟩ : U) : H)) := rfl
        _ = W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
              rw [hstep]
    rw [hL, hR]

end Reducing

end LinearPMap
end TauCeti
