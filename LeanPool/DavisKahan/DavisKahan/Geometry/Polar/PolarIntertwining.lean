/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Polar factors and reducing projections

This file isolates the functional-analytic facts used by the nonacute
Davis--Kahan direct rotation.  The key principle is that an intertwining
relation `T P = Q T`, together with the adjoint relation, passes from `T` to
its polar partial isometry.  The proof is carried out first on `range |T|`,
then on its closure, and finally on the orthogonal complement, where the polar
factor vanishes.
-/

open scoped InnerProductSpace InnerProduct

namespace TauCeti
namespace DavisKahan

open DavisKahan.Foundation

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


/-- A self-adjoint projection commuting with `|T|` preserves the initial polar
space. -/
theorem polarInitial_invariant_of_commute_modulus
    (T P : H →L[𝕜] H)
    (hcomm : T.modulus ∘L P = P ∘L T.modulus)
    {x : H} (hx : x ∈ T.polarInitial) : P x ∈ T.polarInitial := by
  let M : Submodule 𝕜 H := Submodule.comap (P : H →ₗ[𝕜] H) (T.polarInitial)
  have hMclosed : IsClosed (M : Set H) := by
    have hcl : IsClosed ((T.polarInitial : Set H)) := by
      rw [ContinuousLinearMap.polarInitial]
      exact Submodule.isClosed_topologicalClosure _
    exact hcl.preimage P.continuous
  have hrange : LinearMap.range (T.modulus).toLinearMap ≤ M := by
    rintro y ⟨z, rfl⟩
    change P (T.modulus z) ∈ T.polarInitial
    have hpoint := DFunLike.congr_fun hcomm z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpoint
    rw [← hpoint]
    exact T.modulus_apply_mem_polarInitial (P z)
  have hclosure : T.polarInitial ≤ M := by
    rw [ContinuousLinearMap.polarInitial]
    exact Submodule.topologicalClosure_minimal _ hrange hMclosed
  exact hclosure hx

/-- If a self-adjoint projection preserves the initial polar space, it also
preserves its orthogonal complement. -/
theorem polarInitial_orthogonal_invariant_of_selfAdjoint
    (T P : H →L[𝕜] H) (hP : IsSelfAdjoint P)
    (hpres : ∀ x ∈ T.polarInitial, P x ∈ T.polarInitial)
    {x : H} (hx : x ∈ (T.polarInitial)ᗮ) : P x ∈ (T.polarInitial)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hP.star_eq
  rw [hPadj]
  exact hx (P y) (hpres y hy)

/-- The absolute value commutes with the initial projection whenever `T`
intertwines two orthogonal projections. -/
theorem modulus_commutes_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    T.modulus ∘L P = P ∘L T.modulus := by
  have hPsa : IsSelfAdjoint P := LinearMap.IsSymmetric.isSelfAdjoint hP.2
  have hQsa : IsSelfAdjoint Q := LinearMap.IsSymmetric.isSelfAdjoint hQ.2
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hPsa.star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q :=
    (ContinuousLinearMap.star_eq_adjoint Q).symm.trans hQsa.star_eq
  have hstar : P ∘L T† = T† ∘L Q := by
    have h := congrArg ContinuousLinearMap.adjoint hTP
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hPadj, hQadj] at h
    exact h
  have hgram : (T† ∘L T) ∘L P = P ∘L (T† ∘L T) := by
    calc
      (T† ∘L T) ∘L P = T† ∘L (T ∘L P) := by
        ext x
        rfl
      _ = T† ∘L (Q ∘L T) := by rw [hTP]
      _ = (T† ∘L Q) ∘L T := by
        ext x
        rfl
      _ = (P ∘L T†) ∘L T := by rw [← hstar]
      _ = P ∘L (T† ∘L T) := by
        ext x
        rfl
  have hcomm : Commute (star T * T) P := by
    have hmul : (star T * T) * P = P * (star T * T) := by
      simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact hgram
    exact hmul
  simpa [ContinuousLinearMap.mul_def] using
    (ContinuousLinearMap.commute_modulus_of_commute_star_mul_self T P hcomm).eq

/-- The polar partial isometry intertwines the same two projections as the
original operator. -/
theorem polarPartial_intertwines_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    T.polarPartial ∘L P = Q ∘L T.polarPartial := by
  have habs : T.modulus ∘L P = P ∘L T.modulus :=
    modulus_commutes_of_projection_intertwining T P Q hP hQ hTP
  have hpres : ∀ x ∈ T.polarInitial, P x ∈ T.polarInitial :=
    fun x hx => polarInitial_invariant_of_commute_modulus T P habs hx
  have hPsa : IsSelfAdjoint P := LinearMap.IsSymmetric.isSelfAdjoint hP.2
  have hpresOrth : ∀ x ∈ (T.polarInitial)ᗮ, P x ∈ (T.polarInitial)ᗮ :=
    fun x hx => polarInitial_orthogonal_invariant_of_selfAdjoint T P hPsa hpres hx
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨m, hm, hmk⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := T.polarInitial) x
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ (T.polarInitial)ᗮ, x = m + k :=
    ⟨x - m, hmk, by abel⟩
  have hUk : T.polarPartial k = 0 := by
    rw [ContinuousLinearMap.polarPartial_apply]
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hk]
    simp
  have hUPk : T.polarPartial (P k) = 0 := by
    rw [ContinuousLinearMap.polarPartial_apply]
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (hpresOrth k hk)]
    simp
  simp only [ContinuousLinearMap.comp_apply, map_add, hUk, hUPk, map_zero,
    add_zero]
  have heqOnDense :
      T.polarInitialMap ((T.polarInitial).orthogonalProjectionOnto (P m)) =
        Q (T.polarInitialMap ((T.polarInitial).orthogonalProjectionOnto m)) := by
    let f : T.polarInitial →L[𝕜] H :=
      T.polarInitialMap ∘L
        (P ∘L (T.polarInitial).subtypeL).codRestrict
          (T.polarInitial) (fun z => hpres z z.property)
    let g : T.polarInitial →L[𝕜] H := Q ∘L T.polarInitialMap
    have hfg : f = g := by
      apply DFunLike.coe_injective
      apply DenseRange.equalizer T.denseRange_modulusCorestrict
        f.continuous g.continuous
      funext z
      change T.polarInitialMap
          ⟨P (T.modulus z), hpres _ (T.modulus_apply_mem_polarInitial z)⟩ =
        Q (T.polarInitialMap (T.modulusCorestrict z))
      have hpabs := DFunLike.congr_fun habs z
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpabs
      have hleft :
          (⟨P (T.modulus z), hpres _ (T.modulus_apply_mem_polarInitial z)⟩ : T.polarInitial) =
            T.modulusCorestrict (P z) := by
        apply Subtype.ext
        simpa using hpabs.symm
      rw [hleft, ContinuousLinearMap.polarInitialMap_modulusCorestrict,
        ContinuousLinearMap.polarInitialMap_modulusCorestrict]
      exact DFunLike.congr_fun hTP z
    have hmproj : (T.polarInitial).orthogonalProjectionOnto m = ⟨m, hm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hm
    have hPm : P m ∈ T.polarInitial := hpres m hm
    have hPmproj : (T.polarInitial).orthogonalProjectionOnto (P m) = ⟨P m, hPm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hPm
    have hcodeq :
        ((P ∘L (T.polarInitial).subtypeL).codRestrict (T.polarInitial)
            (fun z => hpres z z.property)) ⟨m, hm⟩ = (⟨P m, hPm⟩ : T.polarInitial) := by
      apply Subtype.ext
      -- `simp` no longer takes the `codRestrict` coercion step; it is definitional.
      rfl
    have hkey := DFunLike.congr_fun hfg ⟨m, hm⟩
    simp only [f, g, ContinuousLinearMap.comp_apply, hcodeq] at hkey
    rw [hmproj, hPmproj]
    exact hkey
  simpa [ContinuousLinearMap.polarPartial_apply] using heqOnDense

/-- The polar factor of the canonical two-projection intertwiner intertwines
both projections without an acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalPolarFactor U V ∘L U.starProjection =
      V.starProjection ∘L spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor]
  apply polarPartial_intertwines_of_projection_intertwining
  · exact ⟨U.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection U).isSymmetric⟩
  · exact ⟨V.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection V).isSymmetric⟩
  · simpa [ContinuousLinearMap.mul_def] using
      spectraCanonicalIntertwiner_mul_projection U V

/-- Taking adjoints exchanges the ordered pair of subspaces in the canonical
polar factor. -/
theorem canonicalPolarFactor_adjoint_swap_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalPolarFactor U V) =
      spectraCanonicalPolarFactor V U := by
  rw [spectraCanonicalPolarFactor, spectraCanonicalPolarFactor,
    ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.polarPartial_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, star_spectraCanonicalIntertwiner]

end

end DavisKahan
end TauCeti
