/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# The spectrum of a reduced partial map is covered by its blocks

The unbounded counterpart of `realSpectrum_subset_union_of_reduces`, which the
bounded Section 8 development uses to turn Theorem 8.2's two printed *block*
spectral placements into the ambient placement its proof consumes.

The argument is the direct sum of the two block resolvents: if `lam` inverts both
blocks, the operator `ι_U R₁ P_U + ι_{Uᗮ} R₂ P_{Uᗮ}` inverts `A − lam`, because
`A` acts blockwise on a reducing decomposition.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **A reducing projection commutes with the operator on its domain.** -/
theorem starProjection_apply_eq_of_reduces
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (x : A.domain) :
    U.starProjection (A x) =
      A ⟨U.starProjection (x : E), hred.projection_mem_domain x⟩ := by
  obtain ⟨a, ha, hadef⟩ : ∃ a, ∃ h : a ∈ A.domain, a = U.starProjection (x : E) :=
    ⟨_, hred.projection_mem_domain x, rfl⟩
  obtain ⟨b, hb, hbdef⟩ : ∃ b, ∃ h : b ∈ A.domain, b = Uᗮ.starProjection (x : E) :=
    ⟨_, hred.orthogonalProjection_mem_domain x, rfl⟩
  have haU : a ∈ U := hadef ▸ U.starProjection_apply_mem _
  have hbU : b ∈ Uᗮ := hbdef ▸ Uᗮ.starProjection_apply_mem _
  have hsplit : (x : E) = a + b := by
    rw [hadef, hbdef, Submodule.starProjection_orthogonal_apply]
    abel
  have hxeq : x = (⟨a, ha⟩ : A.domain) + ⟨b, hb⟩ := Subtype.ext hsplit
  have hgoal : U.starProjection (A x) = A ⟨a, ha⟩ := by
    rw [hxeq, _root_.LinearPMap.map_add, map_add]
    have h1 : U.starProjection (A (⟨a, ha⟩ : A.domain)) = A ⟨a, ha⟩ :=
      Submodule.starProjection_eq_self_iff.mpr (hred.invariant ⟨a, ha⟩ haU)
    have h2 : U.starProjection (A (⟨b, hb⟩ : A.domain)) = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hred.orthogonal_invariant ⟨b, hb⟩ hbU
    rw [h1, h2, add_zero]
  rw [hgoal]
  congr 1
  exact Subtype.ext hadef

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
noncomputable local instance instCompleteSpaceCoeReducing
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

omit [CompleteSpace E] in
/-- **The real spectrum of a reduced partial map is covered by its two blocks.**

The unbounded counterpart of the bounded `realSpectrum_subset_union_of_reduces`.
If `lam` inverts both blocks, the direct sum of the two block inverses inverts
`A - lam`, because `A` acts blockwise on a reducing decomposition. -/
theorem realSpectrum_subset_union_of_reduces
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
    TauCeti.LinearPMap.realSpectrum A ⊆
      TauCeti.LinearPMap.realSpectrum
          (TauCeti.LinearPMap.reducingRestriction A U hred) ∪
        TauCeti.LinearPMap.realSpectrum
          (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) := by
  intro lam hlam
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, not_not] at h1 h2
  obtain ⟨R1, hL1, hRt1⟩ := h1
  obtain ⟨R2, hL2, hRt2⟩ := h2
  refine hlam ?_
  refine ⟨U.subtypeL ∘L R1 ∘L U.orthogonalProjectionOnto
    + Uᗮ.subtypeL ∘L R2 ∘L Uᗮ.orthogonalProjectionOnto, ?_, ?_⟩
  · -- left inverse
    intro x
    obtain ⟨a, ha, hadef⟩ : ∃ a, ∃ h : a ∈ A.domain, a = U.starProjection (x : E) :=
      ⟨_, hred.projection_mem_domain x, rfl⟩
    obtain ⟨b, hb, hbdef⟩ : ∃ b, ∃ h : b ∈ A.domain, b = Uᗮ.starProjection (x : E) :=
      ⟨_, hred.orthogonalProjection_mem_domain x, rfl⟩
    have haU : a ∈ U := hadef ▸ U.starProjection_apply_mem _
    have hbU : b ∈ Uᗮ := hbdef ▸ Uᗮ.starProjection_apply_mem _
    -- the `U` leg
    have hUdom : (⟨a, haU⟩ : U) ∈ (TauCeti.LinearPMap.reducingRestriction A U hred).domain := ha
    have hUleg := hL1 ⟨⟨a, haU⟩, hUdom⟩
    have hUproj : U.orthogonalProjectionOnto (A x - (lam : 𝕜) • (x : E))
        = (TauCeti.LinearPMap.reducingRestriction A U hred) ⟨⟨a, haU⟩, hUdom⟩
          - (lam : 𝕜) • (⟨a, haU⟩ : U) := by
      refine Subtype.ext ?_
      have hcomm := starProjection_apply_eq_of_reduces hred x
      show U.starProjection (A x - (lam : 𝕜) • (x : E)) = _
      rw [map_sub, hcomm, map_smul]
      show (A ⟨U.starProjection (x : E), hred.projection_mem_domain x⟩ : E)
        - (lam : 𝕜) • U.starProjection (x : E) = (A ⟨a, ha⟩ : E) - (lam : 𝕜) • a
      have hsub : (⟨U.starProjection (x : E), hred.projection_mem_domain x⟩ : A.domain)
          = ⟨a, ha⟩ := Subtype.ext hadef.symm
      rw [hsub, ← hadef]
    -- the `Uᗮ` leg
    have hVdom : (⟨b, hbU⟩ : Uᗮ) ∈
        (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal).domain := hb
    have hVleg := hL2 ⟨⟨b, hbU⟩, hVdom⟩
    have hVproj : Uᗮ.orthogonalProjectionOnto (A x - (lam : 𝕜) • (x : E))
        = (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) ⟨⟨b, hbU⟩, hVdom⟩
          - (lam : 𝕜) • (⟨b, hbU⟩ : Uᗮ) := by
      refine Subtype.ext ?_
      have hcomm := starProjection_apply_eq_of_reduces hred.orthogonal x
      show Uᗮ.starProjection (A x - (lam : 𝕜) • (x : E)) = _
      rw [map_sub, hcomm, map_smul]
      show (A ⟨Uᗮ.starProjection (x : E), hred.orthogonal.projection_mem_domain x⟩ : E)
        - (lam : 𝕜) • Uᗮ.starProjection (x : E) = (A ⟨b, hb⟩ : E) - (lam : 𝕜) • b
      have hsub : (⟨Uᗮ.starProjection (x : E), hred.orthogonal.projection_mem_domain x⟩
          : A.domain) = ⟨b, hb⟩ := Subtype.ext hbdef.symm
      rw [hsub, ← hbdef]
    show (U.subtypeL (R1 (U.orthogonalProjectionOnto (A x - (lam : 𝕜) • (x : E)))) : E)
      + (Uᗮ.subtypeL (R2 (Uᗮ.orthogonalProjectionOnto (A x - (lam : 𝕜) • (x : E)))) : E)
      = (x : E)
    rw [hUproj, hVproj, hUleg, hVleg]
    show a + b = (x : E)
    rw [hadef, hbdef, Submodule.starProjection_orthogonal_apply]
    abel
  · -- right inverse
    intro y
    obtain ⟨hu, hueq⟩ := hRt1 (U.orthogonalProjectionOnto y)
    obtain ⟨hv, hveq⟩ := hRt2 (Uᗮ.orthogonalProjectionOnto y)
    have hua : ((R1 (U.orthogonalProjectionOnto y) : U) : E) ∈ A.domain := hu
    have hvb : ((R2 (Uᗮ.orthogonalProjectionOnto y) : Uᗮ) : E) ∈ A.domain := hv
    have hmem : (U.subtypeL (R1 (U.orthogonalProjectionOnto y)) : E)
        + (Uᗮ.subtypeL (R2 (Uᗮ.orthogonalProjectionOnto y)) : E) ∈ A.domain :=
      A.domain.add_mem hua hvb
    refine ⟨hmem, ?_⟩
    have hadd : A ⟨(U.subtypeL (R1 (U.orthogonalProjectionOnto y)) : E)
          + (Uᗮ.subtypeL (R2 (Uᗮ.orthogonalProjectionOnto y)) : E), hmem⟩
        = A ⟨((R1 (U.orthogonalProjectionOnto y) : U) : E), hua⟩
          + A ⟨((R2 (Uᗮ.orthogonalProjectionOnto y) : Uᗮ) : E), hvb⟩ := by
      rw [← _root_.LinearPMap.map_add]
      congr 1
    have hueq' : (A ⟨((R1 (U.orthogonalProjectionOnto y) : U) : E), hua⟩ : E)
        - (lam : 𝕜) • ((R1 (U.orthogonalProjectionOnto y) : U) : E)
        = U.starProjection y := congrArg (fun z : U => (z : E)) hueq
    have hveq' : (A ⟨((R2 (Uᗮ.orthogonalProjectionOnto y) : Uᗮ) : E), hvb⟩ : E)
        - (lam : 𝕜) • ((R2 (Uᗮ.orthogonalProjectionOnto y) : Uᗮ) : E)
        = Uᗮ.starProjection y := congrArg (fun z : Uᗮ => (z : E)) hveq
    show (A ⟨_, hmem⟩ : E) - (lam : 𝕜) •
      (((R1 (U.orthogonalProjectionOnto y) : U) : E)
        + ((R2 (Uᗮ.orthogonalProjectionOnto y) : Uᗮ) : E)) = y
    rw [hadd, smul_add]
    have hsum : U.starProjection y + Uᗮ.starProjection y = y := by
      rw [Submodule.starProjection_orthogonal_apply]; abel
    linear_combination (norm := module) hueq' + hveq' + hsum

/-! ## Invariance plus self-adjointness gives reduction

The unbounded counterpart of `reduces_orthogonalComplement`.  The complement's
invariance is not assumed: it follows from symmetry, because the projection
preserves the domain and therefore `U.starProjection '' dom A` is dense in `U`. -/

/-- **The complement of an invariant subspace of a self-adjoint partial map is
invariant**, provided the projection preserves the domain. -/
theorem invariantSubspace_orthogonal_of_isSelfAdjoint
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (hproj : ∀ x : A.domain, U.starProjection (x : E) ∈ A.domain)
    (hinv : TauCeti.LinearPMap.InvariantSubspace A U) :
    TauCeti.LinearPMap.InvariantSubspace A Uᗮ := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hcont : Continuous fun w : E => (inner 𝕜 w (A x) : 𝕜) := by fun_prop
  have hzero : Set.EqOn (fun w : E => (inner 𝕜 w (A x) : 𝕜)) (fun _ => (0 : 𝕜))
      (U.starProjection '' (A.domain : Set E)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyd : U.starProjection y ∈ A.domain := hproj ⟨y, hy⟩
    have hval := hsym ⟨U.starProjection y, hyd⟩ x
    have hmemU : A (⟨U.starProjection y, hyd⟩ : A.domain) ∈ U :=
      hinv ⟨U.starProjection y, hyd⟩ (U.starProjection_apply_mem y)
    have hperp : (inner 𝕜 (A (⟨U.starProjection y, hyd⟩ : A.domain)) (x : E) : 𝕜) = 0 :=
      (Submodule.mem_orthogonal U (x : E)).mp hx _ hmemU
    show (inner 𝕜 (U.starProjection y) (A x) : 𝕜) = 0
    rw [← hval]
    exact hperp
  have hsub : (U : Set E) ⊆ closure (U.starProjection '' (A.domain : Set E)) := by
    intro w hw
    have himg : U.starProjection '' (closure (A.domain : Set E)) ⊆
        closure (U.starProjection '' (A.domain : Set E)) :=
      image_closure_subset_closure_image (U.starProjection.continuous)
    rw [hA.dense_domain.closure_eq] at himg
    refine himg ⟨w, Set.mem_univ w, ?_⟩
    exact Submodule.starProjection_eq_self_iff.mpr hw
  have := (hzero.closure hcont continuous_const) (hsub hu)
  exact this

/-- **Invariance plus self-adjointness gives reduction.** -/
theorem reducesSubspace_of_isSelfAdjoint_of_invariant
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (hproj : ∀ x : A.domain, U.starProjection (x : E) ∈ A.domain)
    (hinv : TauCeti.LinearPMap.InvariantSubspace A U) :
    TauCeti.LinearPMap.ReducesSubspace A U := by
  have hperp : ∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain := by
    intro x
    have h : Uᗮ.starProjection (x : E) = (x : E) - U.starProjection (x : E) :=
      Submodule.starProjection_orthogonal_apply U (x : E)
    rw [h]
    exact A.domain.sub_mem x.2 (hproj x)
  exact TauCeti.LinearPMap.ReducesSubspace.of_components hproj hperp hinv
    (invariantSubspace_orthogonal_of_isSelfAdjoint hA hproj hinv)

end DavisKahan
end TauCeti
