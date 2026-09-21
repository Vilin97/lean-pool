/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PartialIsometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularPartialIsometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The polar decomposition of a bounded operator

Every bounded operator `M : E →L[𝕜] F` between Hilbert spaces factors as

```
M = M.polarPartial ∘L |M|
```

with `|M| = M.modulus` positive and `M.polarPartial` a **partial isometry**: isometric on
the closure of the range of `|M|` and zero on its orthogonal complement.  Unlike
`ContinuousLinearMap.polarIsometryOfIsUnitModulus`, which inverts `|M|` and therefore needs
`|M|` to be
invertible, this holds for *every* `M` with no side condition.

## The construction

The whole decomposition rests on one identity, `ContinuousLinearMap.norm_modulus_apply`:

```
‖ |M| x ‖ = ‖ M x ‖.
```

Read from left to right it says the assignment `|M| x ↦ M x` is well defined — if
`|M| x = |M| y` then `‖M (x - y)‖ = ‖ |M| (x - y) ‖ = 0` — and read as an equation it says
that assignment is an isometry.  So there is an isometry from `range |M|` into `F`, and
`range |M|` is dense in the closed subspace `polarInitial M`.  Extending it by continuity
(`LinearMap.extendOfNorm`) and precomposing with the orthogonal projection onto that
subspace gives `polarPartial`.

## Main definitions and results

* `ContinuousLinearMap.polarInitial`: the **initial space**, the closure of `range |M|`;
* `ContinuousLinearMap.polarPartial`: the partial isometry;
* `ContinuousLinearMap.polarPartial_comp_modulus`: the polar identity
  `M.polarPartial ∘L |M| = M`, **unconditional**;
* `ContinuousLinearMap.polarPartial_comp_adjoint_comp_polarPartial`: the algebraic
  partial-isometry identity `W W⋆ W = W`, also unconditional;
* `ContinuousLinearMap.norm_polarPartial_apply_of_mem` and
  `ContinuousLinearMap.inner_polarPartial_apply_of_mem`: `W` preserves norms, and in fact
  inner products, on the initial space;
* `ContinuousLinearMap.polarPartial_eq_zero_of_mem_orthogonal` and
  `ContinuousLinearMap.ker_polarPartial`: `W` vanishes off the initial space, and nowhere
  else;
* `ContinuousLinearMap.adjoint_comp_polarPartial`: `W⋆ W` is the orthogonal projection onto
  the initial space;
* `ContinuousLinearMap.polarInitial_orthogonal_eq_ker`: the orthogonal complement of the
  initial space is exactly `ker M`, so the initial space is `(ker M)ᗮ`;
* `ContinuousLinearMap.commute_polarPartial_of_commute`: an endomorphism commuting with both
  `M` and `|M|` also commutes with the polar partial isometry;
* `ContinuousLinearMap.polarPartial_comp_self_eq_neg_starProjection_of_adjoint_eq_neg`:
  for skew-adjoint `M`, the polar phase squares to minus the initial-space projection;
* `ContinuousLinearMap.range_polarPartial` and
  `ContinuousLinearMap.isClosed_range_polarPartial`: the range of `W` is closed and is the
  closure of `range M` — the **final** space;
* `ContinuousLinearMap.isSelfAdjoint_polarPartial_comp_adjoint` and
  `ContinuousLinearMap.isIdempotentElem_polarPartial_comp_adjoint`: `W W⋆` is the
  orthogonal projection onto it;
* `ContinuousLinearMap.adjoint_polarPartial_comp_self`: the initial-space identity
  `W⋆ M = |M|`;
* `ContinuousLinearMap.modulus_adjoint`: `|M⋆| = W |M| W⋆`, and
  `ContinuousLinearMap.modulus_adjoint_comp_polarPartial`: the second polar identity
  `M = |M⋆| W`;
* `ContinuousLinearMap.eq_polarPartial_of_comp_modulus`: **uniqueness** — a bounded `V`
  with `V |M| = M` vanishing off the initial space *is* `W`, so the decomposition is
  characterised and not merely exhibited;
* `ContinuousLinearMap.polarPartial_adjoint`: `W(M⋆) = W(M)⋆`, an immediate consequence of
  uniqueness.

## Relation to the rest of the library

`ForTauCeti/Analysis/InnerProductSpace/Polar/Decomposition.lean` has the partial-isometry
factor for `LinearMap` endomorphisms in **finite dimensions**;
`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` has the *invertible* case in
general.  This is the general bounded statement that subsumes both directions of that gap,
which is why `Polar/Isometry.lean` is its bounded-below specialization.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Sol.
* Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.  This module is the canonical bounded polar decomposition used
  directly by the Davis--Kahan geometry; no parallel Spectra-derived polar API remains in the
  supported source tree.

## The three polar factors, and how they relate

Documented here because none of the three named the others, so a reviewer could
not tell a designed hierarchy from three independent
attempts. The separating hypotheses are the carrier, the field, and whether the
modulus is invertible:

* `TauCeti.polarFactor`, in `Polar/Decomposition.lean` — square `E →ₗ[𝕜] E`,
  `RCLike`, finite dimension; a genuine **unitary** factor.
* `TauCeti.polarPartial`, in `Polar/PartialIsometry.lean` — rectangular
  `E →L[𝕜] F` over `RCLike`, no invertibility assumed; a **partial isometry**.
* `TauCeti.polarIsometryOfIsUnitModulus`, in `Polar/Isometry.lean` — rectangular
  `E →L[𝕜] F` over `RCLike` **and** the modulus a unit; then the factor is an
  **isometry**.

Read down the list: dropping finite dimension costs the unitary and leaves a
partial isometry; adding invertibility of the modulus gives an isometry.

`Polar/GramContraction.lean` is lower-level machinery for this construction rather than a
fourth modulus or polar-factor API.  It starts from a self-adjoint `A` satisfying the Gram
identity `A ∘L A = T⋆ ∘L T` and constructs the contraction needed here.  This module applies
that machinery to the canonical `A = T.modulus` and carries the full partial-isometry API
(`W W⋆ W = W`, the initial and final spaces, uniqueness, `|M⋆| = W |M| W⋆`).

`ContinuousLinearMap.modulus` is `RCLike`-generic with its scalar and functional-calculus
infrastructure selected locally inside the reusable operator modules.  The polar decomposition
therefore has only the Hilbert-space and completeness assumptions below.  Results involving
`|M⋆|` use the same canonical infrastructure on the target space without adding hypotheses to
their public signatures.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
/-- The **initial space** of the polar decomposition of `M`: the closure of the range of
the modulus.  `M.polarPartial` is isometric on it and zero on its orthogonal complement,
and it is exactly `(ker M)ᗮ` (`polarInitial_orthogonal_eq_ker`). -/
noncomputable def polarInitial (M : E →L[𝕜] F) : Submodule 𝕜 E :=
  (LinearMap.range M.modulus.toLinearMap).topologicalClosure

/-- Every value of the modulus lies in the initial space, which is the closure
of its range. -/
theorem modulus_apply_mem_polarInitial (M : E →L[𝕜] F) (x : E) :
    M.modulus x ∈ M.polarInitial :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- The initial space is complete, being a topological closure.  This is what
lets `polarInitialMap` be built by continuous extension. -/
instance (M : E →L[𝕜] F) : CompleteSpace M.polarInitial :=
  Submodule.topologicalClosure.completeSpace _

/-- The modulus, corestricted to the initial space, where it has dense range. -/
noncomputable def modulusCorestrict (M : E →L[𝕜] F) : E →ₗ[𝕜] M.polarInitial :=
  LinearMap.codRestrict M.polarInitial M.modulus.toLinearMap M.modulus_apply_mem_polarInitial

/-- The corestriction has the same values as the modulus; only its codomain
changes. -/
@[simp]
theorem coe_modulusCorestrict_apply (M : E →L[𝕜] F) (x : E) :
    (M.modulusCorestrict x : E) = M.modulus x := (rfl)
/-- The corestricted modulus has **dense** range in the initial space — the
initial space is defined as that closure.  This density is the hypothesis
`extendOfNorm` needs, and is why `polarPartial` is determined on all of
`polarInitial` by its values on `range |M|`. -/
theorem denseRange_modulusCorestrict (M : E →L[𝕜] F) :
    DenseRange M.modulusCorestrict := by
  rw [DenseRange, Subtype.dense_iff]
  have hsub : (LinearMap.range M.modulus.toLinearMap : Set E)
      ⊆ (Subtype.val '' Set.range M.modulusCorestrict) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨M.modulusCorestrict x, ⟨x, rfl⟩, rfl⟩
  calc (M.polarInitial : Set E)
      = closure (LinearMap.range M.modulus.toLinearMap : Set E) :=
        Submodule.topologicalClosure_coe _
    _ ⊆ closure (Subtype.val '' Set.range M.modulusCorestrict) := closure_mono hsub

/-- The isometry bound that makes the extension possible:
`‖M x‖ ≤ 1 * ‖ |M| x ‖`, which is an equality by
`ContinuousLinearMap.norm_modulus_apply`. -/
theorem norm_apply_le_norm_modulusCorestrict (M : E →L[𝕜] F) (x : E) :
    ‖M.toLinearMap x‖ ≤ 1 * ‖M.modulusCorestrict x‖ := by
  rw [one_mul]
  exact le_of_eq (M.norm_modulus_apply x).symm

/-- The isometry `|M| x ↦ M x`, extended from the dense range of the modulus to the whole
initial space. -/
noncomputable def polarInitialMap (M : E →L[𝕜] F) : M.polarInitial →L[𝕜] F :=
  M.toLinearMap.extendOfNorm M.modulusCorestrict

/-- The extension undoes the modulus on the dense range: `W₀ (|M| x) = M x`.
This is the defining property carried across by continuity. -/
@[simp]
theorem polarInitialMap_modulusCorestrict (M : E →L[𝕜] F) (x : E) :
    M.polarInitialMap (M.modulusCorestrict x) = M x :=
  LinearMap.extendOfNorm_eq M.denseRange_modulusCorestrict
    ⟨1, M.norm_apply_le_norm_modulusCorestrict⟩ x

/-- The **polar partial isometry** of a bounded operator.

Isometric on `M.polarInitial` and zero on its orthogonal complement, with
`M.polarPartial ∘L |M| = M` unconditionally. -/
noncomputable def polarPartial (M : E →L[𝕜] F) : E →L[𝕜] F :=
  M.polarInitialMap ∘L M.polarInitial.orthogonalProjectionOnto

/-- `polarPartial` unfolded: project onto the initial space, then apply the
continuous extension.  The projection is what makes `W` vanish off the initial
space, i.e. on `ker M`. -/
theorem polarPartial_apply (M : E →L[𝕜] F) (x : E) :
    M.polarPartial x = M.polarInitialMap (M.polarInitial.orthogonalProjectionOnto x) := (rfl)
/-- **The polar identity.**  `M = W |M|` with `W` the polar partial isometry, for every
bounded `M` and with no invertibility hypothesis. -/
@[simp]
theorem polarPartial_apply_modulus (M : E →L[𝕜] F) (x : E) :
    M.polarPartial (M.modulus x) = M x := by
  rw [polarPartial_apply]
  have hmem : M.modulus x ∈ M.polarInitial := M.modulus_apply_mem_polarInitial x
  have hproj : M.polarInitial.orthogonalProjectionOnto (M.modulus x)
      = M.modulusCorestrict x := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hmem
  rw [hproj, polarInitialMap_modulusCorestrict]

/-- **The polar identity in composed form**: `W ∘L |M| = M`, unconditionally.
The pointwise version is `polarPartial_apply_modulus`; this is the form that
composes, and the one `eq_polarPartial_of_comp_modulus` characterises `W` by. -/
theorem polarPartial_comp_modulus (M : E →L[𝕜] F) :
    M.polarPartial ∘L M.modulus = M := by
  ext x
  simp


/-- The modulus is self-adjoint, so it moves across the inner product. -/
theorem inner_modulus_left (M : E →L[𝕜] F) (x z : E) :
    ⟪M.modulus x, z⟫_𝕜 = ⟪x, M.modulus z⟫_𝕜 :=
  calc ⟪M.modulus x, z⟫_𝕜 = ⟪M.modulus.adjoint x, z⟫_𝕜 := by rw [M.adjoint_modulus]
    _ = ⟪x, M.modulus z⟫_𝕜 := ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The extension is an isometry on the whole initial space: it is one on the dense range
of the modulus, and both sides are continuous. -/
theorem norm_polarInitialMap_apply (M : E →L[𝕜] F) (y : M.polarInitial) :
    ‖M.polarInitialMap y‖ = ‖y‖ := by
  have heq : Set.EqOn (fun z : M.polarInitial => ‖M.polarInitialMap z‖)
      (fun z : M.polarInitial => ‖z‖) (Set.range M.modulusCorestrict) := by
    rintro _ ⟨x, rfl⟩
    simp only [polarInitialMap_modulusCorestrict]
    exact (M.norm_modulus_apply x).symm
  exact congrFun (Continuous.ext_on M.denseRange_modulusCorestrict
    (by fun_prop) (by fun_prop) heq) y

/-- The polar partial isometry is an isometry on the initial space. -/
theorem norm_polarPartial_apply_of_mem (M : E →L[𝕜] F) {y : E} (hy : y ∈ M.polarInitial) :
    ‖M.polarPartial y‖ = ‖y‖ := by
  rw [polarPartial_apply]
  have hproj : M.polarInitial.orthogonalProjectionOnto y = ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hy
  rw [hproj, M.norm_polarInitialMap_apply ⟨y, hy⟩]
  rfl

/-- The polar partial isometry vanishes off the initial space. -/
theorem polarPartial_eq_zero_of_mem_orthogonal (M : E →L[𝕜] F) {y : E}
    (hy : y ∈ M.polarInitialᗮ) : M.polarPartial y = 0 := by
  rw [polarPartial_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy, map_zero]

/-- **The initial space is the orthogonal complement of the kernel.**  Equivalently
`M.polarInitial = (ker M)ᗮ`: the partial isometry is supported exactly where `M` is. -/
theorem polarInitial_orthogonal_eq_ker (M : E →L[𝕜] F) :
    M.polarInitialᗮ = LinearMap.ker M.toLinearMap := by
  ext y
  constructor
  · intro hy
    have hall : ∀ x : E, ⟪x, M.modulus y⟫_𝕜 = 0 := by
      intro x
      have h := hy (M.modulus x) (M.modulus_apply_mem_polarInitial x)
      rwa [M.inner_modulus_left] at h
    have hzero : M.modulus y = 0 := inner_self_eq_zero.mp (hall _)
    exact (M.modulus_apply_eq_zero_iff y).mp hzero
  · intro hy
    have hMy : M y = 0 := hy
    have hmod : M.modulus y = 0 := (M.modulus_apply_eq_zero_iff y).mpr hMy
    have hle : M.polarInitial ≤ (𝕜 ∙ y)ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rintro _ ⟨x, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp only [ContinuousLinearMap.coe_coe]
      rw [← M.inner_modulus_left, hmod, inner_zero_left]
    intro u hu
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    exact this

/-- The initial space is exactly the orthogonal complement of the kernel. -/
theorem polarInitial_eq_orthogonal_ker (M : E →L[𝕜] F) :
    M.polarInitial = (LinearMap.ker M.toLinearMap)ᗮ := by
  rw [← M.polarInitial_orthogonal_eq_ker, Submodule.orthogonal_orthogonal]

/-- Commutation passes from an operator and its modulus to the polar partial isometry.

This is the dimension-free support argument behind the usual statement that a symmetry of both
`M` and `|M|` also preserves the phase in the polar decomposition.  No injectivity or closed-range
hypothesis is needed: on `M.polarInitial` the result follows by density of the modulus range, and
on its orthogonal complement both sides vanish because commutation with `M` preserves `ker M`. -/
theorem commute_polarPartial_of_commute
    {A M : E →L[𝕜] E} (hAM : Commute A M) (hAmod : Commute A M.modulus) :
    Commute A M.polarPartial := by
  rw [commute_iff_eq]
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hJq : M.polarPartial q = 0 := M.polarPartial_eq_zero_of_mem_orthogonal hq
  have hAqker : A q ∈ LinearMap.ker M.toLinearMap := by
    rw [LinearMap.mem_ker]
    have hq' : q ∈ LinearMap.ker M.toLinearMap := by
      rwa [← M.polarInitial_orthogonal_eq_ker]
    have hqker : M q = 0 := hq'
    have h := congrArg (fun T : E →L[𝕜] E => T q) hAM.eq
    simp only [mul_apply_eq_comp] at h
    rw [hqker, map_zero] at h
    exact h.symm
  have hAq : A q ∈ M.polarInitialᗮ := by
    rwa [M.polarInitial_orthogonal_eq_ker]
  have hJAq : M.polarPartial (A q) = 0 := M.polarPartial_eq_zero_of_mem_orthogonal hAq
  have hagree : A (M.polarPartial p) = M.polarPartial (A p) := by
    have hclosed : IsClosed {z : M.polarInitial |
        A (M.polarPartial z) = M.polarPartial (A z)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hgen : ∀ y : E,
        A (M.polarPartial (M.modulusCorestrict y)) =
          M.polarPartial (A (M.modulusCorestrict y)) := by
      intro y
      have hleft : A (M y) = M (A y) := by
        have h := congrArg (fun T : E →L[𝕜] E => T y) hAM.eq
        simpa only [mul_apply_eq_comp] using h
      have hmodApp : A (M.modulus y) = M.modulus (A y) := by
        have h := congrArg (fun T : E →L[𝕜] E => T y) hAmod.eq
        simpa only [mul_apply_eq_comp] using h
      change A (M.polarPartial (M.modulus y)) =
        M.polarPartial (A (M.modulus y))
      rw [M.polarPartial_apply_modulus, hmodApp, M.polarPartial_apply_modulus, hleft]
    exact M.denseRange_modulusCorestrict.induction_on
      (p := fun z : M.polarInitial =>
        A (M.polarPartial z) = M.polarPartial (A z)) ⟨p, hp⟩ hclosed hgen
  simp only [mul_apply_eq_comp, map_add, hJq, hJAq, map_zero, add_zero]
  exact hagree

/-- The kernel of the polar partial isometry is exactly the orthogonal complement of the
initial space — it kills nothing else. -/
theorem ker_polarPartial (M : E →L[𝕜] F) :
    LinearMap.ker M.polarPartial.toLinearMap = M.polarInitialᗮ := by
  apply le_antisymm
  · intro y hy
    have hWy : M.polarPartial y = 0 := hy
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) y
    have hWq : M.polarPartial q = 0 := M.polarPartial_eq_zero_of_mem_orthogonal hq
    have hWp : M.polarPartial p = 0 := by
      have := hWy
      rw [map_add, hWq, add_zero] at this
      exact this
    have hp0 : p = 0 := by
      have := M.norm_polarPartial_apply_of_mem hp
      rw [hWp, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    rw [hp0, zero_add]
    exact hq
  · intro y hy
    exact M.polarPartial_eq_zero_of_mem_orthogonal hy

/-- The initial space is the orthogonal complement of the kernel of the partial isometry,
which is the shape the abstract partial-isometry API expects. -/
theorem orthogonal_ker_polarPartial (M : E →L[𝕜] F) :
    (LinearMap.ker M.polarPartial.toLinearMap)ᗮ = M.polarInitial := by
  rw [M.ker_polarPartial, Submodule.orthogonal_orthogonal]

/-- On the initial space the partial isometry preserves inner products, not just norms. -/
theorem inner_polarPartial_apply_of_mem (M : E →L[𝕜] F) {p q : E}
    (hp : p ∈ M.polarInitial) (hq : q ∈ M.polarInitial) :
    ⟪M.polarPartial p, M.polarPartial q⟫_𝕜 = ⟪p, q⟫_𝕜 := by
  have hnorm : ∀ w : M.polarInitial,
      ‖(M.polarPartial.toLinearMap ∘ₗ M.polarInitial.subtype) w‖ = ‖w‖ := by
    intro w
    simpa using M.norm_polarPartial_apply_of_mem w.2
  have hmap := (LinearMap.norm_map_iff_inner_map_map
    (M.polarPartial.toLinearMap ∘ₗ M.polarInitial.subtype)).mp hnorm
  simpa using hmap ⟨p, hp⟩ ⟨q, hq⟩

/-- `W⋆ W` fixes the initial space pointwise. -/
theorem adjoint_polarPartial_polarPartial_apply_of_mem (M : E →L[𝕜] F) {p : E}
    (hp : p ∈ M.polarInitial) :
    M.polarPartial.adjoint (M.polarPartial p) = p := by
  have hall : ∀ z : E, ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z⟫_𝕜 = 0 := by
    intro z
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ :=
      Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) z
    have h₁ : ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z₁⟫_𝕜 = 0 := by
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
        M.inner_polarPartial_apply_of_mem hp hz₁, sub_self]
    have h₂ : ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z₂⟫_𝕜 = 0 := by
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
        M.polarPartial_eq_zero_of_mem_orthogonal hz₂, inner_zero_right,
        (Submodule.mem_orthogonal _ _).mp hz₂ p hp, sub_zero]
    rw [inner_add_right, h₁, h₂, add_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hall _))

/-- `W⋆ W` is the orthogonal projection onto the initial space. -/
theorem adjoint_comp_polarPartial (M : E →L[𝕜] F) :
    M.polarPartial.adjoint ∘L M.polarPartial = M.polarInitial.starProjection := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hqz : M.polarInitial.starProjection q = 0 := by
    have hmem : q ∈ (M.polarInitial.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  simp only [ContinuousLinearMap.comp_apply, map_add,
    M.polarPartial_eq_zero_of_mem_orthogonal hq, map_zero, add_zero,
    M.adjoint_polarPartial_polarPartial_apply_of_mem hp, hqz,
    Submodule.starProjection_eq_self_iff.mpr hp]

/-- The partial isometry is unchanged by first projecting onto its initial space. -/
theorem polarPartial_comp_starProjection (M : E →L[𝕜] F) :
    M.polarPartial ∘L M.polarInitial.starProjection = M.polarPartial := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hqz : M.polarInitial.starProjection q = 0 := by
    have hmem : q ∈ (M.polarInitial.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  simp only [ContinuousLinearMap.comp_apply, map_add, hqz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hp,
    M.polarPartial_eq_zero_of_mem_orthogonal hq, map_zero]

/-- **The partial-isometry identity `W W⋆ W = W`**, for every bounded operator and with no
invertibility or finite-dimensionality hypothesis.  This is the algebraic form of
"`W` is a partial isometry"; the analytic form is
`norm_polarPartial_apply_of_mem` together with
`polarPartial_eq_zero_of_mem_orthogonal`. -/
theorem polarPartial_comp_adjoint_comp_polarPartial (M : E →L[𝕜] F) :
    M.polarPartial ∘L M.polarPartial.adjoint ∘L M.polarPartial = M.polarPartial := by
  rw [M.adjoint_comp_polarPartial, M.polarPartial_comp_starProjection]

/-- **The rectangular polar factor is a partial isometry** (Conway VI.3.9). -/
theorem polarPartial_isPartialIsometry (M : E →L[𝕜] F) :
    M.polarPartial.IsPartialIsometry :=
  M.polarPartial_comp_adjoint_comp_polarPartial

/-- The adjoint form of the partial-isometry identity, `W⋆ W W⋆ = W⋆`. -/
theorem adjoint_comp_polarPartial_comp_adjoint (M : E →L[𝕜] F) :
    M.polarPartial.adjoint ∘L M.polarPartial ∘L M.polarPartial.adjoint =
      M.polarPartial.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint M.polarPartial_comp_adjoint_comp_polarPartial
  simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using h

/-- `W W⋆` is an orthogonal projection: idempotent and self-adjoint.  It is the projection
onto the *final* space of the polar decomposition. -/
theorem isSelfAdjoint_polarPartial_comp_adjoint (M : E →L[𝕜] F) :
    IsSelfAdjoint (M.polarPartial ∘L M.polarPartial.adjoint) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- `W W⋆` is idempotent.  With `isSelfAdjoint_polarPartial_comp_adjoint` this
makes it the orthogonal projection onto the final space — the second half of
`W` being a partial isometry. -/
theorem isIdempotentElem_polarPartial_comp_adjoint (M : E →L[𝕜] F) :
    IsIdempotentElem (M.polarPartial ∘L M.polarPartial.adjoint) := by
  have h := M.adjoint_comp_polarPartial_comp_adjoint
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (M.polarPartial ∘L M.polarPartial.adjoint) ∘L
    (M.polarPartial ∘L M.polarPartial.adjoint) = _
  calc (M.polarPartial ∘L M.polarPartial.adjoint) ∘L
        (M.polarPartial ∘L M.polarPartial.adjoint)
      = M.polarPartial ∘L (M.polarPartial.adjoint ∘L M.polarPartial ∘L
          M.polarPartial.adjoint) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = M.polarPartial ∘L M.polarPartial.adjoint := by rw [h]

/-- The partial isometry, bundled as a `LinearIsometry` on the initial space. -/
noncomputable def polarInitialIsometry (M : E →L[𝕜] F) :
    M.polarInitial →ₗᵢ[𝕜] F where
  toLinearMap := M.polarInitialMap.toLinearMap
  norm_map' := M.norm_polarInitialMap_apply

/-- Every vector in the range of the partial isometry already comes from the initial
space, because the projection is the identity there. -/
theorem range_polarPartial_eq_range_polarInitialMap (M : E →L[𝕜] F) :
    Set.range M.polarPartial = Set.range M.polarInitialMap := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨M.polarInitial.orthogonalProjectionOnto x, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨(y : E), ?_⟩
    rw [polarPartial_apply]
    congr 1
    apply Subtype.ext
    simp

/-- **The range of the partial isometry is closed.**  It is the isometric image of the
initial space, and that space is complete. -/
theorem isClosed_range_polarPartial (M : E →L[𝕜] F) :
    IsClosed (Set.range M.polarPartial) := by
  rw [M.range_polarPartial_eq_range_polarInitialMap]
  have hrange : Set.range M.polarInitialMap = Set.range M.polarInitialIsometry := (rfl)
  rw [hrange, ← Set.image_univ]
  exact ((LinearIsometry.isComplete_image_iff M.polarInitialIsometry).mpr
    isComplete_univ).isClosed

/-- **The range of the partial isometry is the closure of the range of `M`** — the *final*
space of the polar decomposition. -/
theorem range_polarPartial (M : E →L[𝕜] F) :
    LinearMap.range M.polarPartial.toLinearMap =
      (LinearMap.range M.toLinearMap).topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have hclosed : IsClosed
        {w : M.polarInitial |
          M.polarInitialMap w ∈ (LinearMap.range M.toLinearMap).topologicalClosure} :=
      (Submodule.isClosed_topologicalClosure _).preimage M.polarInitialMap.continuous
    have hgen : ∀ x : E, M.polarInitialMap (M.modulusCorestrict x)
        ∈ (LinearMap.range M.toLinearMap).topologicalClosure := by
      intro x
      rw [polarInitialMap_modulusCorestrict]
      exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change M.polarPartial y ∈ _
    rw [polarPartial_apply]
    exact M.denseRange_modulusCorestrict.induction_on
      (p := fun w => M.polarInitialMap w ∈
        (LinearMap.range M.toLinearMap).topologicalClosure)
      (M.polarInitial.orthogonalProjectionOnto y) hclosed hgen
  · refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨M.modulus x, M.polarPartial_apply_modulus x⟩
    · rw [LinearMap.coe_range]
      exact M.isClosed_range_polarPartial

/-- **The initial-space identity `W⋆ M = |M|`.**

`W⋆ M = W⋆ W |M| = P |M| = |M|`, because the range of `|M|` already lies in the initial
space, where `W⋆ W` is the identity.  This is the identity behind the trace-norm duality
`tr (W⋆ M) = tr |M|`. -/
theorem adjoint_polarPartial_comp_self (M : E →L[𝕜] F) :
    M.polarPartial.adjoint ∘L M = M.modulus := by
  ext x
  have hstep : M.polarPartial.adjoint (M x)
      = M.polarPartial.adjoint (M.polarPartial (M.modulus x)) := by
    rw [M.polarPartial_apply_modulus]
  simpa [hstep] using
    M.adjoint_polarPartial_polarPartial_apply_of_mem (M.modulus_apply_mem_polarInitial x)

/-- `|M|` vanishes off the initial space, so projecting first changes nothing. -/
theorem modulus_comp_starProjection (M : E →L[𝕜] F) :
    M.modulus ∘L M.polarInitial.starProjection = M.modulus := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hqker : M.modulus q = 0 := by
    have hq' : q ∈ LinearMap.ker M.toLinearMap := by
      rw [← M.polarInitial_orthogonal_eq_ker]; exact hq
    exact (M.modulus_apply_eq_zero_iff q).mpr hq'
  have hqz : M.polarInitial.starProjection q = 0 := by
    have hmem : q ∈ (M.polarInitial.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  simp only [ContinuousLinearMap.comp_apply, map_add, hqz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hp, hqker, map_zero]

/-- The adjoint form of the polar identity: `M⋆ = |M| W⋆`. -/
theorem adjoint_eq_modulus_comp_adjoint_polarPartial (M : E →L[𝕜] F) :
    M.adjoint = M.modulus ∘L M.polarPartial.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint M.polarPartial_comp_modulus
  rw [ContinuousLinearMap.adjoint_comp, M.modulus_isSelfAdjoint.adjoint_eq] at h
  exact h.symm

/-- **The modulus of the adjoint**: `|M⋆| = W |M| W⋆`.

This is the other half of the polar decomposition — alongside `M = W |M|` it gives
`M = |M⋆| W` — and it identifies the final space as the initial space of `M⋆`.  The proof
is uniqueness of the positive square root: `W |M| W⋆` is positive, and both it squared and
`M M⋆` reduce to `W (M⋆ M) W⋆`. -/
theorem modulus_adjoint (M : E →L[𝕜] F) :
    M.adjoint.modulus = M.polarPartial ∘L M.modulus ∘L M.polarPartial.adjoint := by
  refine (eq_modulus_of_nonneg_of_mul_self_eq ?_ ?_).symm
  · rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp M.modulus_nonneg).conj_adjoint
      M.polarPartial
  · have hP : ∀ y : E, M.polarPartial.adjoint (M.polarPartial y)
        = M.polarInitial.starProjection y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, M.adjoint_comp_polarPartial]
    have hS : ∀ z : E, M.modulus (M.polarInitial.starProjection z) = M.modulus z := by
      intro z
      rw [← ContinuousLinearMap.comp_apply, M.modulus_comp_starProjection]
    have hMadj : ∀ y : F, M.adjoint y = M.modulus (M.polarPartial.adjoint y) := by
      intro y
      rw [M.adjoint_eq_modulus_comp_adjoint_polarPartial, ContinuousLinearMap.comp_apply]
    have hM : ∀ z : E, M z = M.polarPartial (M.modulus z) := by
      intro z
      rw [M.polarPartial_apply_modulus]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (M.polarPartial ∘L M.modulus ∘L M.polarPartial.adjoint) ∘L
      (M.polarPartial ∘L M.modulus ∘L M.polarPartial.adjoint) = _
    rw [ContinuousLinearMap.adjoint_adjoint]
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hP, hS, hMadj, hM]

/-- The second polar identity, `M = |M⋆| W`. -/
theorem modulus_adjoint_comp_polarPartial (M : E →L[𝕜] F) :
    M.adjoint.modulus ∘L M.polarPartial = M := by
  rw [M.modulus_adjoint]
  calc (M.polarPartial ∘L M.modulus ∘L M.polarPartial.adjoint) ∘L M.polarPartial
      = M.polarPartial ∘L M.modulus ∘L (M.polarPartial.adjoint ∘L M.polarPartial) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = M.polarPartial ∘L M.modulus := by
        rw [M.adjoint_comp_polarPartial, M.modulus_comp_starProjection]
    _ = M := M.polarPartial_comp_modulus

/-- **Uniqueness of the polar partial isometry.**  A bounded `V` with `V |M| = M` that
vanishes off the initial space *is* `W`.

Together with `polarPartial_comp_modulus` this characterises the decomposition: `W` is the
unique partial isometry with initial space `(ker M)ᗮ` factoring `M` through `|M|`. -/
theorem eq_polarPartial_of_comp_modulus (M : E →L[𝕜] F) (V : E →L[𝕜] F)
    (hV : V ∘L M.modulus = M)
    (hker : ∀ y ∈ M.polarInitialᗮ, V y = 0) :
    V = M.polarPartial := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hagree : ∀ z ∈ M.polarInitial, V z = M.polarPartial z := by
    intro z hz
    have hclosed : IsClosed {w : M.polarInitial | V w = M.polarPartial w} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hgen : ∀ u : E, V (M.modulusCorestrict u) = M.polarPartial (M.modulusCorestrict u) := by
      intro u
      have hVu : V (M.modulus u) = M u := by
        rw [← ContinuousLinearMap.comp_apply, hV]
      simpa using hVu.trans (M.polarPartial_apply_modulus u).symm
    exact M.denseRange_modulusCorestrict.induction_on
      (p := fun w : M.polarInitial => V w = M.polarPartial w) ⟨z, hz⟩ hclosed hgen
  rw [map_add, map_add, hagree p hp, hker q hq,
    M.polarPartial_eq_zero_of_mem_orthogonal hq]

/-- Negating an operator negates its polar partial isometry. -/
@[simp]
theorem polarPartial_neg (M : E →L[𝕜] F) : (-M).polarPartial = -M.polarPartial := by
  symm
  refine (-M).eq_polarPartial_of_comp_modulus (-M.polarPartial) ?_ ?_
  · rw [ContinuousLinearMap.modulus_neg]
    ext x
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      M.polarPartial_apply_modulus]
  · intro y hy
    have hyM : y ∈ M.polarInitialᗮ := by
      rw [M.polarInitial_orthogonal_eq_ker]
      rw [(-M).polarInitial_orthogonal_eq_ker] at hy
      simpa using hy
    rw [neg_apply,
      M.polarPartial_eq_zero_of_mem_orthogonal hyM, neg_zero]

/-- The projection onto the initial space fixes the range of `|M|`. -/
theorem starProjection_comp_modulus (M : E →L[𝕜] F) :
    M.polarInitial.starProjection ∘L M.modulus = M.modulus := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (M.modulus_apply_mem_polarInitial x)

/-- `W⋆` lands in the initial space. -/
theorem starProjection_comp_adjoint_polarPartial (M : E →L[𝕜] F) :
    M.polarInitial.starProjection ∘L M.polarPartial.adjoint = M.polarPartial.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint M.polarPartial_comp_starProjection
  rwa [ContinuousLinearMap.adjoint_comp,
    (_root_.isSelfAdjoint_starProjection M.polarInitial).adjoint_eq] at h

/-- **`W(M⋆) = W(M)⋆`**: the partial isometry of the adjoint is the adjoint of the partial
isometry.  By uniqueness, since `W⋆ |M⋆| = M⋆` and `W⋆` vanishes on `ker M⋆`. -/
theorem polarPartial_adjoint (M : E →L[𝕜] F) :
    M.adjoint.polarPartial = M.polarPartial.adjoint := by
  refine (M.adjoint.eq_polarPartial_of_comp_modulus M.polarPartial.adjoint ?_ ?_).symm
  · -- W⋆ |M⋆| = W⋆ W |M| W⋆ = P |M| W⋆ = |M| W⋆ = M⋆
    rw [M.modulus_adjoint]
    have hstep : M.polarPartial.adjoint ∘L
        (M.polarPartial ∘L M.modulus ∘L M.polarPartial.adjoint)
        = (M.polarPartial.adjoint ∘L M.polarPartial) ∘L
            M.modulus ∘L M.polarPartial.adjoint := by
      simp only [ContinuousLinearMap.comp_assoc]
    rw [hstep, M.adjoint_comp_polarPartial]
    have hstep2 : M.polarInitial.starProjection ∘L M.modulus ∘L M.polarPartial.adjoint
        = (M.polarInitial.starProjection ∘L M.modulus) ∘L M.polarPartial.adjoint := by
      simp only [ContinuousLinearMap.comp_assoc]
    rw [hstep2, M.starProjection_comp_modulus,
      ← M.adjoint_eq_modulus_comp_adjoint_polarPartial]
  · -- W⋆ kills ker M⋆
    intro y hy
    have hker : y ∈ LinearMap.ker M.adjoint.toLinearMap := by
      rwa [← M.adjoint.polarInitial_orthogonal_eq_ker]
    have hmod : M.modulus (M.polarPartial.adjoint y) = 0 := by
      have : M.adjoint y = 0 := hker
      rwa [M.adjoint_eq_modulus_comp_adjoint_polarPartial,
        ContinuousLinearMap.comp_apply] at this
    have hperp : M.polarPartial.adjoint y ∈ M.polarInitialᗮ := by
      rw [M.polarInitial_orthogonal_eq_ker]
      exact (M.modulus_apply_eq_zero_iff _).mp hmod
    have hmem : M.polarPartial.adjoint y ∈ M.polarInitial := by
      have h := congrArg (fun T => T y) M.starProjection_comp_adjoint_polarPartial
      simp only [ContinuousLinearMap.comp_apply] at h
      rw [← h]
      exact Submodule.starProjection_apply_mem _ _
    exact inner_self_eq_zero.mp (hperp _ hmem)

/-- The polar partial isometry of a skew-adjoint endomorphism is skew-adjoint. -/
theorem adjoint_polarPartial_eq_neg_of_adjoint_eq_neg
    {M : E →L[𝕜] E} (hM : M.adjoint = -M) :
    M.polarPartial.adjoint = -M.polarPartial := by
  rw [← M.polarPartial_adjoint, hM, M.polarPartial_neg]

/-- For a skew-adjoint endomorphism, the square of the polar partial isometry is minus the
orthogonal projection onto its initial space.  This is the global form of the statement that the
polar phase is a quarter turn on the support of the operator and vanishes on its kernel. -/
theorem polarPartial_comp_self_eq_neg_starProjection_of_adjoint_eq_neg
    {M : E →L[𝕜] E} (hM : M.adjoint = -M) :
    M.polarPartial ∘L M.polarPartial = -M.polarInitial.starProjection := by
  have hstar := adjoint_polarPartial_eq_neg_of_adjoint_eq_neg (M := M) hM
  ext x
  have hproj := congrArg (fun T : E →L[𝕜] E => T x) M.adjoint_comp_polarPartial
  simp only [ContinuousLinearMap.comp_apply] at hproj ⊢
  rw [hstar] at hproj
  simp only [neg_apply] at hproj ⊢
  calc
    M.polarPartial (M.polarPartial x) = -(-M.polarPartial (M.polarPartial x)) := by simp
    _ = -(M.polarInitial.starProjection x) := by rw [hproj]

/-- On the initial space of a skew-adjoint endomorphism, applying its polar partial isometry twice
is exactly negation. -/
theorem polarPartial_apply_polarPartial_apply_of_mem_of_adjoint_eq_neg
    {M : E →L[𝕜] E} (hM : M.adjoint = -M) {x : E} (hx : x ∈ M.polarInitial) :
    M.polarPartial (M.polarPartial x) = -x := by
  have hsquare := polarPartial_comp_self_eq_neg_starProjection_of_adjoint_eq_neg
    (M := M) hM
  have happ := congrArg (fun T : E →L[𝕜] E => T x) hsquare
  simpa only [ContinuousLinearMap.comp_apply, neg_apply,
    Submodule.starProjection_eq_self_iff.mpr hx] using happ

/-- The **final space** of the polar decomposition: the closure of the range of `M`,
equivalently the range of `W` (`range_polarPartial`). -/
noncomputable def polarFinal (M : E →L[𝕜] F) : Submodule 𝕜 F :=
  (LinearMap.range M.toLinearMap).topologicalClosure

/-- The final space is complete, being a topological closure. -/
instance (M : E →L[𝕜] F) : CompleteSpace M.polarFinal :=
  Submodule.topologicalClosure.completeSpace _

/-- The final space is exactly the range of `W`: closing the range of `M` and
taking the range of the partial isometry give the same subspace.  This is the
counterpart of `polarInitial` being the closed range of `|M|`. -/
theorem polarFinal_eq_range_polarPartial (M : E →L[𝕜] F) :
    M.polarFinal = LinearMap.range M.polarPartial.toLinearMap :=
  M.range_polarPartial.symm

/-- `W⋆` vanishes off the final space. -/
theorem adjoint_polarPartial_eq_zero_of_mem_orthogonal (M : E →L[𝕜] F) {y : F}
    (hy : y ∈ M.polarFinalᗮ) : M.polarPartial.adjoint y = 0 := by
  have hall : ∀ z : E, ⟪z, M.polarPartial.adjoint y⟫_𝕜 = 0 := by
    intro z
    rw [ContinuousLinearMap.adjoint_inner_right]
    refine hy _ ?_
    rw [M.polarFinal_eq_range_polarPartial]
    exact ⟨z, rfl⟩
  exact inner_self_eq_zero.mp (hall _)

/-- **`W W⋆` is the orthogonal projection onto the final space.** -/
theorem polarPartial_comp_adjoint (M : E →L[𝕜] F) :
    M.polarPartial ∘L M.polarPartial.adjoint = M.polarFinal.starProjection := by
  ext y
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarFinal) y
  have hqz : M.polarFinal.starProjection q = 0 := by
    have hmem : q ∈ (M.polarFinal.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  have hqW : M.polarPartial.adjoint q = 0 :=
    M.adjoint_polarPartial_eq_zero_of_mem_orthogonal hq
  have hpW : M.polarPartial (M.polarPartial.adjoint p) = p := by
    rw [M.polarFinal_eq_range_polarPartial] at hp
    obtain ⟨z, rfl⟩ := hp
    simp only [ContinuousLinearMap.coe_coe]
    have hz : M.polarPartial.adjoint (M.polarPartial z) = M.polarInitial.starProjection z := by
      rw [← ContinuousLinearMap.comp_apply, M.adjoint_comp_polarPartial]
    rw [hz, ← ContinuousLinearMap.comp_apply, M.polarPartial_comp_starProjection]
  simp only [ContinuousLinearMap.comp_apply, map_add, hqW, hqz, map_zero, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hp, hpW]

/-! ### The invertible case

When `|M|` is invertible the partial isometry is given by the closed formula
`M |M|⁻¹`, and its initial space is everything.  This reconciles the general
construction with the light one in
`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean`, which defines
`polarIsometryOfIsUnitModulus M := M ∘L Ring.inverse M.modulus` directly and needs no
polar-decomposition theory: the two agree exactly where the light one is
meaningful, so it is a specialisation rather than a rival construction. -/

/-- **The polar partial isometry in the invertible case.**  If `|M|` is a unit
then `W = M |M|⁻¹`.

Proved from uniqueness: `M |M|⁻¹` composes with `|M|` to give `M`, and it
vanishes off the initial space vacuously, because invertibility of `|M|` forces
`ker M = ⊥` and hence `polarInitialᗮ = ⊥`. -/
theorem polarPartial_eq_comp_ringInverse_modulus (M : E →L[𝕜] F)
    (hM : IsUnit M.modulus) :
    M.polarPartial = M ∘L Ring.inverse M.modulus := by
  refine (M.eq_polarPartial_of_comp_modulus _ ?_ ?_).symm
  · rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ hM, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id]
  · intro y hy
    rw [M.polarInitial_orthogonal_eq_ker] at hy
    have hMy : M y = 0 := hy
    have hmod : M.modulus y = 0 := (M.modulus_apply_eq_zero_iff y).mpr hMy
    have hy0 : y = 0 := by
      have h1 : (Ring.inverse M.modulus * M.modulus) y = y := by
        rw [Ring.inverse_mul_cancel _ hM]
        rfl
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hmod,
        map_zero] at h1
      exact h1.symm
    simp [hy0]

end ContinuousLinearMap
