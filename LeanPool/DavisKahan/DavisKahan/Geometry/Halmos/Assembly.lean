/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.Classification
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OrthogonalGluing

/-! # Assembly -/

open TauCeti.DavisKahan.Sylvester

/-!
# Assembling a pair-equivalence from matched Halmos summands

The converse of `twoProjection_operator_classification` has to *produce* a
unitary `H₁ ≃ₗᵢ H₂` carrying `U₁, V₁` to `U₂, V₂` out of an invariant that only
says the pieces match.  This module is the assembly half of that — brick (2) in
the frontier module's terminology.

`halmosTrivialPart U V` is `(common ⊔ source) ⊔ (target ⊔ exterior)` and
`halmosGenericPart U V` is its orthogonal complement, so the assembly is three
applications of `TauCeti.orthogonalSupGlue` followed by one of
`TauCeti.orthogonalGlue`.  What makes it work is that the four elementary
summands are *mutually orthogonal* (`halmosCommon_le_sourceDefect_orthogonal`
and its five siblings), which is exactly the side condition those lemmas want.

The remaining brick is the generic model: an isometry of the generic parts that
intertwines the two cosine-square operators has to be upgraded to one that
intertwines both projections.  That is the input `eg` here, and it is where the
mathematics still missing lives.

## Overlap with `Geometry/Polar/TwoProjectionOperatorClassification.lean`

**That file already assembles a trivial-part equivalence and a generic-part
equivalence into an ambient unitary**, via `Submodule.orthogonalDecomposition`
and `withLpProdCongr`, and concludes its own
`twoProjection_operator_classification`.  This file's `halmosGlobalEquiv` does
the same outer step by a different route, so the outer glue is genuinely
duplicated.  That was not noticed until after this module was written; it is
recorded here rather than left silent.

What is *not* duplicated, and is why this module exists:

* That file takes `trivialEquiv` as **given**, packaged in
  `TwoProjectionOperatorEquivalence` together with a hypothesis that it
  intertwines the restricted projections.  A caller does not have that — a
  caller has four isometries of the four elementary summands.  This file builds
  `trivialEquiv` from them (`halmosTrivialEquiv`, three `orthogonalSupGlue`s)
  and shows **no intertwining hypothesis on the elementary summands is needed**:
  it is automatic, because `common ≤ U ⊓ V`, `source ≤ U ⊓ Vᗮ`,
  `target ≤ Uᗮ ⊓ V` and `exterior ≤ Uᗮ ⊓ Vᗮ`.
* The structural lemmas `inf_halmosTrivialPart_left`/`_right`,
  `starProjection_trivial_mem_left`/`_right` and
  `eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart` are new.
* `ForTauCeti.orthogonalSupGlue` (gluing across `A ⊔ B`) has no counterpart
  there; `orthogonalDecomposition` only splits a space against one complement.

**Consolidation is a follow-up**: `halmosGlobalEquiv` and its four
`map_halmosGlobalEquiv_*` lemmas should be replaced by a constructor
`TwoProjectionOperatorEquivalence` built from the four summand isometries, so
the outer assembly exists once.  Doing it needs the trivial-part intertwining
fields proved from the summand data, which is the one piece not yet written.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan



universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]

section OrthogonalPairs

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A join is orthogonal to a join when each of the four pairs is. -/
theorem sup_le_orthogonal_sup {K L M N : Submodule 𝕜 H} (h₁ : K ≤ Mᗮ)
    (h₂ : K ≤ Nᗮ) (h₃ : L ≤ Mᗮ) (h₄ : L ≤ Nᗮ) : K ⊔ L ≤ (M ⊔ N)ᗮ := by
  have hmem : ∀ {P : Submodule 𝕜 H}, P ≤ Mᗮ → P ≤ Nᗮ → P ≤ (M ⊔ N)ᗮ := by
    intro P hM hN x hx
    rw [Submodule.mem_orthogonal]
    rintro u hu
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hu
    rw [inner_add_left, (Submodule.mem_orthogonal _ _).mp (hM hx) m hm,
      (Submodule.mem_orthogonal _ _).mp (hN hx) n hn, add_zero]
  exact sup_le (hmem h₁ h₂) (hmem h₃ h₄)

end OrthogonalPairs

/-! ## How `U` and `V` sit across the trivial/generic split

To show an assembled isometry carries `U₁` to `U₂` one has to split a vector of
`U₁` into a trivial and a generic piece *that are themselves in `U₁`*, and know
what the trivial piece looks like.  Both facts are recorded here; neither was in
`TwoProjections.lean`, which carries the dual statements (the projections
preserve the summands) but not these.
-/

section Structure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- The trivial part reduces the source projection. -/
theorem starProjection_left_reduces_halmosTrivialPart :
    U.starProjection.Reduces (halmosTrivialPart U V) :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    U.starProjection_isSymmetric
    fun y hy => projection_mem_halmosTrivialPart_left U V (x := y) hy

omit [CompleteSpace H] in
/-- The trivial part reduces the target projection. -/
theorem starProjection_right_reduces_halmosTrivialPart :
    V.starProjection.Reduces (halmosTrivialPart U V) :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    V.starProjection_isSymmetric
    fun y hy => projection_mem_halmosTrivialPart_right U V (x := y) hy

/-- **`U` is split by the trivial/generic decomposition.**  The trivial-part
projector maps `U` into itself, so a vector of `U` decomposes into a trivial and
a generic piece each still in `U`. -/
theorem starProjection_trivial_mem_left {x : H} (hx : x ∈ U) :
    (halmosTrivialPart U V).starProjection x ∈ U := by
  have h := ContinuousLinearMap.starProjection_apply_comm_of_reduces
    U.starProjection (halmosTrivialPart U V)
    (starProjection_left_reduces_halmosTrivialPart U V) x
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact h ▸ U.starProjection_apply_mem _

/-- The same for `V`. -/
theorem starProjection_trivial_mem_right {x : H} (hx : x ∈ V) :
    (halmosTrivialPart U V).starProjection x ∈ V := by
  have h := ContinuousLinearMap.starProjection_apply_comm_of_reduces
    V.starProjection (halmosTrivialPart U V)
    (starProjection_right_reduces_halmosTrivialPart U V) x
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact h ▸ V.starProjection_apply_mem _

omit [CompleteSpace H] in
/-- A vector in both `U` and `Uᗮ` is zero. -/
private theorem eq_zero_of_mem_of_mem_orthogonal {K : Submodule 𝕜 H} {x : H}
    (h₁ : x ∈ K) (h₂ : x ∈ Kᗮ) : x = 0 :=
  inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp h₂ x h₁)

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- **The part of `U` inside the trivial summand is `common ⊔ source`.**  The
other two elementary summands lie in `Uᗮ`, so they contribute nothing. -/
theorem inf_halmosTrivialPart_left :
    U ⊓ halmosTrivialPart U V =
      halmosCommonPart U V ⊔ halmosSourceDefect U V := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxU, hxT⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hxT
    -- `p` already lies in `U`; hence so does `q`, which also lies in `Uᗮ`.
    have hcsU : halmosCommonPart U V ⊔ halmosSourceDefect U V ≤ U :=
      sup_le inf_le_left inf_le_left
    have hteUc : halmosTargetDefect U V ⊔ halmosExteriorPart U V ≤ Uᗮ :=
      sup_le inf_le_left inf_le_left
    have hpU : p ∈ U := hcsU hp
    have hqU : q ∈ U := by
      have hq' : q = p + q - p := by abel
      rw [hq']
      exact U.sub_mem hxU hpU
    have hqUc : q ∈ Uᗮ := hteUc hq
    rw [eq_zero_of_mem_of_mem_orthogonal hqU hqUc, add_zero]
    exact hp
  · exact sup_le (le_inf inf_le_left (halmosCommonPart_le_trivial U V))
      (le_inf inf_le_left (halmosSourceDefect_le_trivial U V))

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- **The part of `V` inside the trivial summand is `common ⊔ target`.** -/
theorem inf_halmosTrivialPart_right :
    V ⊓ halmosTrivialPart U V =
      halmosCommonPart U V ⊔ halmosTargetDefect U V := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxV, hxT⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hxT
    -- Here the `V`-part is split across the two halves, so regroup by hand.
    obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨t, ht, e, he, rfl⟩ := Submodule.mem_sup.mp hq
    have hcV : c ∈ V := hc.2
    have htV : t ∈ V := ht.2
    have hsVc : s ∈ Vᗮ := hs.2
    have heVc : e ∈ Vᗮ := he.2
    have hrest : s + e ∈ V := by
      have : s + e = c + s + (t + e) - (c + t) := by abel
      rw [this]
      exact V.sub_mem hxV (V.add_mem hcV htV)
    have hrestc : s + e ∈ Vᗮ := Vᗮ.add_mem hsVc heVc
    have hse : s + e = 0 := eq_zero_of_mem_of_mem_orthogonal hrest hrestc
    have hsplit : c + s + (t + e) = c + t + (s + e) := by abel
    rw [hsplit, hse, add_zero]
    exact Submodule.mem_sup.mpr ⟨c, hc, t, ht, rfl⟩
  · exact sup_le (le_inf inf_le_right (halmosCommonPart_le_trivial U V))
      (le_inf inf_le_right (halmosTargetDefect_le_trivial U V))

/-- **`U` is the join of its trivial and generic parts.** -/
theorem eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart :
    U = (U ⊓ halmosTrivialPart U V) ⊔ (U ⊓ halmosGenericPart U V) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  refine Submodule.mem_sup.mpr
    ⟨(halmosTrivialPart U V).starProjection x,
      ⟨starProjection_trivial_mem_left U V hx,
        (halmosTrivialPart U V).starProjection_apply_mem x⟩,
      x - (halmosTrivialPart U V).starProjection x,
      ⟨U.sub_mem hx (starProjection_trivial_mem_left U V hx),
        (halmosTrivialPart U V).sub_starProjection_mem_orthogonal x⟩, by abel⟩

/-- The same for `V`. -/
theorem eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart_right :
    V = (V ⊓ halmosTrivialPart U V) ⊔ (V ⊓ halmosGenericPart U V) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  refine Submodule.mem_sup.mpr
    ⟨(halmosTrivialPart U V).starProjection x,
      ⟨starProjection_trivial_mem_right U V hx,
        (halmosTrivialPart U V).starProjection_apply_mem x⟩,
      x - (halmosTrivialPart U V).starProjection x,
      ⟨V.sub_mem hx (starProjection_trivial_mem_right U V hx),
        (halmosTrivialPart U V).sub_starProjection_mem_orthogonal x⟩, by abel⟩

end Structure

variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- The common part and the source defect are jointly complemented. -/
noncomputable instance instHasOrthogonalProjectionCommonSupSource :
    (halmosCommonPart U₁ V₁ ⊔ halmosSourceDefect U₁ V₁).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal _ _
    (halmosCommon_le_sourceDefect_orthogonal U₁ V₁)

/-- The target defect and the exterior part are jointly complemented. -/
noncomputable instance instHasOrthogonalProjectionTargetSupExterior :
    (halmosTargetDefect U₁ V₁ ⊔ halmosExteriorPart U₁ V₁).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal _ _
    (halmosTargetDefect_le_exterior_orthogonal U₁ V₁)

omit [CompleteSpace H₁] [U₁.HasOrthogonalProjection] [V₁.HasOrthogonalProjection] in
/-- The two halves of the trivial part are orthogonal. -/
theorem commonSupSource_le_orthogonal_targetSupExterior :
    halmosCommonPart U₁ V₁ ⊔ halmosSourceDefect U₁ V₁ ≤
      (halmosTargetDefect U₁ V₁ ⊔ halmosExteriorPart U₁ V₁)ᗮ :=
  sup_le_orthogonal_sup (halmosCommon_le_targetDefect_orthogonal U₁ V₁)
    (halmosCommon_le_exterior_orthogonal U₁ V₁)
    (halmosSourceDefect_le_targetDefect_orthogonal U₁ V₁)
    (halmosSourceDefect_le_exterior_orthogonal U₁ V₁)

/-- **The trivial-part isometry**, glued from the four elementary ones. -/
noncomputable def halmosTrivialEquiv
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂) :
    halmosTrivialPart U₁ V₁ ≃ₗᵢ[𝕜] halmosTrivialPart U₂ V₂ :=
  TauCeti.orthogonalSupGlue
    (commonSupSource_le_orthogonal_targetSupExterior U₁ V₁)
    (commonSupSource_le_orthogonal_targetSupExterior U₂ V₂)
    (TauCeti.orthogonalSupGlue (halmosCommon_le_sourceDefect_orthogonal U₁ V₁)
      (halmosCommon_le_sourceDefect_orthogonal U₂ V₂) ec es)
    (TauCeti.orthogonalSupGlue (halmosTargetDefect_le_exterior_orthogonal U₁ V₁)
      (halmosTargetDefect_le_exterior_orthogonal U₂ V₂) et ee)

/-- **The global isometry**, glued from the trivial part and the generic
remainder.  `halmosGenericPart` is by definition the orthogonal complement of
`halmosTrivialPart`, so this is exactly the ambient-complement glue. -/
noncomputable def halmosGlobalEquiv
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    H₁ ≃ₗᵢ[𝕜] H₂ :=
  TauCeti.orthogonalGlue (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee) eg

/-- On the trivial part the global isometry is the trivial-part one. -/
theorem halmosGlobalEquiv_apply_of_mem_trivial
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    {x : H₁} (hx : x ∈ halmosTrivialPart U₁ V₁) :
    halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x =
      (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hx⟩ : H₂) :=
  TauCeti.orthogonalGlue_apply_of_mem _ _ hx

/-- On the generic part the global isometry is the generic one. -/
theorem halmosGlobalEquiv_apply_of_mem_generic
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    {x : H₁} (hx : x ∈ halmosGenericPart U₁ V₁) :
    halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x = (eg ⟨x, hx⟩ : H₂) :=
  TauCeti.orthogonalGlue_apply_of_mem_orthogonal _ _ hx

/-! ### How the trivial-part isometry acts on each elementary summand

`halmosTrivialEquiv` is a nested pair of `orthogonalSupGlue`s, so reading it off
on a summand is two applications of `coe_orthogonalSupGlue` followed by the
matching `supGlueAmbient_apply_of_mem_left/right`.
-/

variable (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)

omit [CompleteSpace H₂] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- On the common part, the glued trivial equivalence is the common-part
component `ec`. -/
theorem coe_halmosTrivialEquiv_of_mem_common {x : H₁}
    (hx : x ∈ halmosCommonPart U₁ V₁) (hxT : x ∈ halmosTrivialPart U₁ V₁) :
    (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hxT⟩ : H₂) =
      (ec ⟨x, hx⟩ : H₂) := by
  rw [halmosTrivialEquiv, TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_left (commonSupSource_le_orthogonal_targetSupExterior U₁
      V₁) _ _ (Submodule.mem_sup_left hx),
    TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_left (halmosCommon_le_sourceDefect_orthogonal U₁ V₁) _ _ hx]

omit [CompleteSpace H₂] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- On the source defect `U ⊓ Vᗮ`, the glued trivial equivalence is the
source-defect component `es`. -/
theorem coe_halmosTrivialEquiv_of_mem_source {x : H₁}
    (hx : x ∈ halmosSourceDefect U₁ V₁) (hxT : x ∈ halmosTrivialPart U₁ V₁) :
    (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hxT⟩ : H₂) =
      (es ⟨x, hx⟩ : H₂) := by
  rw [halmosTrivialEquiv, TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_left (commonSupSource_le_orthogonal_targetSupExterior U₁
      V₁) _ _ (Submodule.mem_sup_right hx),
    TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_right (halmosCommon_le_sourceDefect_orthogonal U₁ V₁) _
      _ hx]

omit [CompleteSpace H₂] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- On the target defect `Uᗮ ⊓ V`, the glued trivial equivalence is the
target-defect component `et`. -/
theorem coe_halmosTrivialEquiv_of_mem_target {x : H₁}
    (hx : x ∈ halmosTargetDefect U₁ V₁) (hxT : x ∈ halmosTrivialPart U₁ V₁) :
    (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hxT⟩ : H₂) =
      (et ⟨x, hx⟩ : H₂) := by
  rw [halmosTrivialEquiv, TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_right (commonSupSource_le_orthogonal_targetSupExterior
      U₁ V₁) _ _ (Submodule.mem_sup_left hx),
    TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_left (halmosTargetDefect_le_exterior_orthogonal U₁ V₁) _
      _ hx]

omit [CompleteSpace H₂] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- On the exterior `Uᗮ ⊓ Vᗮ`, the glued trivial equivalence is the exterior
component `ee`. -/
theorem coe_halmosTrivialEquiv_of_mem_exterior {x : H₁}
    (hx : x ∈ halmosExteriorPart U₁ V₁) (hxT : x ∈ halmosTrivialPart U₁ V₁) :
    (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hxT⟩ : H₂) =
      (ee ⟨x, hx⟩ : H₂) := by
  rw [halmosTrivialEquiv, TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_right (commonSupSource_le_orthogonal_targetSupExterior
      U₁ V₁) _ _ (Submodule.mem_sup_right hx),
    TauCeti.coe_orthogonalSupGlue,
    TauCeti.supGlueAmbient_apply_of_mem_right (halmosTargetDefect_le_exterior_orthogonal U₁ V₁)
      _ _ hx]

/-- The global isometry carries the trivial part onto the trivial part. -/
theorem map_halmosGlobalEquiv_trivial
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosTrivialPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosTrivialPart U₂ V₂ :=
  TauCeti.map_orthogonalGlue _ _

/-- The global isometry carries the generic part onto the generic part. -/
theorem map_halmosGlobalEquiv_generic
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosGenericPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosGenericPart U₂ V₂ :=
  TauCeti.map_orthogonalGlue_orthogonal _ _

/-- The assembled isometry carries the common summand onto the common summand. -/
theorem map_halmosGlobalEquiv_common
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosCommonPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosCommonPart U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hct : c ∈ halmosTrivialPart U₁ V₁ := halmosCommonPart_le_trivial U₁ V₁ hc
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg c ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_common U₁ V₁ U₂ V₂ ec es et ee hc hct]
    exact (ec ⟨c, hc⟩).2
  · intro d hd
    refine ⟨(ec.symm ⟨d, hd⟩ : H₁), (ec.symm ⟨d, hd⟩).2, ?_⟩
    have hct : (ec.symm ⟨d, hd⟩ : H₁) ∈ halmosTrivialPart U₁ V₁ :=
      halmosCommonPart_le_trivial U₁ V₁ (ec.symm ⟨d, hd⟩).2
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = d
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_common U₁ V₁ U₂ V₂ ec es et ee
        (ec.symm ⟨d, hd⟩).2 hct]
    simp
/-- The assembled isometry carries the source summand onto the source summand. -/
theorem map_halmosGlobalEquiv_source
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosSourceDefect U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosSourceDefect U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hct : c ∈ halmosTrivialPart U₁ V₁ := halmosSourceDefect_le_trivial U₁ V₁ hc
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg c ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_source U₁ V₁ U₂ V₂ ec es et ee hc hct]
    exact (es ⟨c, hc⟩).2
  · intro d hd
    refine ⟨(es.symm ⟨d, hd⟩ : H₁), (es.symm ⟨d, hd⟩).2, ?_⟩
    have hct : (es.symm ⟨d, hd⟩ : H₁) ∈ halmosTrivialPart U₁ V₁ :=
      halmosSourceDefect_le_trivial U₁ V₁ (es.symm ⟨d, hd⟩).2
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = d
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_source U₁ V₁ U₂ V₂ ec es et ee
        (es.symm ⟨d, hd⟩).2 hct]
    simp
/-- The assembled isometry carries the target summand onto the target summand. -/
theorem map_halmosGlobalEquiv_target
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosTargetDefect U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosTargetDefect U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hct : c ∈ halmosTrivialPart U₁ V₁ := halmosTargetDefect_le_trivial U₁ V₁ hc
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg c ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_target U₁ V₁ U₂ V₂ ec es et ee hc hct]
    exact (et ⟨c, hc⟩).2
  · intro d hd
    refine ⟨(et.symm ⟨d, hd⟩ : H₁), (et.symm ⟨d, hd⟩).2, ?_⟩
    have hct : (et.symm ⟨d, hd⟩ : H₁) ∈ halmosTrivialPart U₁ V₁ :=
      halmosTargetDefect_le_trivial U₁ V₁ (et.symm ⟨d, hd⟩).2
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = d
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_target U₁ V₁ U₂ V₂ ec es et ee
        (et.symm ⟨d, hd⟩).2 hct]
    simp
/-- The assembled isometry carries the exterior summand onto the exterior summand. -/
theorem map_halmosGlobalEquiv_exterior
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂) :
    (halmosExteriorPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosExteriorPart U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hct : c ∈ halmosTrivialPart U₁ V₁ := halmosExteriorPart_le_trivial U₁ V₁ hc
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg c ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_exterior U₁ V₁ U₂ V₂ ec es et ee hc hct]
    exact (ee ⟨c, hc⟩).2
  · intro d hd
    refine ⟨(ee.symm ⟨d, hd⟩ : H₁), (ee.symm ⟨d, hd⟩).2, ?_⟩
    have hct : (ee.symm ⟨d, hd⟩ : H₁) ∈ halmosTrivialPart U₁ V₁ :=
      halmosExteriorPart_le_trivial U₁ V₁ (ee.symm ⟨d, hd⟩).2
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = d
    rw [halmosGlobalEquiv_apply_of_mem_trivial U₁ V₁ U₂ V₂ ec es et ee eg hct,
      coe_halmosTrivialEquiv_of_mem_exterior U₁ V₁ U₂ V₂ ec es et ee
        (ee.symm ⟨d, hd⟩).2 hct]
    simp

/-- The assembled isometry carries the `U`-part of the generic summand where the
generic hypothesis says it does. -/
theorem map_halmosGlobalEquiv_inf_generic_left
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    (hgU : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ U₂ ↔ (y : H₁) ∈ U₁)) :
    (U₁ ⊓ halmosGenericPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      U₂ ⊓ halmosGenericPart U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨hxU, hxg⟩, rfl⟩
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_generic U₁ V₁ U₂ V₂ ec es et ee eg hxg]
    exact ⟨(hgU ⟨x, hxg⟩).mpr hxU, (eg ⟨x, hxg⟩).2⟩
  · rintro y ⟨hyU, hyg⟩
    refine ⟨(eg.symm ⟨y, hyg⟩ : H₁), ⟨?_, (eg.symm ⟨y, hyg⟩).2⟩, ?_⟩
    · refine (hgU (eg.symm ⟨y, hyg⟩)).mp ?_
      simpa using hyU
    · change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = y
      rw [halmosGlobalEquiv_apply_of_mem_generic U₁ V₁ U₂ V₂ ec es et ee eg
        (eg.symm ⟨y, hyg⟩).2]
      simp

/-- The same for `V`. -/
theorem map_halmosGlobalEquiv_inf_generic_right
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    (hgV : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ V₂ ↔ (y : H₁) ∈ V₁)) :
    (V₁ ⊓ halmosGenericPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      V₂ ⊓ halmosGenericPart U₂ V₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨hxV, hxg⟩, rfl⟩
    change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x ∈ _
    rw [halmosGlobalEquiv_apply_of_mem_generic U₁ V₁ U₂ V₂ ec es et ee eg hxg]
    exact ⟨(hgV ⟨x, hxg⟩).mpr hxV, (eg ⟨x, hxg⟩).2⟩
  · rintro y ⟨hyV, hyg⟩
    refine ⟨(eg.symm ⟨y, hyg⟩ : H₁), ⟨?_, (eg.symm ⟨y, hyg⟩).2⟩, ?_⟩
    · refine (hgV (eg.symm ⟨y, hyg⟩)).mp ?_
      simpa using hyV
    · change halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg _ = y
      rw [halmosGlobalEquiv_apply_of_mem_generic U₁ V₁ U₂ V₂ ec es et ee eg
        (eg.symm ⟨y, hyg⟩).2]
      simp

/-- **The assembled isometry carries `U₁` onto `U₂`.** -/
theorem map_halmosGlobalEquiv_left
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    (hgU : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ U₂ ↔ (y : H₁) ∈ U₁)) :
    U₁.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap = U₂ := by
  have hsplit : U₁.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      ((U₁ ⊓ halmosTrivialPart U₁ V₁) ⊔ (U₁ ⊓ halmosGenericPart U₁ V₁)).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap :=
    congrArg (fun K : Submodule 𝕜 H₁ =>
      K.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap)
      (eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart U₁ V₁)
  rw [hsplit, Submodule.map_sup, inf_halmosTrivialPart_left U₁ V₁, Submodule.map_sup,
    map_halmosGlobalEquiv_common U₁ V₁ U₂ V₂ ec es et ee eg,
    map_halmosGlobalEquiv_source U₁ V₁ U₂ V₂ ec es et ee eg,
    map_halmosGlobalEquiv_inf_generic_left U₁ V₁ U₂ V₂ ec es et ee eg hgU,
    ← inf_halmosTrivialPart_left U₂ V₂,
    ← eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart U₂ V₂]

/-- **The assembled isometry carries `V₁` onto `V₂`.** -/
theorem map_halmosGlobalEquiv_right
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    (hgV : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ V₂ ↔ (y : H₁) ∈ V₁)) :
    V₁.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap = V₂ := by
  have hsplit : V₁.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      ((V₁ ⊓ halmosTrivialPart U₁ V₁) ⊔ (V₁ ⊓ halmosGenericPart U₁ V₁)).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap :=
    congrArg (fun K : Submodule 𝕜 H₁ =>
      K.map (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap)
      (eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart_right U₁ V₁)
  rw [hsplit, Submodule.map_sup, inf_halmosTrivialPart_right U₁ V₁, Submodule.map_sup,
    map_halmosGlobalEquiv_common U₁ V₁ U₂ V₂ ec es et ee eg,
    map_halmosGlobalEquiv_target U₁ V₁ U₂ V₂ ec es et ee eg,
    map_halmosGlobalEquiv_inf_generic_right U₁ V₁ U₂ V₂ ec es et ee eg hgV,
    ← inf_halmosTrivialPart_right U₂ V₂,
    ← eq_sup_inf_halmosTrivialPart_inf_halmosGenericPart_right U₂ V₂]

/-- **Brick (2), complete.**  Matched isometries of the four elementary Halmos
summands together with a generic-part isometry that respects `U` and `V`
assemble into a unitary equivalence of the ordered pairs.

The elementary summands need no compatibility hypothesis: `common ≤ U ⊓ V`,
`source ≤ U ⊓ Vᗮ`, `target ≤ Uᗮ ⊓ V` and `exterior ≤ Uᗮ ⊓ Vᗮ`, so *any*
isometry between matched summands lands where it must.  The only real input is
`hgU`/`hgV` on the generic part — which is exactly what brick (1), the generic
`2 × 2` model, has to supply. -/
theorem pairOfSubspacesUnitaryEquivalent_of_summandEquivs
    (ec' : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es' : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et' : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee' : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂)
    (hgU : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ U₂ ↔ (y : H₁) ∈ U₁))
    (hgV : ∀ y : halmosGenericPart U₁ V₁, ((eg y : H₂) ∈ V₂ ↔ (y : H₁) ∈ V₁)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ :=
  ⟨halmosGlobalEquiv U₁ V₁ U₂ V₂ ec' es' et' ee' eg,
    map_halmosGlobalEquiv_left U₁ V₁ U₂ V₂ ec' es' et' ee' eg hgU,
    map_halmosGlobalEquiv_right U₁ V₁ U₂ V₂ ec' es' et' ee' eg hgV⟩

end DavisKahan
end TauCeti
