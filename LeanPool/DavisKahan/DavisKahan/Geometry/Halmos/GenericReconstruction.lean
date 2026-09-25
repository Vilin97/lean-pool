/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericPosition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ModulusConjugation

/-!
# Brick (1): the generic part is reconstructed from its cosine block

`GenericPosition.lean` puts the second projection into `2 × 2` block form on the
generic part, in the coordinates `M = U ⊓ generic`, `N = Uᗮ ⊓ generic`:

```
P_U = [[1, 0], [0, 0]]        P_V = [[A, B'], [B, D]]
```

with `A` the cosine block, `B` the cross block, `B'` its adjoint, and `D` the
sine block.  This module proves that the *upper-left corner alone* determines
the whole pair: a unitary `W : M₁ ≃ₗᵢ M₂` intertwining `A₁` and `A₂` extends to
a unitary of the generic parts carrying `U₁, V₁` to `U₂, V₂`.

The extension is forced, not chosen.  The polar decomposition `B = Φ |B|` has
`Φ : M ≃ₗᵢ N` unitary (`genericHalvesEquiv`), so `N` is a copy of `M` and the
only candidate for the `N`-component of the extension is `W' := Φ₂ W Φ₁⁻¹`.
That candidate works because each of the other three blocks is pinned by `A`:

* `|B|` is the unique nonnegative square root of `A - A²`, so `W` intertwines
  it (`ContinuousLinearMap.modulus_conj_apply`), hence `W' B₁ = B₂ W`;
* `D` is pinned by `D B = B (1 - A)` together with the *dense range* of `B`;
* `B'` is the adjoint of `B`, so it follows from the `B` case.

## What this closes

Brick (1), and with `Assembly.lean`'s brick (2) the whole converse of
Davis--Kahan Theorem 3.1.  The frontier statement
`DavisKahan1970.twoProjection_operator_classification` is grounded by `:=` on
the classification proved at the end of this file.

The frontier used to record the generic part by `genericHalmosCosineSq`, the
compression of the symmetrized `P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`.  On the generic
part that is `A` on the `M`-half and `1 - D` on the `N`-half — `A ⊕ A` — so a
unitary equivalence of the recorded invariants was an equivalence of `A₁ ⊕ A₁'`
with `A₂ ⊕ A₂'`, and halving that multiplicity is Hahn--Hellinger theory.  The
invariant now records the cosine block on the `U`-side, which is what Davis and
Kahan state Theorem 3.1 for, and multiplicity theory left the critical path.

## Main results

* `TauCeti.DavisKahan.genericTransport`:
  the extension `halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂`.
* `..._mem_left_iff` and `..._mem_right_iff`: it carries `U₁` to `U₂` and `V₁`
  to `V₂`.
* `..._pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv`: the pair
  equivalence, assembled with the four elementary summand isometries through
  `Assembly.lean`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The `M ⊕ N` decomposition of a generic vector -/

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- Every generic vector splits across the two halves. -/
theorem exists_halves_decomposition {y : H} (hy : y ∈ halmosGenericPart U V) :
    ∃ (m : genericLeftHalf U V) (n : genericRightHalf U V),
      y = (m : H) + (n : H) := by
  refine ⟨⟨U.starProjection y, U.starProjection_apply_mem y,
      projection_mem_halmosGenericPart_left U V hy⟩,
    ⟨y - U.starProjection y, sub_starProjection_mem_genericRightHalf U V hy⟩, ?_⟩
  simp

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- A vector of the `U`-half plus a vector of the `Uᗮ`-half lies in the `U`-half
only when the second is zero. -/
theorem add_mem_genericLeftHalf_iff (m : genericLeftHalf U V)
    (n : genericRightHalf U V) :
    ((m : H) + (n : H)) ∈ genericLeftHalf U V ↔ n = 0 := by
  constructor
  · intro h
    have hn : (n : H) ∈ genericLeftHalf U V := by
      have hsub := (genericLeftHalf U V).sub_mem h m.2
      simpa using hsub
    have hzero : ⟪(n : H), (n : H)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).mp
        (genericLeftHalf_le_orthogonal_genericRightHalf U V hn) _ n.2
    exact Subtype.ext (inner_self_eq_zero.mp hzero)
  · rintro rfl
    simp

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- On the generic part, membership in `U` is membership in the `U`-half. -/
theorem mem_left_iff_mem_genericLeftHalf {y : H}
    (hy : y ∈ halmosGenericPart U V) :
    y ∈ U ↔ y ∈ genericLeftHalf U V :=
  ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩

/-- The range of the cross block is dense in the `Uᗮ`-half. -/
theorem dense_range_genericCrossBlock :
    Dense (Set.range (genericCrossBlock U V)) := by
  have hclosed : (LinearMap.range (genericCrossBlock U V : genericLeftHalf U V →ₗ[𝕜]
      genericRightHalf U V)).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr
      (orthogonal_range_genericCrossBlock_eq_bot U V)
  have hdense := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosed
  simpa [LinearMap.coe_range] using hdense

end OneSpace

/-! ## Transporting the four blocks -/

section TwoSpaces

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]
variable (W : genericLeftHalf U₁ V₁ ≃ₗᵢ[𝕜] genericLeftHalf U₂ V₂)
variable (hW : ∀ m, W (genericCosineBlock U₁ V₁ m) = genericCosineBlock U₂ V₂ (W m))

include hW in
/-- A unitary intertwining the cosine blocks intertwines the Gram operators of
the cross blocks, because `B⋆ B = A - A²`. -/
theorem gram_intertwine_of_cosineBlock (m : genericLeftHalf U₁ V₁) :
    W (((genericCrossBlock U₁ V₁).adjoint ∘L genericCrossBlock U₁ V₁) m) =
      ((genericCrossBlock U₂ V₂).adjoint ∘L genericCrossBlock U₂ V₂) (W m) := by
  rw [adjoint_comp_genericCrossBlock, adjoint_comp_genericCrossBlock]
  simp [hW]

/-! ### Functional calculus on the generic halves

Everything from `modulus_intertwine_of_cosineBlock` onwards factors through the operator
modulus of the cross block.  Each generic left half is complete, so the local `RCLike`
operator instances supply the real functional calculus on both source algebras. -/


include hW in
/-- **Step 1.**  The intertwiner passes to the moduli of the cross blocks, by
uniqueness of the nonnegative square root of `A - A²`. -/
theorem modulus_intertwine_of_cosineBlock (m : genericLeftHalf U₁ V₁) :
    W ((genericCrossBlock U₁ V₁).modulus m) =
      (genericCrossBlock U₂ V₂).modulus (W m) :=
  ContinuousLinearMap.modulus_conj_apply W
    (gram_intertwine_of_cosineBlock U₁ V₁ U₂ V₂ W hW) m

/-- **Step 2.**  The forced companion of `W` on the `Uᗮ`-halves: conjugate by the
two polar equivalences `Φᵢ : Mᵢ ≃ₗᵢ Nᵢ`. -/
noncomputable def genericRightTransport :
    genericRightHalf U₁ V₁ ≃ₗᵢ[𝕜] genericRightHalf U₂ V₂ :=
  ((genericHalvesEquiv U₁ V₁).symm.trans W).trans (genericHalvesEquiv U₂ V₂)

/-- The transported right half is `W` conjugated by the two polar factors `Φ`:
unfold the composition. -/
theorem genericRightTransport_apply (n : genericRightHalf U₁ V₁) :
    genericRightTransport U₁ V₁ U₂ V₂ W n =
      genericHalvesEquiv U₂ V₂ (W ((genericHalvesEquiv U₁ V₁).symm n)) :=
  rfl

include hW in
/-- **Step 3.**  `W' B₁ = B₂ W`.  This is where the polar identity `Φ |B| = B`
is used: `Φ₁⁻¹ B₁ = |B₁|`, step 1 moves `|B₁|` to `|B₂|`, and `Φ₂ |B₂| = B₂`. -/
theorem crossBlock_intertwine (m : genericLeftHalf U₁ V₁) :
    genericRightTransport U₁ V₁ U₂ V₂ W (genericCrossBlock U₁ V₁ m) =
      genericCrossBlock U₂ V₂ (W m) := by
  have hsymm : (genericHalvesEquiv U₁ V₁).symm (genericCrossBlock U₁ V₁ m) =
      (genericCrossBlock U₁ V₁).modulus m := by
    rw [← genericHalvesEquiv_modulus U₁ V₁ m, LinearIsometryEquiv.symm_apply_apply]
  rw [genericRightTransport_apply, hsymm,
    modulus_intertwine_of_cosineBlock U₁ V₁ U₂ V₂ W hW, genericHalvesEquiv_modulus]

include hW in
/-- **Step 4.**  `W' D₁ = D₂ W'`.  The two sides agree on the range of `B₁` by
`D B = B (1 - A)` and step 3, and that range is dense in the `Uᗮ`-half. -/
theorem sineBlock_intertwine (n : genericRightHalf U₁ V₁) :
    genericRightTransport U₁ V₁ U₂ V₂ W (genericSineBlock U₁ V₁ n) =
      genericSineBlock U₂ V₂ (genericRightTransport U₁ V₁ U₂ V₂ W n) := by
  have hDB₁ : ∀ m : genericLeftHalf U₁ V₁,
      genericSineBlock U₁ V₁ (genericCrossBlock U₁ V₁ m) =
        genericCrossBlock U₁ V₁ m -
          genericCrossBlock U₁ V₁ (genericCosineBlock U₁ V₁ m) := by
    intro m
    have h := congrArg (fun f : genericLeftHalf U₁ V₁ →L[𝕜] genericRightHalf U₁ V₁ => f m)
      (genericSineBlock_comp_genericCrossBlock U₁ V₁)
    simpa using h
  have hDB₂ : ∀ m : genericLeftHalf U₂ V₂,
      genericSineBlock U₂ V₂ (genericCrossBlock U₂ V₂ m) =
        genericCrossBlock U₂ V₂ m -
          genericCrossBlock U₂ V₂ (genericCosineBlock U₂ V₂ m) := by
    intro m
    have h := congrArg (fun f : genericLeftHalf U₂ V₂ →L[𝕜] genericRightHalf U₂ V₂ => f m)
      (genericSineBlock_comp_genericCrossBlock U₂ V₂)
    simpa using h
  -- The two continuous maps agree on the range of `B₁` ...
  have hkey : Set.EqOn
      (fun x => genericRightTransport U₁ V₁ U₂ V₂ W (genericSineBlock U₁ V₁ x))
      (fun x => genericSineBlock U₂ V₂ (genericRightTransport U₁ V₁ U₂ V₂ W x))
      (Set.range (genericCrossBlock U₁ V₁)) := by
    rintro _ ⟨m, rfl⟩
    simp only
    rw [hDB₁ m, map_sub, crossBlock_intertwine U₁ V₁ U₂ V₂ W hW,
      crossBlock_intertwine U₁ V₁ U₂ V₂ W hW, hDB₂ (W m), hW]
  -- ... and that range is dense.
  have hcont₁ : Continuous fun x : genericRightHalf U₁ V₁ =>
      genericRightTransport U₁ V₁ U₂ V₂ W (genericSineBlock U₁ V₁ x) :=
    (genericRightTransport U₁ V₁ U₂ V₂ W).continuous.comp
      (genericSineBlock U₁ V₁).continuous
  have hcont₂ : Continuous fun x : genericRightHalf U₁ V₁ =>
      genericSineBlock U₂ V₂ (genericRightTransport U₁ V₁ U₂ V₂ W x) :=
    (genericSineBlock U₂ V₂).continuous.comp
      (genericRightTransport U₁ V₁ U₂ V₂ W).continuous
  exact congrFun
    (Continuous.ext_on (dense_range_genericCrossBlock U₁ V₁) hcont₁ hcont₂ hkey) n

include hW in
/-- **Step 5.**  `W B'₁ = B'₂ W'`, by taking adjoints in step 3. -/
theorem mirrorBlock_intertwine (n : genericRightHalf U₁ V₁) :
    W (genericCrossBlockMirror U₁ V₁ n) =
      genericCrossBlockMirror U₂ V₂ (genericRightTransport U₁ V₁ U₂ V₂ W n) := by
  refine ext_inner_left 𝕜 fun m₂ => ?_
  obtain ⟨m, rfl⟩ := W.surjective m₂
  calc ⟪W m, W (genericCrossBlockMirror U₁ V₁ n)⟫_𝕜
      = ⟪m, genericCrossBlockMirror U₁ V₁ n⟫_𝕜 := W.inner_map_map _ _
    _ = ⟪genericCrossBlock U₁ V₁ m, n⟫_𝕜 := (inner_genericCrossBlock U₁ V₁ m n).symm
    _ = ⟪genericRightTransport U₁ V₁ U₂ V₂ W (genericCrossBlock U₁ V₁ m),
          genericRightTransport U₁ V₁ U₂ V₂ W n⟫_𝕜 :=
        ((genericRightTransport U₁ V₁ U₂ V₂ W).inner_map_map _ _).symm
    _ = ⟪genericCrossBlock U₂ V₂ (W m),
          genericRightTransport U₁ V₁ U₂ V₂ W n⟫_𝕜 := by
        rw [crossBlock_intertwine U₁ V₁ U₂ V₂ W hW]
    _ = ⟪W m, genericCrossBlockMirror U₂ V₂
          (genericRightTransport U₁ V₁ U₂ V₂ W n)⟫_𝕜 :=
        inner_genericCrossBlock U₂ V₂ _ _

/-! ## Gluing the two halves -/

/-- **Step 6.**  The extension of `W` to the whole generic part. -/
noncomputable def genericTransport :
    halmosGenericPart U₁ V₁ ≃ₗᵢ[𝕜] halmosGenericPart U₂ V₂ :=
  (LinearIsometryEquiv.ofEq _ _ (halmosGenericPart_eq_sup_inf_left U₁ V₁)).trans
    ((orthogonalSupGlue (genericLeftHalf_le_orthogonal_genericRightHalf U₁ V₁)
          (genericLeftHalf_le_orthogonal_genericRightHalf U₂ V₂) W
          (genericRightTransport U₁ V₁ U₂ V₂ W)).trans
      (LinearIsometryEquiv.ofEq _ _ (halmosGenericPart_eq_sup_inf_left U₂ V₂).symm))

/-- The generic transport is the restriction of the ambient glue of `W` and its
right-half transport. -/
theorem coe_genericTransport (y : halmosGenericPart U₁ V₁) :
    (genericTransport U₁ V₁ U₂ V₂ W y : H₂) =
      supGlueAmbient W (genericRightTransport U₁ V₁ U₂ V₂ W) (y : H₁) := by
  simp [genericTransport, coe_orthogonalSupGlue]

/-- The glue on a decomposed vector: `W` on the `M`-part, `W'` on the `N`-part. -/
theorem supGlueAmbient_halves (m : genericLeftHalf U₁ V₁)
    (n : genericRightHalf U₁ V₁) :
    supGlueAmbient W (genericRightTransport U₁ V₁ U₂ V₂ W)
        ((m : H₁) + (n : H₁)) =
      (W m : H₂) + (genericRightTransport U₁ V₁ U₂ V₂ W n : H₂) := by
  rw [map_add,
    supGlueAmbient_apply_of_mem_left
      (genericLeftHalf_le_orthogonal_genericRightHalf U₁ V₁) _ _ m.2,
    supGlueAmbient_apply_of_mem_right
      (genericLeftHalf_le_orthogonal_genericRightHalf U₁ V₁) _ _ n.2]

/-! ## The extension is pair-compatible -/

/-- **The extension carries `U₁` to `U₂`.**  Immediate from the glue: it maps
the `U`-half onto the `U`-half and the `Uᗮ`-half onto the `Uᗮ`-half. -/
theorem mem_left_genericTransport_iff (y : halmosGenericPart U₁ V₁) :
    ((genericTransport U₁ V₁ U₂ V₂ W y : halmosGenericPart U₂ V₂) : H₂) ∈ U₂ ↔
      (y : H₁) ∈ U₁ := by
  obtain ⟨m, n, hy⟩ := exists_halves_decomposition U₁ V₁ y.2
  have himg := coe_genericTransport U₁ V₁ U₂ V₂ W y
  rw [hy, supGlueAmbient_halves] at himg
  rw [mem_left_iff_mem_genericLeftHalf U₂ V₂
      (genericTransport U₁ V₁ U₂ V₂ W y).2,
    mem_left_iff_mem_genericLeftHalf U₁ V₁ y.2, himg, hy,
    add_mem_genericLeftHalf_iff, add_mem_genericLeftHalf_iff]
  constructor
  · intro h
    exact (genericRightTransport U₁ V₁ U₂ V₂ W).map_eq_zero_iff.mp h
  · rintro rfl
    simp

include hW in
/-- **The extension intertwines the second projections.**  Both sides are the
glue applied to `P_V y`, once the `2 × 2` block matrix of `P_V` is transported
entry by entry through steps 1--5. -/
theorem starProjection_right_genericTransport (y : halmosGenericPart U₁ V₁) :
    V₂.starProjection
        ((genericTransport U₁ V₁ U₂ V₂ W y : halmosGenericPart U₂ V₂) : H₂) =
      supGlueAmbient W (genericRightTransport U₁ V₁ U₂ V₂ W)
        (V₁.starProjection (y : H₁)) := by
  obtain ⟨m, n, hy⟩ := exists_halves_decomposition U₁ V₁ y.2
  have himg := coe_genericTransport U₁ V₁ U₂ V₂ W y
  rw [hy, supGlueAmbient_halves] at himg
  rw [himg, hy, map_add, map_add]
  -- The four blocks on each side.
  rw [starProjection_eq_cosineBlock_add_crossBlock U₂ V₂ (W m),
    starProjection_eq_mirror_add_sineBlock U₂ V₂
      (genericRightTransport U₁ V₁ U₂ V₂ W n),
    starProjection_eq_cosineBlock_add_crossBlock U₁ V₁ m,
    starProjection_eq_mirror_add_sineBlock U₁ V₁ n]
  -- Regroup the source side into an `M`-part and an `N`-part, then glue.
  have hregroup : ((genericCosineBlock U₁ V₁ m : genericLeftHalf U₁ V₁) : H₁) +
        ((genericCrossBlock U₁ V₁ m : genericRightHalf U₁ V₁) : H₁) +
        (((genericCrossBlockMirror U₁ V₁ n : genericLeftHalf U₁ V₁) : H₁) +
          ((genericSineBlock U₁ V₁ n : genericRightHalf U₁ V₁) : H₁)) =
      ((genericCosineBlock U₁ V₁ m + genericCrossBlockMirror U₁ V₁ n :
          genericLeftHalf U₁ V₁) : H₁) +
        ((genericCrossBlock U₁ V₁ m + genericSineBlock U₁ V₁ n :
          genericRightHalf U₁ V₁) : H₁) := by
    push_cast
    abel
  rw [hregroup, supGlueAmbient_halves, map_add, map_add,
    mirrorBlock_intertwine U₁ V₁ U₂ V₂ W hW, sineBlock_intertwine U₁ V₁ U₂ V₂ W hW,
    hW, crossBlock_intertwine U₁ V₁ U₂ V₂ W hW]
  push_cast
  abel

include hW in
/-- **The extension carries `V₁` to `V₂`.** -/
theorem mem_right_genericTransport_iff (y : halmosGenericPart U₁ V₁) :
    ((genericTransport U₁ V₁ U₂ V₂ W y : halmosGenericPart U₂ V₂) : H₂) ∈ V₂ ↔
      (y : H₁) ∈ V₁ := by
  have hgen : V₁.starProjection (y : H₁) ∈ halmosGenericPart U₁ V₁ :=
    projection_mem_halmosGenericPart_right U₁ V₁ y.2
  constructor
  · intro h
    have hfix : V₂.starProjection
        ((genericTransport U₁ V₁ U₂ V₂ W y : halmosGenericPart U₂ V₂) : H₂) =
        ((genericTransport U₁ V₁ U₂ V₂ W y : halmosGenericPart U₂ V₂) : H₂) :=
      Submodule.starProjection_eq_self_iff.mpr h
    rw [starProjection_right_genericTransport U₁ V₁ U₂ V₂ W hW,
      coe_genericTransport] at hfix
    have hinj : V₁.starProjection (y : H₁) = (y : H₁) := by
      -- Injectivity of the glue on the generic part.
      have hsub : (⟨V₁.starProjection (y : H₁), hgen⟩ :
          halmosGenericPart U₁ V₁) = y := by
        apply (genericTransport U₁ V₁ U₂ V₂ W).injective
        apply Subtype.ext
        rw [coe_genericTransport, coe_genericTransport]
        exact hfix
      exact congrArg Subtype.val hsub
    exact Submodule.starProjection_eq_self_iff.mp hinj
  · intro h
    have hfix : V₁.starProjection (y : H₁) = (y : H₁) :=
      Submodule.starProjection_eq_self_iff.mpr h
    have hkey := starProjection_right_genericTransport U₁ V₁ U₂ V₂ W hW y
    rw [hfix, ← coe_genericTransport] at hkey
    exact Submodule.starProjection_eq_self_iff.mp hkey

/-! ## Bricks (1) and (2) together -/

include hW in
/-- **Bricks (1) and (2), joined.**  Isometries of the four elementary Halmos
summands together with a unitary of the `U`-halves intertwining the cosine
blocks reconstruct a unitary equivalence of the ordered pairs.

Every hypothesis here is *data about the two pairs separately*: no map between
the ambient spaces is assumed.  That is what makes this the converse half of
Davis--Kahan Theorem 3.1 rather than a restatement of it. -/
theorem pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ :=
  pairOfSubspacesUnitaryEquivalent_of_summandEquivs U₁ V₁ U₂ V₂ ec es et ee
    (genericTransport U₁ V₁ U₂ V₂ W)
    (mem_left_genericTransport_iff U₁ V₁ U₂ V₂ W)
    (mem_right_genericTransport_iff U₁ V₁ U₂ V₂ W hW)

end TwoSpaces

/-! ## Theorem 3.1's operator-level spine, in the paper's own invariant -/

section Classification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Forward direction, in the paper's invariant.**  A pair-equivalence carries
the `U`-half of the generic part onto the `U`-half, and there it intertwines the
cosine blocks. -/
theorem exists_cosineBlockEquiv_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    ∃ W : genericLeftHalf U₁ V₁ ≃ₗᵢ[𝕜] genericLeftHalf U₂ V₂,
      ∀ m, W (genericCosineBlock U₁ V₁ m) = genericCosineBlock U₂ V₂ (W m) := by
  obtain ⟨e, hU, hV⟩ := h
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  have hGen := map_halmosGenericPart U₁ V₁ U₂ V₂ e hU hV
  have hM : (genericLeftHalf U₁ V₁).map e.toLinearMap = genericLeftHalf U₂ V₂ := by
    rw [genericLeftHalf, Submodule.map_inf _ hinj, hU, hGen]
  refine ⟨summandEquiv e _ hM, fun m => ?_⟩
  apply Subtype.ext
  simp only [coe_summandEquiv, genericCosineBlock, DavisKahan.Sylvester.compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  calc e ((genericLeftHalf U₁ V₁).starProjection (V₁.starProjection (m : H₁)))
      = (genericLeftHalf U₂ V₂).starProjection (e (V₁.starProjection (m : H₁))) :=
        isometryEquiv_intertwines_projection e hM _
    _ = (genericLeftHalf U₂ V₂).starProjection (V₂.starProjection (e (m : H₁))) :=
        congrArg (genericLeftHalf U₂ V₂).starProjection
          (isometryEquiv_intertwines_projection e hV (m : H₁))

/-- **The elementary half of Davis--Kahan 1970 Theorem 3.1's invariant.**

Equality of the four elementary Halmos summands, expressed as isometric
equivalences rather than as equal cardinals, so that no finite-rank substitute
is needed.  These are the first four fields of `SameHalmosCosineBlockInvariant`,
named separately because the paper states Theorem 3.1 and Corollary 3.1 as
"these multiplicities agree, *and* the angle data agree", with two different
readings of the second half. -/
structure SameHalmosTrivialDimensions : Prop where
  common : Nonempty
    (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty
    (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- Transport a nonempty isometric equivalence of submodules along equalities
of those submodules.  Needed because the two summand families below are equal
as submodules but the `≃ₗᵢ` type former does not rewrite. -/
private theorem nonempty_linearIsometryEquiv_congr
    {X X' : Submodule 𝕜 H₁} {Y Y' : Submodule 𝕜 H₂}
    (hX : X = X') (hY : Y = Y') (h : Nonempty (X ≃ₗᵢ[𝕜] Y)) :
    Nonempty (X' ≃ₗᵢ[𝕜] Y') :=
  h.map fun f =>
    ((LinearIsometryEquiv.ofEq X' X hX.symm).trans f).trans
      (LinearIsometryEquiv.ofEq Y Y' hY)

omit [U₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection] [CompleteSpace H₁]
  [CompleteSpace H₂] in
/-- Complementing the second subspace permutes the four elementary Halmos
summands: `U ⊓ V` swaps with `U ⊓ Vᗮ`, and `Uᗮ ⊓ V` with `Uᗮ ⊓ Vᗮ`. -/
theorem sameHalmosTrivialDimensions_orthogonal_right_iff :
    SameHalmosTrivialDimensions U₁ V₁ᗮ U₂ V₂ᗮ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ := by
  have hVV1 : V₁ᗮᗮ = V₁ := Submodule.orthogonal_orthogonal V₁
  have hVV2 : V₂ᗮᗮ = V₂ := Submodule.orthogonal_orthogonal V₂
  have e1 : U₁ ⊓ V₁ᗮᗮ = U₁ ⊓ V₁ := by rw [hVV1]
  have e2 : U₂ ⊓ V₂ᗮᗮ = U₂ ⊓ V₂ := by rw [hVV2]
  have e3 : U₁ᗮ ⊓ V₁ᗮᗮ = U₁ᗮ ⊓ V₁ := by rw [hVV1]
  have e4 : U₂ᗮ ⊓ V₂ᗮᗮ = U₂ᗮ ⊓ V₂ := by rw [hVV2]
  constructor
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨nonempty_linearIsometryEquiv_congr e1 e2 hs, hc,
      nonempty_linearIsometryEquiv_congr e3 e4 he, ht⟩
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨hs, nonempty_linearIsometryEquiv_congr e1.symm e2.symm hc,
      he, nonempty_linearIsometryEquiv_congr e3.symm e4.symm ht⟩

/-- **Davis--Kahan 1970 Theorem 3.1's complete invariant, in the paper's own
terms.**

The four elementary Halmos multiplicities, together with the
unitary-equivalence class of the angle operator `cos²Θ` *on the `U`-side* — the
compression of `P_V` to `U ⊓ generic`.  That is the operator whose spectral
multiplicity function the paper's Theorem 3.1 uses.

The source-facing Theorem 3.1,
`DavisKahan1970.twoProjection_operator_classification`, is grounded by `:=` on
the theorem below and splits this invariant into its two printed halves,
`SameHalmosTrivialDimensions` and the angle-operator equivalence.  This
structure used to record the symmetrized `P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`, which
on the generic part is the cosine block on the `U`-half and `1 - D` on the
`Uᗮ`-half — the same angle data with multiplicity doubled, which is what put
Hahn--Hellinger on the critical path. -/
structure SameHalmosCosineBlockInvariant : Prop where
  common : Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
  cosineBlock : ∃ W : genericLeftHalf U₁ V₁ ≃ₗᵢ[𝕜] genericLeftHalf U₂ V₂,
    ∀ m, W (genericCosineBlock U₁ V₁ m) = genericCosineBlock U₂ V₂ (W m)


/-- **Davis--Kahan 1970, Theorem 3.1: the operator-level classification, both
directions.**

Two ordered pairs of subspaces of two complex Hilbert spaces are unitarily
equivalent *as pairs* exactly when their four elementary Halmos summands are
isometric and their angle operators `cos²Θ` are unitarily equivalent.

No compactness, no finite dimension, no separability, no direct-integral
presentation, and — with the invariant read on the `U`-side, as the paper reads
it — no spectral-multiplicity theory: the reconstruction in
`pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv` is elementary, driven by
the polar decomposition of the Halmos cross block. -/
theorem pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosCosineBlockInvariant U₁ V₁ U₂ V₂ := by
  constructor
  · intro h
    obtain ⟨hc, hs, ht, he, _⟩ := sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
    exact ⟨hc, hs, ht, he, exists_cosineBlockEquiv_of_pairEquiv U₁ V₁ U₂ V₂ h⟩
  · rintro ⟨⟨ec⟩, ⟨es⟩, ⟨et⟩, ⟨ee⟩, W, hW⟩
    exact pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv U₁ V₁ U₂ V₂ W hW
      ec es et ee

end Classification

end DavisKahan
end TauCeti
