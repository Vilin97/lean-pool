/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationSpectrumCompact
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationContinuity

/-!
# Compactness of the Adic Spectrum `Spa(A, A⁺)`

We derive quasi-compactness of the adic spectrum `Spa(A, A⁺)` from the corresponding
statement for the full valuation spectrum `Spv A` (see
`ValuationSpectrum.instCompactSpace` in `ValuationSpectrumCompact.lean`).

## Route taken

Unlike `Spv A`, the set `Spa A A⁺ = Cont A ∩ ⋂_{a ∈ A⁺} {v | v.vle a 1}` is **not**
closed in `Spv A` in general: each `{v | v.vle a 1}` equals the **open** set
`basicOpen a 1` (since `¬ v.vle 1 0` always holds), and the continuity condition
`v.IsContinuous` is not in general a closed condition either. So the naive
"closed-in-compact" route does not work directly through the `Spv A` topology.

We therefore proceed through the Bool Huber embedding
`ιSpvBool : Spv A → (A × A → Bool)`. In the discrete Bool product:

* each coordinate condition `{r | r(a, 1) = true}` is clopen;
* `range ιSpvBool` is closed (from `ValuationSpectrumCompact`);
* under `[DiscreteTopology A]` the continuity condition `v ∈ Cont A` is
  automatic (`Cont A = univ`, `cont_eq_univ_of_discreteTopology`);

hence `ιSpvBool '' Spa A A⁺ = range ιSpvBool ∩ ⋂_{a ∈ A⁺} {r | r(a, 1) = true}`
is closed in the compact Hausdorff space `(A × A → Bool)`, so is compact. The
factorisation `ιSpv = (fun r p => boolToProp (r p)) ∘ ιSpvBool` transfers this to
compactness of `ιSpv '' Spa A A⁺` (continuous image), and finally
`ιSpv_isEmbedding.isCompact_iff` yields `IsCompact (Spa A A⁺ : Set (Spv A))` and
the `CompactSpace ↥(Spa A A⁺)` instance.

## Main results

* `image_spa_ιSpv_bool` : Characterisation of `ιSpvBool '' Spa A A⁺` in the
  discrete case as `range ιSpvBool ∩ ⋂_{a ∈ A⁺} {r | r(a, 1) = true}`.
* `isClosed_image_spa_ιSpv_bool` : The above image is closed in the Bool product.
* `isCompact_spa` : `Spa A A⁺` is a compact subset of `Spv A` (discrete case).
* `instCompactSpace_spa` : `CompactSpace ↥(Spa A A⁺)` (discrete case).
* `isCompact_spa_of_isClosed_image` : Abstract compactness criterion — given any
  closed subset `S` of `(A × A → Bool)` equal to `ιSpvBool '' Spa A A⁺` (up to
  intersection with the range), `Spa A A⁺` is compact.
* `isCompact_spa_of_tate_pseudouniformizer` : Compactness of `Spa A A⁺` for Tate
  rings with an explicit pseudo-uniformizer `π` generating the ideal of
  definition, `A₀ ⊆ A⁺`, and MulArchimedean hypothesis on valuations.

## Scope

The present file proves the compactness of `Spa(A, A⁺)` under two regimes:

1. `[DiscreteTopology A]`, matching the "discrete case first" design decision.
2. Tate rings with an explicit pseudo-uniformizer and MulArchimedean hypothesis
   on the value groups — see `isCompact_spa_of_tate_pseudouniformizer` below.

The general Huber case without MulArchimedean remains open and requires
coarsening to archimedean quotients (Wedhorn §7.1), which is future work.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 7.30, Corollary 7.32.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 445–477.
-/

open Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### Bool-embedding description of `Spa A A⁺` under `[DiscreteTopology A]` -/

/-- **Image of `Spa A A⁺` under `ιSpvBool` (discrete case).**

Under `[DiscreteTopology A]`, the image of the adic spectrum under the Bool Huber
embedding is exactly the intersection of `range ιSpvBool` with the coordinate
cylinders `{r | r (a, 1) = true}` for `a ∈ A⁺`. The continuity condition is
automatic in the discrete setting (`cont_eq_univ_of_discreteTopology`). -/
lemma image_spa_ιSpv_bool [DiscreteTopology A] :
    (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩
        ⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true} := by
  ext r
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_range,
    Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, rfl⟩, fun a ha ↦ ?_⟩
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)]
    exact ⟨hv.2 a ha, v.not_vle_one_zero⟩
  · rintro ⟨⟨v, rfl⟩, hr⟩
    refine ⟨v, ⟨fun _ ↦ isOpen_discrete _, fun a ha ↦ ?_⟩, rfl⟩
    have h := hr a ha
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at h
    exact h.1

/-- **Closedness of `ιSpvBool '' Spa A A⁺` (discrete case).**

In the discrete Bool product `A × A → Bool`, the image of `Spa A A⁺` under
`ιSpvBool` is closed: it is the intersection of the closed range of
`ιSpvBool` (from `ValuationSpectrumCompact`) with the coordinate conditions
`{r | r(a, 1) = true}`, each clopen in the discrete product. -/
lemma isClosed_image_spa_ιSpv_bool [DiscreteTopology A] :
    IsClosed ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
  rw [image_spa_ιSpv_bool]
  exact isClosed_range_ιSpv_bool.inter
    (isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦ isClosed_coord_true (a, 1))

/-! ### Quasi-compactness of `Spa A A⁺` in `Spv A` -/

/-- **T-NULL-0c (discrete case): `Spa(A, A⁺)` is quasi-compact in `Spv A`.**

We route compactness through the Sierpinski Huber embedding
`ιSpv : Spv A → (A × A → Prop)` (an embedding, see `ιSpv_isEmbedding`) and the
Bool embedding `ιSpvBool` (with closed range). The factorisation
`ιSpv = (boolToProp ∘ ·) ∘ ιSpvBool` lets us transfer compactness of
`ιSpvBool '' Spa` — which is closed in the compact Bool product — into
compactness of `ιSpv '' Spa`, hence of `Spa` itself via the embedding.

**Hypothesis:** `[DiscreteTopology A]`. Under this, `Cont A = univ` and the
obstruction to closedness of `Cont` disappears. The general Huber/Tate version
(Wedhorn 7.30) is future work. -/
theorem isCompact_spa [DiscreteTopology A] :
    IsCompact ((Spa A A⁺) : Set (Spv A)) := by
  refine (ιSpv_isEmbedding.isCompact_iff (s := Spa A A⁺)).mpr ?_
  -- Factor `ιSpv '' Spa` as the continuous image under `boolToProp_pi` of
  -- `ιSpvBool '' Spa`. The latter is closed in the compact Bool product,
  -- hence compact; continuous image of compact is compact.
  have hfactor :
      (ιSpv : Spv A → (A × A → Prop)) '' (Spa A A⁺) =
        (fun r : A × A → Bool ↦ fun p ↦ boolToProp (r p)) ''
          ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
    ext s
    simp only [Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨ιSpvBool v, ⟨v, hv, rfl⟩, (ιSpv_eq_boolToProp_comp_ιSpv_bool v).symm⟩
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, ιSpv_eq_boolToProp_comp_ιSpv_bool v⟩
  rw [hfactor]
  exact isClosed_image_spa_ιSpv_bool.isCompact.image continuous_boolToProp_pi

/-- **T-NULL-0c capstone: `CompactSpace ↥(Spa(A, A⁺))` (discrete case).**

The adic spectrum `Spa(A, A⁺)` of a commutative ring `A` with the discrete
topology and a choice of integral subring `A⁺` is a compact topological space.

This is the discrete specialisation of Wedhorn Theorem 7.30. Together with
`ValuationSpectrum.instCompactSpace` (quasi-compactness of `Spv A`) it unblocks
the Nullstellensatz refinement / Cor 7.32 route to the dominating-unit lemma
(see `docs/plans/2026-04-16-s3-nullstellensatz-plan.md`, T-NULL-0c). -/
instance instCompactSpace_spa [DiscreteTopology A] :
    CompactSpace ↥(Spa A A⁺) :=
  isCompact_iff_compactSpace.mp isCompact_spa

/-! ### Abstract compactness criterion via closed Bool cylinders

The discrete-case proof relies only on two facts: (i) the image
`ιSpvBool '' Spa A A⁺` is closed in the Bool product, and (ii) the continuous
factorisation `ιSpv = boolToProp ∘ ιSpvBool` transfers compactness from Bool
to the Sierpinski target, so `ιSpv_isEmbedding.isCompact_iff` gives compactness
of `Spa A A⁺` itself.

We factor out this route: given **any** closed subset `S` of `(A × A → Bool)`
such that `ιSpvBool '' Spa A A⁺ = (range ιSpvBool) ∩ S`, the same argument
yields `IsCompact (Spa A A⁺)` and `CompactSpace ↥(Spa A A⁺)`. In the discrete
case `S = ⋂_{a ∈ A⁺} {r | r(a,1) = true}`; for Tate rings we will instantiate
`S` with an additional cylinder capturing the continuity condition
`v(π) < 1`. -/

/-- **Abstract compactness criterion.** Given a closed subset `S` of
`(A × A → Bool)` whose intersection with `range ιSpvBool` equals
`ιSpvBool '' Spa A A⁺`, the adic spectrum `Spa A A⁺` is compact in `Spv A`. -/
theorem isCompact_spa_of_isClosed_image
    {S : Set (A × A → Bool)} (hS : IsClosed S)
    (hEq : (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S) :
    IsCompact ((Spa A A⁺) : Set (Spv A)) := by
  refine (ιSpv_isEmbedding.isCompact_iff (s := Spa A A⁺)).mpr ?_
  have hfactor :
      (ιSpv : Spv A → (A × A → Prop)) '' (Spa A A⁺) =
        (fun r : A × A → Bool ↦ fun p ↦ boolToProp (r p)) ''
          ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
    ext s
    simp only [Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨ιSpvBool v, ⟨v, hv, rfl⟩, (ιSpv_eq_boolToProp_comp_ιSpv_bool v).symm⟩
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, ιSpv_eq_boolToProp_comp_ιSpv_bool v⟩
  rw [hfactor, hEq]
  exact (isClosed_range_ιSpv_bool.inter hS).isCompact.image continuous_boolToProp_pi

/-- **Abstract compactness criterion (instance form).** -/
theorem instCompactSpace_spa_of_isClosed_image
    {S : Set (A × A → Bool)} (hS : IsClosed S)
    (hEq : (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S) :
    CompactSpace ↥(Spa A A⁺) :=
  isCompact_iff_compactSpace.mp (isCompact_spa_of_isClosed_image hS hEq)

/-! ### Quasi-compactness of rational opens via the Bool cylinder extension

`rationalOpen T s ⊆ Spa A A⁺` is a finite intersection of `basicOpen t s`
for `t ∈ insert s T`. Each `basicOpen` is OPEN but **not closed** in the
`Spv A` topology (see the SpaCompact preamble), so the naive
"closed-in-compact" route fails.

**The correct route** uses the Bool Huber embedding: for each `(t, s)`
the cylinder `{r | r(t, s) = true}` IS clopen in the discrete Bool product
(`isClosed_coord_true`), and `v ∈ basicOpen t s ↔ ιSpvBool v (t, s) = true`.
Hence
  `ιSpvBool '' rationalOpen T s = (ιSpvBool '' Spa A A⁺) ∩ ⋂_{t ∈ insert s T} {r | r(t,s)=true}`
stays closed whenever `ιSpvBool '' Spa A A⁺` is; closed in compact Bool
gives compact, which transfers back via `continuous_boolToProp_pi` +
`ιSpv_isEmbedding.isCompact_iff`. -/

/-- **Bool image of a rational open.** Assuming an abstract closed
description `ιSpvBool '' Spa A A⁺ = range ιSpvBool ∩ S`, the image of
`rationalOpen T s` is obtained by intersecting with the clopen cylinder
`{r | r(s, s) = true}` (encoding `¬ v.vle s 0`) and, for each `t ∈ T`,
the cylinder `{r | r(t, s) = true}` (encoding `v.vle t s`). -/
lemma image_ιSpv_bool_rationalOpen
    {S : Set (A × A → Bool)}
    (hEq : (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S)
    (T : Finset A) (s : A) :
    (ιSpvBool : Spv A → (A × A → Bool)) '' (rationalOpen T s) =
      (Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S) ∩
        ({r : A × A → Bool | r (s, s) = true} ∩
          ⋂ (t : A) (_ : t ∈ T), {r : A × A → Bool | r (t, s) = true}) := by
  rw [← hEq]
  ext r
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, ⟨hv_spa, hvT, hvs⟩, rfl⟩
    refine ⟨⟨v, hv_spa, rfl⟩, ?_, ?_⟩
    · simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)]
      exact ⟨(v.vle_total s s).elim id id, hvs⟩
    · intro t ht
      simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)]
      exact ⟨hvT t ht, hvs⟩
  · rintro ⟨⟨v, hv_spa, rfl⟩, hs_cell, hCyl⟩
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at hs_cell
    refine ⟨v, ⟨hv_spa, ?_, hs_cell.2⟩, rfl⟩
    intro t ht
    have hcell := hCyl t ht
    simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at hcell
    exact hcell.1

/-- **Quasi-compactness of rational opens (abstract form).** From any
closed description `ιSpvBool '' Spa A A⁺ = range ιSpvBool ∩ S`, the
rational open `rationalOpen T s` is quasi-compact in `Spv A`. Specialise
via `image_spa_ιSpv_bool` (discrete case) or
`image_spa_ιSpv_bool_of_tate` (Tate case). -/
theorem isCompact_rationalOpen_of_isClosed_image
    {S : Set (A × A → Bool)} (hS : IsClosed S)
    (hEq : (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S)
    (T : Finset A) (s : A) :
    IsCompact (rationalOpen T s : Set (Spv A)) := by
  have hBoolCompact :
      IsCompact ((ιSpvBool : Spv A → (A × A → Bool)) '' (rationalOpen T s)) := by
    rw [image_ιSpv_bool_rationalOpen hEq T s]
    refine IsClosed.isCompact ?_
    refine (isClosed_range_ιSpv_bool.inter hS).inter ?_
    refine (isClosed_coord_true (s, s)).inter ?_
    exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦ isClosed_coord_true (t, s)
  refine (ιSpv_isEmbedding.isCompact_iff (s := rationalOpen T s)).mpr ?_
  have hfactor :
      (ιSpv : Spv A → (A × A → Prop)) '' (rationalOpen T s) =
        (fun r : A × A → Bool ↦ fun p ↦ boolToProp (r p)) ''
          ((ιSpvBool : Spv A → (A × A → Bool)) '' (rationalOpen T s)) := by
    ext p
    simp only [Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨ιSpvBool v, ⟨v, hv, rfl⟩, (ιSpv_eq_boolToProp_comp_ιSpv_bool v).symm⟩
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, ιSpv_eq_boolToProp_comp_ιSpv_bool v⟩
  rw [hfactor]
  exact hBoolCompact.image continuous_boolToProp_pi

/-- **Subtype form: rational opens pull back to compact sets in `↥(Spa A A⁺)`.**
Since `rationalOpen T s ⊆ Spa A A⁺`, the preimage under `Subtype.val` is a
compact subset of the adic spectrum when the ambient Bool image is closed. -/
theorem isCompact_preimage_rationalOpen_of_isClosed_image
    {S : Set (A × A → Bool)} (hS : IsClosed S)
    (hEq : (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S)
    (T : Finset A) (s : A) :
    IsCompact (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺)) := by
  have hEmb : Topology.IsEmbedding (Subtype.val : ↥(Spa A A⁺) → Spv A) :=
    Topology.IsEmbedding.subtypeVal
  refine (hEmb.isCompact_iff (s := Subtype.val ⁻¹' rationalOpen T s)).mpr ?_
  have himg : Subtype.val '' (Subtype.val ⁻¹' rationalOpen T s
      : Set ↥(Spa A A⁺)) = rationalOpen T s := by
    rw [Subtype.image_preimage_val]
    exact Set.inter_eq_right.mpr rationalOpen_subset_spa
  rw [himg]
  exact isCompact_rationalOpen_of_isClosed_image hS hEq T s

/-- **Quasi-compactness of rational opens (discrete case).** Under
`[DiscreteTopology A]`, each rational open `rationalOpen T s ⊆ Spa A A⁺`
is quasi-compact. Instantiates the abstract criterion with the discrete
image description `image_spa_ιSpv_bool`. -/
theorem isCompact_preimage_rationalOpen_of_discreteTopology
    [DiscreteTopology A] (T : Finset A) (s : A) :
    IsCompact (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺)) :=
  isCompact_preimage_rationalOpen_of_isClosed_image
    (S := ⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true})
    (isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦ isClosed_coord_true (a, 1))
    image_spa_ιSpv_bool T s

end ValuationSpectrum

/-! ### Tate case: compactness via a pseudo-uniformizer

For a Huber ring `A` with a pair of definition `P` such that the ring of
definition `A₀ := P.A₀` is contained in `A⁺`, and a distinguished
**pseudo-uniformizer** `π` — an element of `A₀` whose image in `A` is a unit,
such that `P.I` is the principal ideal generated by `π` — the continuity
condition for a valuation `v` with `v ≤ 1` on `A⁺` reduces to the single
strict inequality `v(π) < 1`. This matches Wedhorn's treatment of Tate rings
(§6.10) and is the source of their "single coordinate" rigidity in
`Spa(A, A⁺)`.

In terms of the Bool Huber embedding, `v(π) < 1` is the conjunction of two
clopen cylinder conditions:

* `r(π, 1) = true` (reading: `v.vle π 1 ∧ ¬ v.vle 1 0`, and `¬ v.vle 1 0`
  always holds);
* `r(1, π) = false` (reading: `¬ (v.vle 1 π ∧ ¬ v.vle π 0)`, which under
  `π ∈ A×` — so `¬ v.vle π 0` — simplifies to `¬ v.vle 1 π`).

Combined with the `A⁺`-cylinders `{r | r(a, 1) = true}` for `a ∈ A⁺`, we
obtain a closed description of `ιSpvBool '' Spa A A⁺` in the compact
Bool product. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [PlusSubring A]

open Pointwise

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Forward direction: continuity + pseudo-uniformizer ⟹ `v(π) < 1`.** If
`v ∈ Spa A A⁺` and `π : A` is topologically nilpotent, then `¬ v.vle 1 π`. -/
lemma not_vle_one_of_mem_spa_of_topologicallyNilpotent
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π) :
    ¬ v.vle 1 π := by
  -- Set up the valuation compatibility so we can compare `v.vle` and `≤`.
  letI : ValuativeRel A := v.toValuativeRel
  -- Continuity of `v` yields that `{a | val(a) < 1}` is open in `A`.
  have hcont : v.IsContinuous := hv.1
  have h_open :
      IsOpen {a : A | (ValuativeRel.valuation A) a <
        (ValuativeRel.valuation A) 1} := by
    rw [map_one]; exact hcont 1
  -- Since `π^n → 0` and `{val < 1}` is an open neighbourhood of `0`,
  -- eventually `val(π^n) < 1`.
  have h0_mem : (0 : A) ∈ {a : A | (ValuativeRel.valuation A) a <
      (ValuativeRel.valuation A) 1} := by
    simp only [Set.mem_setOf_eq, map_zero, map_one]
    exact zero_lt_iff.mpr
      (ValuativeRel.valuation_posSubmonoid_ne_zero
        ⟨1, ValuativeRel.zero_vlt_one⟩)
  obtain ⟨n, hn⟩ :=
    (hπ_tn.eventually (h_open.mem_nhds h0_mem)).exists
  -- `val(π^n) < 1` unpacks to `val(π)^n < 1`, hence `val(π) < 1` by the
  -- order axiom: `x ≥ 1 ⟹ x^n ≥ 1`.
  simp only [map_pow, map_one] at hn
  have hπ_lt : (ValuativeRel.valuation A) π < 1 := by
    by_contra h
    push Not at h
    exact not_lt_of_ge (one_le_pow_of_one_le' h n) hn
  -- Translate to `vle` via `Compatible.vle_iff_le`.
  haveI : (ValuativeRel.valuation A).Compatible := inferInstance
  intro h_vle
  have h_le := (Valuation.Compatible.vle_iff_le
    (v := ValuativeRel.valuation A) 1 π).mp h_vle
  exact absurd h_le (not_le.mpr (by simpa using hπ_lt))

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
omit [PlusSubring A] in
/-- For a unit `π : A`, membership in `basicOpen 1 π` coincides with
`v.vle 1 π`: the `¬ v.vle π 0` part is automatic. -/
lemma basicOpen_one_of_isUnit (v : Spv A) {π : A} (hπ : IsUnit π) :
    v ∈ basicOpen 1 π ↔ v.vle 1 π :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, not_vle_zero_of_isUnit hπ v⟩⟩

omit [IsLinearTopology A A] in
/-- **Reverse direction: `v ≤ 1` on `A⁺` + pseudo-uniformizer cofinality ⟹
continuity.** Under the assumptions that
* a pair of definition `P` has `P.A₀ ⊆ A⁺`,
* `π ∈ P.A₀` has image generating `P.I` principally,
* `v` is bounded by `1` on `A⁺` (so in particular on `A₀`),
* cofinality of powers of `w(π)` in the value group of `v`,

the valuation `v` is continuous on `A`. This applies
`Valuation.isContinuous_of_le_one_and_pow_cofinal` with `g = v(π)` and
`I`-generator `π`. -/
lemma isContinuous_of_vle_of_pseudouniformizer
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    {v : Spv A} (hv_le : ∀ a ∈ (A⁺ : Set A), v.vle a 1)
    (h_cofinal :
      letI : ValuativeRel A := v.toValuativeRel
      ∀ γ : ValuativeRel.ValueGroupWithZero A, 0 < γ →
        ∃ n : ℕ, (ValuativeRel.valuation A) (P.A₀.subtype π) ^ n < γ) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  set w := ValuativeRel.valuation A with hw_def
  -- Translate the `vle`-level bound to the `w`-valuation level.
  have hw_le_one : ∀ a : P.A₀, w (P.A₀.subtype a) ≤ 1 := by
    intro a
    have hmem : (P.A₀.subtype a : A) ∈ (A⁺ : Set A) := hA₀_le a.2
    rw [show (1 : ValuativeRel.ValueGroupWithZero A) = w 1 from (map_one w).symm]
    exact (Valuation.Compatible.vle_iff_le (v := w) _ _).mp (hv_le _ hmem)
  -- Set `g := w(π)`. Generators of `I = (π)` are bounded by `g`.
  set g : ValuativeRel.ValueGroupWithZero A := w (P.A₀.subtype π) with hg_def
  -- Bound on the `I`-generator.
  have h_gen : ∀ (a : P.A₀), a ∈ P.I → w (P.A₀.subtype a) ≤ g := by
    intro a ha
    rw [hI] at ha
    -- `a ∈ Ideal.span {π} ⟹ ∃ c, a = c * π`
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [Subring.coe_subtype, map_mul]
    calc w (P.A₀.subtype c) * w (P.A₀.subtype π)
        ≤ 1 * w (P.A₀.subtype π) :=
          mul_le_mul_left (hw_le_one c) _
      _ = g := by rw [one_mul]
  -- Apply the continuity theorem with `h_cofinal`.
  exact Valuation.isContinuous_of_le_one_and_pow_cofinal P w hw_le_one h_gen h_cofinal

omit [IsLinearTopology A A] in
/-- **Bool-image characterisation of `Spa A A⁺` for Tate rings** with pseudo-
uniformizer, under the MulArchimedean assumption on all valuations.

The image of `Spa A A⁺` under `ιSpvBool` is the intersection of:

* `range ιSpvBool` (the set of Bool valuation characteristics);
* the coordinate cylinders `{r | r(a, 1) = true}` for each `a ∈ A⁺`;
* the single coordinate `{r | r(1, π) = false}`, capturing `v(π) < 1` (the
  cylinder `r(π, 1) = true` is subsumed because `π ∈ A⁺`). -/
lemma image_spa_ιSpv_bool_of_tate
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
        letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A)) :
    (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
      Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩
        (⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true}) ∩
        {r : A × A → Bool | r (1, P.A₀.subtype π) = false} := by
  ext r
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_range,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨⟨v, rfl⟩, fun a ha ↦ ?_⟩, ?_⟩
    · simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)]
      exact ⟨hv.2 a ha, v.not_vle_one_zero⟩
    · -- `r(1, π) = false` from `¬ v.vle 1 π`
      simp only [ιSpv_bool_apply, @decide_eq_false_iff_not _ (Classical.dec _)]
      intro hboth
      exact not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn hboth.1
  · rintro ⟨⟨⟨v, rfl⟩, hA⟩, hπc⟩
    refine ⟨v, ?_, rfl⟩
    refine ⟨?_, fun a ha ↦ ?_⟩
    · -- Continuity from reverse direction.
      letI : ValuativeRel A := v.toValuativeRel
      haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero A) := hArch v
      have hv_le : ∀ a ∈ (A⁺ : Set A), v.vle a 1 := by
        intro a ha
        have := hA a ha
        simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at this
        exact this.1
      have hv_lt : ¬ v.vle 1 (P.A₀.subtype π) := by
        simp only [ιSpv_bool_apply, @decide_eq_false_iff_not _ (Classical.dec _)] at hπc
        intro h
        exact hπc ⟨h, not_vle_zero_of_isUnit hπ_unit v⟩
      -- `v.IsContinuous` is the continuity of `ValuativeRel.valuation A`.
      change (ValuativeRel.valuation A).IsContinuous
      refine isContinuous_of_vle_of_pseudouniformizer P hA₀_le π hI hv_le ?_
      -- Cofinality from MulArchimedean + `w(π) < 1`.
      set w := ValuativeRel.valuation A
      have hw_lt_one : w (P.A₀.subtype π) < 1 := by
        by_contra hge
        push Not at hge
        rw [show (1 : ValuativeRel.ValueGroupWithZero A) = w 1
          from (map_one w).symm] at hge
        exact hv_lt ((Valuation.Compatible.vle_iff_le (v := w) _ _).mpr hge)
      intro γ hγ
      exact exists_pow_lt₀ hw_lt_one (Units.mk0 γ hγ.ne')
    · have := hA a ha
      simp only [ιSpv_bool_apply, @decide_eq_true_iff _ (Classical.dec _)] at this
      exact this.1

omit [IsLinearTopology A A] in
/-- **Closedness of the Tate Bool image.** -/
lemma isClosed_image_spa_ιSpv_bool_of_tate
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
        letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A)) :
    IsClosed ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
  rw [image_spa_ιSpv_bool_of_tate P hA₀_le π hI hπ_tn hπ_unit hArch]
  exact (isClosed_range_ιSpv_bool.inter
      (isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
        isClosed_coord_true (a, 1))).inter
    (isClosed_coord_false (1, P.A₀.subtype π))

omit [IsLinearTopology A A] in
/-- **Compactness of `Spa A A⁺` for Tate rings with a pseudo-uniformizer**
(Wedhorn Theorem 7.30, Tate case). Under the hypotheses:

* a pair of definition `P` with `P.A₀ ⊆ A⁺`,
* `π ∈ P.A₀` is a topologically nilpotent unit in `A` (a pseudo-uniformizer),
* `P.I = (π)` (principal ideal of definition),
* MulArchimedean on the ValueGroup of every `v : Spv A`,

the adic spectrum `Spa(A, A⁺)` is quasi-compact in `Spv A`. -/
theorem isCompact_spa_of_tate_pseudouniformizer
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
        letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A)) :
    IsCompact ((Spa A A⁺) : Set (Spv A)) :=
  isCompact_spa_of_isClosed_image
    (S := (⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true}) ∩
      {r : A × A → Bool | r (1, P.A₀.subtype π) = false})
    ((isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
        isClosed_coord_true (a, 1)).inter
      (isClosed_coord_false (1, P.A₀.subtype π)))
    (by
      rw [image_spa_ιSpv_bool_of_tate P hA₀_le π hI hπ_tn hπ_unit hArch]
      ext r; simp only [Set.mem_inter_iff]; tauto)

omit [IsLinearTopology A A] in
/-- **Capstone: `CompactSpace ↥(Spa(A, A⁺))` for Tate rings with a
pseudo-uniformizer.** See `isCompact_spa_of_tate_pseudouniformizer` for
the hypothesis list. -/
theorem instCompactSpace_spa_of_tate_pseudouniformizer
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
        letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A)) :
    CompactSpace ↥(Spa A A⁺) :=
  isCompact_iff_compactSpace.mp
    (isCompact_spa_of_tate_pseudouniformizer P hA₀_le π hI hπ_tn hπ_unit hArch)

/-! ### Quasi-compactness of rational opens (Tate specialisation)

Concrete C2 supplier for the T-NULL-PER-E decomposition: each rational
open `rationalOpen T s ⊆ Spa A A⁺` is quasi-compact under the Tate
hypotheses. Uses the abstract criterion `isCompact_preimage_rationalOpen_of_isClosed_image`
(`SpaCompact.lean`, above) with the closed Bool image description from
`image_spa_ιSpv_bool_of_tate`. -/

omit [IsLinearTopology A A] in
/-- **Quasi-compactness of rational opens for Tate rings** with a
pseudo-uniformizer. This provides the C2 step of the reviewer's T-NULL-
PER-E decomposition (see `StandardCover.lean` for the overall strategy):
a finite open cover of `rationalOpen T s` admits a finite sub-cover. -/
theorem isCompact_preimage_rationalOpen_of_tate_pseudouniformizer
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
        letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (T : Finset A) (s : A) :
    IsCompact (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺)) :=
  isCompact_preimage_rationalOpen_of_isClosed_image
    (S := (⋂ (a : A) (_ : a ∈ A⁺), {r : A × A → Bool | r (a, 1) = true}) ∩
      {r : A × A → Bool | r (1, P.A₀.subtype π) = false})
    ((isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
        isClosed_coord_true (a, 1)).inter
      (isClosed_coord_false (1, P.A₀.subtype π)))
    (by
      rw [image_spa_ιSpv_bool_of_tate P hA₀_le π hI hπ_tn hπ_unit hArch]
      ext r; simp only [Set.mem_inter_iff]; tauto)
    T s

end ValuationSpectrum
