/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCompactExtraction
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStrengthenedC1

/-!
# Wedhorn Strengthened Compact Extraction (C1 + non-zero clause → finite `mk_S_D`)

Strengthened analogue of `WedhornCompactExtraction.mk_S_D_of_C1_and_compactness`:
the C1 input carries a third clause `¬ v.vle f 0` (i.e., `v(f) ≠ 0`),
and the extracted finite `S : Finset A` propagates it to the
strengthened coverage clause

```
∀ v ∈ rationalOpen D.T D.s, ∃ f ∈ S,
  v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0
```

consumed by `WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(commit `63c8ecd`) via its `h_cover_D_nonzero` hypothesis.

## Proof pattern

Mirrors `mk_S_D_of_C1_and_compactness` (Secondary, in
`WedhornCompactExtraction.lean`) but covers the compact set `K` by

```
V w := (Subtype.val ⁻¹' rationalOpen (insert (g w) C.base.T) C.base.s) ∩
       (Subtype.val ⁻¹' rationalOpen ∅ (g w))
```

instead of the plain plus-piece preimage. The second factor uses
`rationalOpen ∅ a = {v ∈ Spa A A⁺ | ¬ v.vle a 0}` and is open by
`rationalOpen_isOpen`. At each witness point `w`, all three input
clauses hold, so `K ⊆ ⋃ w, V w`. The finite-subcover output preserves
the non-zero clause for every `v` in the chosen plus-piece.

## What this file provides

* `mk_S_D_of_C1Strong_and_compactness` — strengthened compact-extraction
  wrapper. Sorry-free, axiom-clean.

## Notes

* No root import: leaf-level, not in `Adic spaces.lean`.
* No edits to `WedhornCompactExtraction.lean` (Secondary) or
  `WedhornStandardCoverRefinement.lean` (Tertiary).
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* Imports `WedhornCompactExtraction` (transitively `Presheaf`/`SpaCompact`
  for the Tate-pseudouniformizer compactness machinery) and
  `WedhornStrengthenedC1` (for the strengthened C1 supplier predicate
  documentation; the compact-extraction theorem here takes the
  strengthened pointwise input directly without the predicate). -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

omit [HasLocLiftPowerBounded A] in
/-- **Strengthened compactness extraction wrapper for the C1 → per-D
refinement step**.

For a fixed cover piece `D` and a strengthened pointwise C1 single-`f`
refinement witness on every `v ∈ rationalOpen D.T D.s` — including the
non-zero clause `¬ v.vle f 0` — quasi-compactness of the rational open
(`isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`) extracts
a finite `S : Finset A` providing the per-D containment AND the
strengthened coverage data consumed by
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`.

The proof refines the open cover used by
`WedhornCompactExtraction.mk_S_D_of_C1_and_compactness`: each piece
`V w` is the intersection of the plus-piece preimage with the open
`Subtype.val ⁻¹' rationalOpen ∅ (g w)` (which encodes
`¬ v.vle (g w) 0`). Each witness point lies in `V w` because all three
input clauses hold there; the finite-subcover output thus preserves the
non-zero clause for every `v` in the chosen plus-piece. -/
theorem mk_S_D_of_C1Strong_and_compactness
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (D : RationalLocData A)
    (hC1_strong : ∀ v ∈ rationalOpen D.T D.s, ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ v.vle f 0) :
    ∃ S : Finset A,
      (∀ f ∈ S,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ S,
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0) := by
  classical
  -- The compact set in `↥(Spa A A⁺)`.
  let K : Set ↥(Spa A A⁺) := Subtype.val ⁻¹' rationalOpen D.T D.s
  have hK_compact : IsCompact K :=
    isCompact_preimage_rationalOpen_of_tate_pseudouniformizer
      P hA₀_le π hI hπ_tn hπ_unit hArch D.T D.s
  -- Lift the strengthened pointwise C1 hypothesis to a Subtype-indexed witness.
  have hC1_K : ∀ w : K, ∃ f : A,
      (w.1.1 : Spv A) ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
      ¬ (w.1.1 : Spv A).vle f 0 :=
    fun w => hC1_strong w.1.1 w.2
  -- Choose a witness function g : K → A.
  let g : K → A := fun w => Classical.choose (hC1_K w)
  have hg_self : ∀ w : K, (w.1.1 : Spv A) ∈
      rationalOpen (insert (g w) C.base.T) C.base.s :=
    fun w => (Classical.choose_spec (hC1_K w)).1
  have hg_sub : ∀ w : K,
      rationalOpen (insert (g w) C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
    fun w => (Classical.choose_spec (hC1_K w)).2.1
  have hg_nonzero : ∀ w : K, ¬ (w.1.1 : Spv A).vle (g w) 0 :=
    fun w => (Classical.choose_spec (hC1_K w)).2.2
  -- Refined K-indexed open cover: plus-piece ∩ {v : v(g w) ≠ 0}.
  let V : K → Set ↥(Spa A A⁺) := fun w =>
    (Subtype.val ⁻¹' rationalOpen (insert (g w) C.base.T) C.base.s) ∩
    (Subtype.val ⁻¹' rationalOpen (∅ : Finset A) (g w))
  have hV_open : ∀ w, IsOpen (V w) :=
    fun _ => (rationalOpen_isOpen _ _).inter (rationalOpen_isOpen _ _)
  have hK_cover : K ⊆ ⋃ w, V w := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hg_self ⟨x, hx⟩, x.2, ?_, hg_nonzero ⟨x, hx⟩⟩
    -- x.1 ∈ rationalOpen ∅ (g ⟨x, hx⟩)
    exact fun t ht => absurd ht (Finset.notMem_empty t)
  -- Finite subcover via mathlib's `IsCompact.elim_finite_subcover`.
  obtain ⟨T₀, hT₀_cover⟩ := hK_compact.elim_finite_subcover V hV_open hK_cover
  refine ⟨T₀.image g, ?_, ?_⟩
  · -- Containment: each `f ∈ T₀.image g` comes from some `w ∈ T₀` via `hg_sub`.
    intro f hf
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hf
    exact hg_sub w
  · -- Strengthened coverage: lift `v` to a point of `K`, find `w₀ ∈ T₀` with
    -- `x ∈ V w₀`, extract `g w₀ ∈ S` together with the plus-piece membership
    -- (first component) and the non-zero clause (third component of the
    -- `rationalOpen ∅ (g w₀)` membership).
    intro v hv
    obtain ⟨w₀, hw₀_T₀, hx_in⟩ := Set.mem_iUnion₂.mp
      (hT₀_cover (a := ⟨v, rationalOpen_subset_spa hv⟩) hv)
    refine ⟨g w₀, Finset.mem_image.mpr ⟨w₀, hw₀_T₀, rfl⟩, hx_in.1, ?_⟩
    -- `hx_in.2 : x ∈ Subtype.val ⁻¹' rationalOpen ∅ (g w₀)`.
    -- Decomposing: x.1 ∈ Spa ∧ (∀ t ∈ ∅, ...) ∧ ¬ x.1.vle (g w₀) 0.
    -- The third component gives `¬ v.vle (g w₀) 0` since `x.1 = v`.
    exact hx_in.2.2.2

end ValuationSpectrum
