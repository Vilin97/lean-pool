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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardDescent
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCechAcyclicity

/-!
# The relative standard refinement (Huber form-(a) product trick) and unconditional A⁺-independence

The descent input `HasStandardRefinementsAt` is discharged **unconditionally** for a
complete Tate ring, via Huber's form-(a) product refinement (Huber Lemma 2.6 /
Wedhorn Lemma 7.54 / Kedlaya Lemma 1.6.8), relativized to a proper rational base by
intersecting with the base and padding the spanning family with a dominating unit.

* `exists_spanTop_standard_refinement_of_rationalCovering_nonempty` — for a nonempty
  rational covering `C` of a rational base, a finite `S ⊆ A` spanning the unit ideal
  such that each generated piece `base ∩ R(S/f)` (= `stdPiece`) is contained in some
  covering member.
* `RingOfIntegralElements.hasStandardRefinements` — the bundled descent input, for
  **every** valid ring of integral elements. No noetherian bypass.

With this, the previously-conditional `A⁺`-independence endpoints become
unconditional:

* `isSheafyFor_congr` — pair-level sheafiness is independent of the valid `A⁺`.
* `isSheafyFor_iff_standardSheafCondition`, `isSheafyFor_iff_isSheafyComplete`.

## The relativization (why the base may be proper)

Over a proper rational base `U = R(base)`, the normalized family `LP` covers only
`U`, so `distinguishedProducts LP` need not span the unit ideal (points outside `U`
may vanish on all of it). This is the project's direct relativization of Huber's
whole-space argument to a proper base: pad with a unit `σ` strictly dominated on `U`
by some `distinguishedProducts` element (the project lemma
`exists_dominating_unit_noHArch_finset_on` on the compact `U`, i.e. Cor 7.32
localized to a compact subset). Then `S := insert σ (distinguishedProducts LP)` spans
(σ is a ring unit), the relative `σ`-piece `U ∩ R(S/σ)` is empty (domination), and for
the other generators the product identity holds *after intersecting with `U`*
(the project lemma `rationalOpen_distinguished_eq_on`).

## Source attribution

Kedlaya Lemma 1.6.8 / Remark 1.6.9 (standard-cover independence); the
topological-embedding transfer in the `A⁺`-free standard condition
(`standardSheafCondition_of_isSheafyFor` + the engine) is the project's own
`IsEmbedding.of_comp_isEmbedding` argument — not asserted to be stated by Kedlaya.

**Edition pin.** All Wedhorn section-numbering citations in this project
(`Definition 7.14/7.23/7.29`, `Proposition 7.51/7.52`, `Lemma 7.54`,
`Definition 8.26`, `Theorem 8.28`, `Remark 8.20`, …) refer to
**T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1** (the file
`Wedhorn-Adic_Spaces-1910.05934v1.pdf` / `references/wedhorn.txt`). Other public
revisions shift the §8 numbering by one; use v1 to resolve any citation here.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace ValuationSpectrum

universe u

section PairLocal

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)]

omit [IsTateRing A] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
/-- `rationalOpen` is antitone in its numerator family. -/
theorem rationalOpen_subset_of_numerator_subset {S₀ S : Finset A} (hSS : S₀ ⊆ S)
    (f : A) : rationalOpen S f ⊆ rationalOpen S₀ f :=
  fun _ ⟨hspa, hT, h0⟩ => ⟨hspa, fun t ht => hT t (hSS ht), h0⟩

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
/-- The rational open of the generated standard piece is the base rational open
intersected with the form-(a) piece `R(S/f)`. -/
theorem rationalOpen_stdPiece_eq [DecidableEq A] (C : RationalCoveringData A)
    (hC : C.IsRational) (S : Finset A) (hS : Ideal.span (S : Set A) = ⊤) (f : A) :
    rationalOpen (stdPiece C.base hC.base S hS f).T
        (stdPiece C.base hC.base S hS f).s =
      rationalOpen C.base.T C.base.s ∩ rationalOpen S f :=
  RationalLocData.interRational_rationalOpen C.base (genPieceDatum C.base.P S f hS)
    hC.base (RationalLocData.isRational_of_span_eq_top hS)

/-- **The relative standard refinement (Huber form-(a) product trick, PHASE 2D).**
For a nonempty rational covering `C` of its rational base, there is a finite family
`S ⊆ A` spanning the unit ideal such that every generated standard piece
`base ∩ R(S/f)` is contained in some covering member. Complete-Tate scope, **no
noetherian / strongly-noetherian hypothesis**. -/
theorem exists_spanTop_standard_refinement_of_rationalCovering_nonempty
    [DecidableEq A] (C : RationalCoveringData A) (hC : C.IsRational)
    (hne : C.covers.Nonempty) :
    ∃ (S : Finset A) (hS : Ideal.span (S : Set A) = ⊤),
      ∀ f ∈ S, ∃ E ∈ C.covers,
        rationalOpen (stdPiece C.base hC.base S hS f).T
            (stdPiece C.base hC.base S hS f).s
          ⊆ rationalOpen E.T E.s := by
  set U : Set (Spv A) := rationalOpen C.base.T C.base.s with hU
  -- Step 1: normalized refinement of `C.covers` over `Y := U`
  obtain ⟨LP, hts, h1, hcovLP, _hrel, hrefLP⟩ :=
    exists_finite_normalized_rational_refinement_on (A := A) U rationalOpen_subset_spa
      C.covers hC.2 C.hcover
  set S₀ : Finset A := distinguishedProducts LP with hS₀
  -- no common zero of `S₀` on `U` (feeds the dominating unit + shows σ-piece empty)
  have hncz : ∀ y : ↥(Spa A A⁺), (y.1 : Spv A) ∈ U →
      ∃ f ∈ S₀, ¬ (y.1 : Spv A).vle f 0 := by
    intro y hy
    obtain ⟨s', hs', _, _, hvs0⟩ :=
      distinguishedProducts_cover LP hts h1 y.2 (hcovLP y.1 hy)
    exact ⟨s', hs', hvs0⟩
  -- Step 5: dominating unit σ over the compact preimage of `U`
  have hUcpt : IsCompact (Subtype.val ⁻¹' U : Set ↥(Spa A A⁺)) :=
    isCompact_preimage_rationalOpen_noHArch
      (IsRingOfIntegralElements.isOpen (B := (A⁺ : Subring A))) C.base hC.base
  obtain ⟨σ, hσ⟩ :=
    exists_dominating_unit_noHArch_finset_on (A := A) hUcpt S₀
      (fun y hy => hncz y hy)
  -- Step 6: `S := insert σ S₀`
  refine ⟨insert (σ : A) S₀, ?_, ?_⟩
  · -- Step 7: `S` spans the unit ideal (σ is a unit and belongs to `S`)
    exact Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Finset.mem_insert_self _ _)) σ.isUnit
  · intro f hf
    -- the product identity, localized to `U`
    have hpieq : U ∩ rationalOpen S₀ f = U ∩
        rationalOpen (transversalProducts (LP.map Prod.fst)) f :=
      (rationalOpen_distinguished_eq_on (A := A) U LP hts h1 hcovLP).symm
    rw [rationalOpen_stdPiece_eq C hC (insert (σ : A) S₀) _ f]
    rcases Finset.mem_insert.mp hf with hfσ | hf₀
    · -- σ-piece is empty on `U`: `E := any member`
      subst hfσ
      obtain ⟨E, hE⟩ := hne
      refine ⟨E, hE, ?_⟩
      rintro v ⟨hvU, hvspa, hvT, hv0⟩
      -- `hσ` gives `t ∈ S₀` with `v(t) > v(σ)`, contradicting `v(t) ≤ v(σ)`
      obtain ⟨t, htS₀, _, ht_not⟩ := hσ ⟨v, hvspa⟩ hvU
      exact absurd (hvT t (Finset.mem_insert_of_mem htS₀)) ht_not
    · -- `f ∈ S₀`: chain through the product identity and the refinement data
      obtain ⟨p, hp, hpsub⟩ := distinguishedProducts_refines LP f hf₀
      obtain ⟨E, hE, hEsub⟩ := hrefLP p hp
      refine ⟨E, hE, ?_⟩
      -- `U ∩ R(S/f) ⊆ U ∩ R(S₀/f) = U ∩ R(P/f) ⊆ R(P/f) ⊆ R(p) ⊆ R(E)`
      calc rationalOpen C.base.T C.base.s ∩ rationalOpen (insert (σ : A) S₀) f
          ⊆ U ∩ rationalOpen S₀ f :=
            Set.inter_subset_inter_right _
              (rationalOpen_subset_of_numerator_subset (Finset.subset_insert _ _) f)
        _ = U ∩ rationalOpen (transversalProducts (LP.map Prod.fst)) f := hpieq
        _ ⊆ rationalOpen (transversalProducts (LP.map Prod.fst)) f :=
            Set.inter_subset_right
        _ ⊆ rationalOpen p.1 p.2 := hpsub
        _ ⊆ rationalOpen E.T E.s := hEsub

end PairLocal

/-! ### Public wrappers (no ambient plus ring; the pair is installed locally) -/

section Public

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **The bundled descent input, unconditionally** (PHASE 2E): every valid ring of
integral elements of a complete Tate ring has standard refinements. -/
theorem RingOfIntegralElements.hasStandardRefinements
    (Bplus : RingOfIntegralElements A) : Bplus.HasStandardRefinements A := by
  intro _ _
  letI := Bplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Bplus.2
  intro C hC hne
  exact exists_spanTop_standard_refinement_of_rationalCovering_nonempty C hC hne

/-! ### Unconditional `A⁺`-independence (the reserved unsuffixed names) -/

/-- **Genuine `A⁺`-independence of pair-level sheafiness** (Kedlaya Remark 1.6.9),
**unconditional** in complete Tate scope: any two valid rings of integral elements
give equivalent pair-level sheafiness. No inclusion/equality/common pair, no
`CompatiblePlusSubring`, no noetherianity. -/
theorem isSheafyFor_congr (Aplus Bplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  isSheafyFor_congr_of_hasStandardRefinements Aplus Bplus
    (RingOfIntegralElements.hasStandardRefinements Aplus)
    (RingOfIntegralElements.hasStandardRefinements Bplus)

/-- **The standard-cover criterion, unconditional**: pair-level sheafiness is
equivalent to the `A⁺`-free standard-cover condition. -/
theorem isSheafyFor_iff_standardSheafCondition (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ StandardSheafCondition A :=
  isSheafyFor_iff_standardSheafCondition_of_hasStandardRefinements Aplus
    (RingOfIntegralElements.hasStandardRefinements Aplus)

/-- **The universal specialization, unconditional**: sheafiness at one valid pair is
equivalent to sheafiness at all pairs (`IsSheafyComplete`, the ring-level
Definition 8.26 for complete `A`). -/
theorem isSheafyFor_iff_isSheafyComplete (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ IsSheafyComplete A :=
  isSheafyFor_iff_isSheafyComplete_of_hasStandardRefinements Aplus
    (fun Bplus => RingOfIntegralElements.hasStandardRefinements Bplus)

end Public

end ValuationSpectrum
