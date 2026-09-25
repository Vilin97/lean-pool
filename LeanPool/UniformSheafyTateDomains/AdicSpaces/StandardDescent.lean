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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardRefinement

/-!
# A⁺-independence via standard covers (Kedlaya Lemma 1.6.8 / Remark 1.6.9)

The genuine transfer engine for pair-level sheafiness between different rings of
integral elements of one complete Tate ring, factored exactly as in Kedlaya's
Remark 1.6.9: *"both the collection of standard rational coverings, and the
assertions of the sheaf axiom for these coverings, depend only on `A`, not on `A⁺`."*

* `standardSheafCondition_of_isSheafyFor` — **the single-pair derivation** of the
  `A⁺`-free `StandardSheafCondition` (upgrading
  `standardSheafCondition_of_isSheafyComplete`, which needed *all* pairs): the
  standard covers instantiate at the given pair (their subordination and covering
  conditions are `Spa`-uniform), the sheaf-axiom *assertions* about them are
  literally `A⁺`-independent (`presheafValue` and `restrictionMap` never see `A⁺`;
  the instance and containment arguments are proof-irrelevant), and the one
  `A⁺`-relative hypothesis shape — Čech compatibility — transfers through the R3
  bridge (`allDataCompatible_iff_exactIntersectionCompatible`), whose
  exact-intersection form mentions only the intersection data.
* `IsEmbedding.of_comp_isEmbedding` — the elementary factorization principle
  (WO2 task 4): if `g ∘ f` is a topological embedding and `g` is continuous, then
  `f` is a topological embedding. Stated and proved here as a plain topology lemma
  (it is *not* attributed to Kedlaya).
* `HasStandardRefinements` — **the named descent input** (the conclusion of Kedlaya
  Lemma 1.6.8 / Wedhorn Lemma 7.54 / Huber [Hu3] 2.6, in the project's
  intersect-with-the-base vocabulary): every rational covering at the given pair is
  refined by a generated standard cover. The *generation* side of 1.6.8 is proved in
  `StandardRefinement.lean`; the *descent* side for coverings of a general rational
  base is the project's recorded missing API (`WedhornStandardCoverRefinement.lean`;
  Kedlaya's proof re-bases through "every rational subspace of `X` is itself the
  spectrum of a Huber pair", whose ring-level keystone `relativePiece_equiv`
  currently carries strongly noetherian hypotheses). It is therefore taken as a
  named, precisely-documented hypothesis — never silently, never via `iff_of_true`.
* `isSheafyFor_of_standardSheafCondition` — the reduction (Kedlaya 1.6.8 ⟹ the
  sheaf axioms for arbitrary rational covers): given the `A⁺`-free standard
  condition and the descent input at a pair, that pair is sheafy. Separation and
  the topological embedding transfer along the refinement by factorization; gluing
  transfers by the two-step Čech argument with the induced standard covers of the
  pieces (which are again standard data for the *same* spanning family, so the
  middle term supplies their separation).
* `isSheafyFor_congr_of_hasStandardRefinements` — **genuine A⁺-independence**
  (Kedlaya Remark 1.6.9), conditional on the named descent input: for a
  complete Tate ring with the descent input, `IsSheafyFor A Aplus ↔ IsSheafyFor A
  Bplus` for *any* two valid rings of integral elements — no strong noetherianness,
  no inclusion between the plus rings, no identification of the two `Spa`'s; the
  proof is the composite `IsSheafyFor A Aplus → StandardSheafCondition A →
  IsSheafyFor A Bplus` through the transfer engine above.

## References

* [K. Kedlaya, AWS 2017 notes], Lemma 1.6.8, Remarks 1.6.9–1.6.10.
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.54, Remark 8.20.
* [R. Huber, *A generalization of formal schemes and rigid analytic varieties*],
  Lemma 2.6.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology Filter

universe u

namespace ValuationSpectrum

/-! ### The factorization principle (elementary topology; WO2 task 4) -/

/-- **Factorization principle for embeddings**: if `g ∘ f` is a topological
embedding and `g` is continuous, then `f` is a topological embedding. (Elementary;
proved from the filter characterization of induced topologies. Used for
transferring the cover-product embedding along a refinement; not a statement from
the cited sources.) -/
theorem IsEmbedding.of_comp_isEmbedding {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {g : β → γ}
    (hgf : Topology.IsEmbedding (g ∘ f)) (hf : Continuous f) (hg : Continuous g) :
    Topology.IsEmbedding f := by
  refine ⟨Topology.isInducing_iff_nhds.mpr fun x => le_antisymm ?_ ?_, ?_⟩
  · exact (hf.tendsto x).le_comap
  · calc Filter.comap f (𝓝 (f x))
        ≤ Filter.comap f (Filter.comap g (𝓝 (g (f x)))) :=
          Filter.comap_mono ((hg.tendsto (f x)).le_comap)
      _ = Filter.comap (g ∘ f) (𝓝 ((g ∘ f) x)) := Filter.comap_comap
      _ ≤ 𝓝 x := le_of_eq (hgf.isInducing.nhds_eq_comap x).symm
  · intro x y hxy
    exact hgf.injective (show (g ∘ f) x = (g ∘ f) y from congrArg g hxy)

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-! ### The single-pair derivation of the `A⁺`-free standard condition -/

/-- **Kedlaya Remark 1.6.9, provable half, from a single pair**: if the genuine
all-open structure presheaf of `Spa (A, Aplus)` is a sheaf of topological rings for
**one** valid ring of integral elements, then the `A⁺`-free standard sheaf
condition holds — i.e. the sheaf-axiom assertions hold for every standard cover
datum *at every valid ring of integral elements simultaneously*.

This is the mechanism of Remark 1.6.9: a standard datum instantiates as a rational
covering at the given pair (its conditions are `Spa`-uniform); the embedding and
gluing *assertions* about it are statements about `presheafValue` and
`restrictionMap` only, hence independent of the instantiating pair (definitionally:
`HasLocLiftPowerBounded` is a `Prop` class and the subordination witnesses are
proofs); and the compatibility *hypothesis* transfers between pairs through its
exact-intersection form (`allDataCompatible_iff_exactIntersectionCompatible`),
which mentions only the intersection data. Upgrades
`standardSheafCondition_of_isSheafyComplete` (which consumed **all** pairs). -/
theorem standardSheafCondition_of_isSheafyFor (Aplus : RingOfIntegralElements A)
    (h : IsSheafyFor A Aplus) : StandardSheafCondition A := by
  classical
  intro S B hB
  -- ——— assertions at the GIVEN pair (derived before the target instance enters) ———
  have key : Topology.IsEmbedding (letI := Aplus.toPlusSubring;
        haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
        haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
        productRestrictionSub A (StandardCoverData.toCovering S)) ∧
      (letI := Aplus.toPlusSubring
       haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
       haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
       ∀ (f : ∀ D : ↥(StandardCoverData.toCovering S).covers, presheafValue D.1),
        (StandardCoverData.toCovering S).ExactIntersectionCompatible
          (StandardCoverData.toCovering_isRational S) f →
        ∃ x : presheafValue (StandardCoverData.toCovering S).base,
          ∀ D : ↥(StandardCoverData.toCovering S).covers,
            restrictionMap (StandardCoverData.toCovering S).base D.1
              ((StandardCoverData.toCovering S).hsubset D.1 D.2) x = f D) := by
    letI := Aplus.toPlusSubring
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    haveI hSheafy₁ : IsSheafy A := isSheafy_of_isLimitSheaf h
    refine ⟨IsSheafy.embedding _ (StandardCoverData.toCovering_isRational S),
      fun f hf => IsSheafy.gluing _ (StandardCoverData.toCovering_isRational S) f ?_⟩
    exact (RationalCoveringData.allDataCompatible_iff_exactIntersectionCompatible
      (StandardCoverData.toCovering_isRational S) f).mpr hf
  -- ——— the assertions at the TARGET pair ———
  letI : PlusSubring A := ⟨B⟩
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := hB
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  refine ⟨?_, ?_⟩
  · -- embedding: the product restriction of the standard datum is the **same
    -- function** at both pairs (the instance and containment arguments are
    -- proof-irrelevant, and the covering's data fields are shared)
    exact key.1
  · -- gluing: the compatibility hypothesis transfers through its
    -- exact-intersection form, which mentions only the intersection data
    intro f hf
    exact key.2 f ((RationalCoveringData.allDataCompatible_iff_exactIntersectionCompatible
      (StandardCoverData.toCovering_isRational S) f).mp hf)

/-! ### The descent input (Kedlaya Lemma 1.6.8's conclusion), named -/

section Descent

variable [DecidableEq A] [DecidableEq (RationalLocData A)]

/-- The piece of the generated standard cover of `D₀` at generator `f` (the
`StandardRefinement.lean` construction, `StandardCoverData.ofSpanTop`): the exact
intersection `R(D₀) ∩ R(S/f)`. Depends only on the ring data — no `A⁺`. -/
def stdPiece (D₀ : RationalLocData A) (hD₀ : D₀.IsRational) (S : Finset A)
    (hS : Ideal.span (S : Set A) = ⊤) (f : A) : RationalLocData A :=
  D₀.interRational (genPieceDatum D₀.P S f hS) hD₀
    (RationalLocData.isRational_of_span_eq_top hS)

variable (A) in
/-- **The descent input** (the conclusion of Kedlaya Lemma 1.6.8 / Wedhorn Lemma
7.54 / Huber [Hu3] Lemma 2.6, in the intersect-with-the-base vocabulary), at a
chosen ring of integral elements: every rational covering is refined by the
generated standard cover of some finite family spanning the unit ideal — each
generated piece `R(base) ∩ R(S/f)` is contained in some member of the covering.

**Status (recorded blocked dependency, 2026-07-20).** The *generation* side (the
generated cover is standard: `Spa`-uniformly subordinate to the base and covering
at every pair) is proved in `StandardRefinement.lean`. This *descent* side is:
(i) for coverings of the **whole space**, Huber's product trick — its remaining
completeness input is `span S = ⊤` from no-common-zero-on-`Spa` (Wedhorn Cor 7.53
via Prop 7.51), whose proven project form
(`isUnit_iff_forall_not_vle_zero_of_completePair`) consumes
`[IsAdicComplete P.I P.A₀]`, currently discharged only via
`principalPair_isAdicComplete_of_stronglyNoetherianTate`; (ii) for coverings of a
**general rational base**, additionally Kedlaya's re-basing ("every rational
subspace of `X` is itself the spectrum of a Huber pair"), whose ring-level keystone
(`relativePiece_equiv`, Wedhorn Prop 8.16/Lemma 2.13) currently carries
`[IsStronglyNoetherian]`. The exact missing declarations are therefore: a
noetherian-free `IsAdicComplete`-from-`CompleteSpace` bridge, and a noetherian-free
`relativePiece_equiv`. Until they exist, this input is a hypothesis — never
supplied silently. -/
def HasStandardRefinementsAt [PlusSubring A] : Prop :=
  ∀ (C : RationalCoveringData A) (hC : C.IsRational),
    C.covers.Nonempty →
      ∃ (S : Finset A) (hS : Ideal.span (S : Set A) = ⊤),
        ∀ f ∈ S, ∃ E ∈ C.covers,
          rationalOpen (stdPiece C.base hC.base S hS f).T
              (stdPiece C.base hC.base S hS f).s
            ⊆ rationalOpen E.T E.s

end Descent

/-! ### The transfer engine: standard condition + descent ⟹ the sheaf axioms -/

section Engine

variable [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [DecidableEq A] [DecidableEq (RationalLocData A)]

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
/-- The generated standard cover of a base, as `StandardCoverData` (from
`StandardRefinement.lean`), with pieces `stdPiece`. -/
theorem stdPiece_mem_ofSpanTop (D₀ : RationalLocData A) (hD₀ : D₀.IsRational)
    (S : Finset A) (hS : Ideal.span (S : Set A) = ⊤) {f : A} (hf : f ∈ S) :
    stdPiece D₀ hD₀ S hS f ∈ (StandardCoverData.ofSpanTop D₀ hD₀ S hS).covers :=
  (mem_genCoverPieces D₀ hD₀ S hS).mpr ⟨⟨f, hf⟩, rfl⟩

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
theorem mem_ofSpanTop_covers {D₀ : RationalLocData A} {hD₀ : D₀.IsRational}
    {S : Finset A} {hS : Ideal.span (S : Set A) = ⊤} {P : RationalLocData A}
    (hP : P ∈ (StandardCoverData.ofSpanTop D₀ hD₀ S hS).covers) :
    ∃ f ∈ S, stdPiece D₀ hD₀ S hS f = P := by
  obtain ⟨f, hfeq⟩ := (mem_genCoverPieces D₀ hD₀ S hS).mp hP
  exact ⟨f.1, f.2, hfeq⟩

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A] [DecidableEq (RationalLocData A)] in
private theorem productRestrictionSub_continuous'' [HasLocLiftPowerBounded A]
    (C : RationalCoveringData A) : Continuous (productRestrictionSub A C) := by
  refine continuous_pi fun E => ?_
  show Continuous fun x : presheafValue C.base =>
    restrictionMap C.base E.1 (C.hsubset E.1 E.2) x
  exact restrictionMapHom_continuous C.base E.1 (C.hsubset E.1 E.2)

omit [DecidableEq A] in
/-- **Empty-cover branch** (Wedhorn's implicit degenerate case): a rational covering
with no members forces the base rational open to be empty (via `C.hcover`), so the
section ring `presheafValue C.base` is a subsingleton
(`presheafValue_subsingleton_of_rationalOpen_empty`). Then the embedding is
`IsEmbedding.of_subsingleton` and gluing is the (vacuously constrained) `0`-section.
Extracted so the two `IsSheafy` fields do not duplicate it. -/
theorem isSheafy_rationalCovering_of_covers_empty
    (C : RationalCoveringData A) (he : C.covers = ∅) :
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    Topology.IsEmbedding (productRestrictionSub A C) ∧
    ∀ (f : ∀ D : ↥C.covers, presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  have hbase_empty : rationalOpen C.base.T C.base.s = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨D, hD, _⟩ := C.hcover v hv
    exact Finset.eq_empty_iff_forall_notMem.mp he D hD
  haveI : Subsingleton (presheafValue C.base) :=
    presheafValue_subsingleton_of_rationalOpen_empty C.base hbase_empty
  exact ⟨Topology.IsEmbedding.of_subsingleton _,
    fun f _ => ⟨0, fun D => absurd D.2 (Finset.eq_empty_iff_forall_notMem.mp he D.1)⟩⟩

/-- **The reduction** (the Čech-refinement argument assembling Kedlaya Lemma 1.6.8
into the sheaf axioms; Wedhorn's Prop A.3-style transfer, algebraic and topological
halves): given the `A⁺`-free standard condition and the descent input at this pair,
every rational covering at this pair satisfies the embedding and gluing axioms.

* Embedding: the product restriction of the refining standard cover factors through
  the product restriction of the given covering by further (continuous)
  restrictions; conclude by the factorization principle
  (`IsEmbedding.of_comp_isEmbedding`).
* Gluing: restrict the compatible family to the standard pieces through the
  refinement map, glue by the standard condition, and identify the result on each
  member `E` by separation along the *induced* standard cover of `E` (the generated
  cover of `E` for the **same** spanning family — again standard data, so again
  supplied by the standard condition).
* Empty cover: `isSheafy_rationalCovering_of_covers_empty`. -/
theorem isSheafy_of_standardSheafCondition_at
    (hstd : StandardSheafCondition A) (href : HasStandardRefinementsAt A) :
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    IsSheafy A := by
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  classical
  constructor
  · -- ——— embedding ———
    intro C hC
    rcases C.covers.eq_empty_or_nonempty with he | hne
    · exact (isSheafy_rationalCovering_of_covers_empty C he).1
    obtain ⟨S, hS, hsub⟩ := href C hC hne
    set Std := StandardCoverData.ofSpanTop C.base hC.base S hS with hStd
    have hkey := hstd Std (A⁺ : Subring A) inferInstance
    -- the refinement map: each standard piece into a member
    have hr : ∀ P : ↥Std.toCovering.covers, ∃ E ∈ C.covers,
        rationalOpen P.1.T P.1.s ⊆ rationalOpen E.T E.s := by
      rintro ⟨P, hP⟩
      obtain ⟨f, hfS, hfeq⟩ := mem_ofSpanTop_covers hP
      obtain ⟨E, hEC, hEsub⟩ := hsub f hfS
      exact ⟨E, hEC, hfeq ▸ hEsub⟩
    choose r hrC hrsub using hr
    -- factorization: the standard product restriction factors through the given one
    have hfac : productRestrictionSub A Std.toCovering =
        (fun y : ∀ E : ↥C.covers, presheafValue E.1 =>
          fun P : ↥Std.toCovering.covers =>
            restrictionMap (r P) P.1 (hrsub P) (y ⟨r P, hrC P⟩)) ∘
        (productRestrictionSub A C) := by
      funext x P
      exact (congr_fun (restrictionMap_comp C.base (r P) P.1
        (C.hsubset (r P) (hrC P)) (hrsub P)) x).symm
    have hΦcont : Continuous (fun y : ∀ E : ↥C.covers, presheafValue E.1 =>
        fun P : ↥Std.toCovering.covers =>
          restrictionMap (r P) P.1 (hrsub P) (y ⟨r P, hrC P⟩)) := by
      refine continuous_pi fun P => ?_
      exact (restrictionMapHom_continuous (r P) P.1 (hrsub P)).comp
        (continuous_apply (⟨r P, hrC P⟩ : ↥C.covers))
    refine IsEmbedding.of_comp_isEmbedding (g := fun y P =>
      restrictionMap (r P) P.1 (hrsub P) (y ⟨r P, hrC P⟩)) ?_
      (productRestrictionSub_continuous'' C) hΦcont
    rw [← hfac]
    exact hkey.1
  · -- ——— gluing ———
    intro C hC f hcompat
    rcases C.covers.eq_empty_or_nonempty with he | hne
    · exact (isSheafy_rationalCovering_of_covers_empty C he).2 f hcompat
    obtain ⟨S, hS, hsub⟩ := href C hC hne
    set Std := StandardCoverData.ofSpanTop C.base hC.base S hS with hStd
    have hkey := hstd Std (A⁺ : Subring A) inferInstance
    have hr : ∀ P : ↥Std.toCovering.covers, ∃ E ∈ C.covers,
        rationalOpen P.1.T P.1.s ⊆ rationalOpen E.T E.s := by
      rintro ⟨P, hP⟩
      obtain ⟨fₚ, hfS, hfeq⟩ := mem_ofSpanTop_covers hP
      obtain ⟨E, hEC, hEsub⟩ := hsub fₚ hfS
      exact ⟨E, hEC, hfeq ▸ hEsub⟩
    choose r hrC hrsub using hr
    -- the restricted family on the standard pieces
    set g : ∀ P : ↥Std.toCovering.covers, presheafValue P.1 := fun P =>
      restrictionMap (r P) P.1 (hrsub P) (f ⟨r P, hrC P⟩) with hgdef
    have hgcompat : Std.toCovering.AllDataCompatible g := by
      intro P₁ P₂ D₃ h₃₁ h₃₂
      calc restrictionMap P₁.1 D₃ h₃₁ (g P₁)
          = restrictionMap (r P₁) D₃ (h₃₁.trans (hrsub P₁)) (f ⟨r P₁, hrC P₁⟩) :=
            congr_fun (restrictionMap_comp (r P₁) P₁.1 D₃ (hrsub P₁) h₃₁)
              (f ⟨r P₁, hrC P₁⟩)
        _ = restrictionMap (r P₂) D₃ (h₃₂.trans (hrsub P₂)) (f ⟨r P₂, hrC P₂⟩) :=
            hcompat ⟨r P₁, hrC P₁⟩ ⟨r P₂, hrC P₂⟩ D₃ (h₃₁.trans (hrsub P₁))
              (h₃₂.trans (hrsub P₂))
        _ = restrictionMap P₂.1 D₃ h₃₂ (g P₂) :=
            (congr_fun (restrictionMap_comp (r P₂) P₂.1 D₃ (hrsub P₂) h₃₂)
              (f ⟨r P₂, hrC P₂⟩)).symm
    obtain ⟨x, hx⟩ := hkey.2 g hgcompat
    refine ⟨x, ?_⟩
    rintro ⟨E, hEC⟩
    -- identify on `E` by separation along the induced standard cover of `E`
    set StdE := StandardCoverData.ofSpanTop E (hC.piece hEC) S hS with hStdE
    have hkeyE := hstd StdE (A⁺ : Subring A) inferInstance
    refine hkeyE.1.injective ?_
    funext Q
    obtain ⟨fq, hfqS, hfqeq⟩ := mem_ofSpanTop_covers Q.2
    -- the `E`-piece sits inside the corresponding base-piece (at this pair)
    have hQP : rationalOpen Q.1.T Q.1.s ⊆
        rationalOpen (stdPiece C.base hC.base S hS fq).T
          (stdPiece C.base hC.base S hS fq).s := by
      rw [← hfqeq]
      show rationalOpen (stdPiece E (hC.piece hEC) S hS fq).T
          (stdPiece E (hC.piece hEC) S hS fq).s ⊆ _
      rw [stdPiece, stdPiece, RationalLocData.interRational_rationalOpen,
        RationalLocData.interRational_rationalOpen]
      have hgen : rationalOpen (genPieceDatum E.P S fq hS).T
          (genPieceDatum E.P S fq hS).s =
          rationalOpen (genPieceDatum C.base.P S fq hS).T
            (genPieceDatum C.base.P S fq hS).s := by
        rw [genPieceDatum_T, genPieceDatum_T, genPieceDatum_s, genPieceDatum_s]
      rw [hgen]
      exact Set.inter_subset_inter_left _ (C.hsubset E hEC)
    have hQE : rationalOpen Q.1.T Q.1.s ⊆ rationalOpen E.T E.s :=
      StdE.toCovering.hsubset Q.1 Q.2
    -- membership of the base-piece in the standard covering
    have hPmem := stdPiece_mem_ofSpanTop C.base hC.base S hS hfqS
    set P : ↥Std.toCovering.covers := ⟨stdPiece C.base hC.base S hS fq, hPmem⟩
      with hPdef
    -- left side: restrict `x` through the base piece
    have hL : restrictionMap E Q.1 hQE
        (restrictionMap C.base E (C.hsubset E hEC) x) =
        restrictionMap P.1 Q.1 hQP (g P) := by
      calc restrictionMap E Q.1 hQE (restrictionMap C.base E (C.hsubset E hEC) x)
          = restrictionMap C.base Q.1 (hQE.trans (C.hsubset E hEC)) x :=
            congr_fun (restrictionMap_comp C.base E Q.1 (C.hsubset E hEC) hQE) x
        _ = restrictionMap P.1 Q.1 hQP
            (restrictionMap C.base P.1 (Std.toCovering.hsubset P.1 P.2) x) :=
            (congr_fun (restrictionMap_comp C.base P.1 Q.1
              (Std.toCovering.hsubset P.1 P.2) hQP) x).symm
        _ = restrictionMap P.1 Q.1 hQP (g P) :=
            congrArg (restrictionMap P.1 Q.1 hQP) (hx P)
    -- right side: the family agrees with the `E`-value on `Q`
    have hR : restrictionMap P.1 Q.1 hQP (g P) =
        restrictionMap E Q.1 hQE (f ⟨E, hEC⟩) := by
      calc restrictionMap P.1 Q.1 hQP (g P)
          = restrictionMap (r P) Q.1 (hQP.trans (hrsub P)) (f ⟨r P, hrC P⟩) :=
            congr_fun (restrictionMap_comp (r P) P.1 Q.1 (hrsub P) hQP)
              (f ⟨r P, hrC P⟩)
        _ = restrictionMap E Q.1 hQE (f ⟨E, hEC⟩) :=
            hcompat ⟨r P, hrC P⟩ ⟨E, hEC⟩ Q.1 (hQP.trans (hrsub P)) hQE
    show restrictionMap E Q.1 _ (restrictionMap C.base E (C.hsubset E hEC) x) =
      restrictionMap E Q.1 _ (f ⟨E, hEC⟩)
    exact hL.trans hR

/-- **Empty-cover regression** (PHASE 1): the empty-cover branch is discharged
unconditionally on the covering (only the ambient complete-Tate structure), with
no descent input — the section ring is a subsingleton. -/
example (C : RationalCoveringData A) (he : C.covers = ∅) :
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    Topology.IsEmbedding (productRestrictionSub A C) :=
  (isSheafy_rationalCovering_of_covers_empty C he).1

end Engine

/-! ### Genuine `A⁺`-independence (conditional on the named descent input) -/

variable (A) in
/-- The descent input at a bundled pair, with the `Decidable` choices quantified
(they are propositionally unique; quantifying keeps consumers instance-free). -/
def RingOfIntegralElements.HasStandardRefinements
    (Bplus : RingOfIntegralElements A) : Prop :=
  ∀ (_ : DecidableEq A) (_ : DecidableEq (RationalLocData A)),
    letI := Bplus.toPlusSubring
    HasStandardRefinementsAt A

/-- **The reduction, bundled-pair form** (Kedlaya Lemma 1.6.8 ⟹ the sheaf
property): the `A⁺`-free standard sheaf condition, together with the descent input
at a valid pair, makes that pair sheafy — the genuine all-open structure presheaf
of `Spa (A, Bplus)` is a sheaf of topological rings. -/
theorem isSheafyFor_of_standardSheafCondition (hstd : StandardSheafCondition A)
    (Bplus : RingOfIntegralElements A)
    (href : Bplus.HasStandardRefinements A) :
    IsSheafyFor A Bplus := by
  classical
  letI := Bplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Bplus.2
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  letI iA : DecidableEq A := Classical.decEq A
  letI iR : DecidableEq (RationalLocData A) := Classical.decEq _
  haveI : IsSheafy A := isSheafy_of_standardSheafCondition_at hstd (href iA iR)
  show IsLimitSheaf A
  exact isLimitSheaf_of_isSheafy

/-- **Genuine `A⁺`-independence of pair-level sheafiness** (Kedlaya Remark 1.6.9)
for a complete Tate ring, **conditional on exactly the descent input** (the
conclusion of Kedlaya Lemma 1.6.8, `HasStandardRefinements` — see its docstring for
the precise blocked dependencies): any two valid rings of integral elements — with
no strong noetherianness, no inclusion or definitional relation between them, and
no identification of the two adic spectra — give equivalent pair-level sheafiness.
The unsuffixed name `isSheafyFor_congr` is reserved for the eventual
*unconditional* theorem (descent input discharged). The proof is the genuine transfer
`IsSheafyFor A Aplus → StandardSheafCondition A → IsSheafyFor A Bplus`:
the `A⁺`-free standard condition is the common middle term, *not* an appeal to a
condition implying both sides. -/
theorem isSheafyFor_congr_of_hasStandardRefinements
    (Aplus Bplus : RingOfIntegralElements A)
    (hA : Aplus.HasStandardRefinements A) (hB : Bplus.HasStandardRefinements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  ⟨fun h => isSheafyFor_of_standardSheafCondition
      (standardSheafCondition_of_isSheafyFor Aplus h) Bplus hB,
   fun h => isSheafyFor_of_standardSheafCondition
      (standardSheafCondition_of_isSheafyFor Bplus h) Aplus hA⟩

/-- **The standard-cover criterion** (WO2 task 3, conditional form): for a complete
Tate ring with the descent input at a pair, the all-rational-cover sheaf condition
at that pair is *equivalent* to the `A⁺`-free standard-cover condition. -/
theorem isSheafyFor_iff_standardSheafCondition_of_hasStandardRefinements
    (Aplus : RingOfIntegralElements A)
    (hA : Aplus.HasStandardRefinements A) :
    IsSheafyFor A Aplus ↔ StandardSheafCondition A :=
  ⟨standardSheafCondition_of_isSheafyFor Aplus,
   fun h => isSheafyFor_of_standardSheafCondition h Aplus hA⟩

/-- **The universal specialization** (WO2 task 6): with the descent input at every
valid pair, sheafiness at one pair is equivalent to sheafiness at all pairs
(`IsSheafyComplete`, the ring-level Definition 8.26 for complete `A`). -/
theorem isSheafyFor_iff_isSheafyComplete_of_hasStandardRefinements
    (Aplus : RingOfIntegralElements A)
    (hall : ∀ Bplus : RingOfIntegralElements A, Bplus.HasStandardRefinements A) :
    IsSheafyFor A Aplus ↔ IsSheafyComplete A :=
  ⟨fun h Bplus => isSheafyFor_of_standardSheafCondition
      (standardSheafCondition_of_isSheafyFor Aplus h) Bplus (hall Bplus),
   fun h => h Aplus⟩

/-- Regression (WO2 task 7 shape): the independence applies to two valid choices
assumed *distinct* — nothing in the transfer identifies them. -/
example (Aplus Bplus : RingOfIntegralElements A) (_ : Aplus ≠ Bplus)
    (hA : Aplus.HasStandardRefinements A) (hB : Bplus.HasStandardRefinements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  isSheafyFor_congr_of_hasStandardRefinements Aplus Bplus hA hB

end ValuationSpectrum
