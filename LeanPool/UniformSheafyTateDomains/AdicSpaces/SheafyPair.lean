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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalBasis
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf

/-!
# Pair-level sheafiness: the rational criterion is the all-open sheaf condition

**Phase C of the sheafiness program** (Wedhorn Remarks 8.9/8.20, Theorem 8.28(b)
vocabulary). For a complete Tate ring `A` with a valid `A⁺`, this file proves that the
chosen-pair finite-rational-cover criterion `IsSheafy A` (the 8.28(b) campaign's class)
makes the **genuine all-open projective-limit structure presheaf**
(`StructurePresheafLimit`) a **sheaf of topological rings**:

* `limitRestrict_injective` — separation for arbitrary open covers (C3-separation);
* `exists_limitSections_glue` — gluing for arbitrary open covers (C3-gluing);
* `isInducing_limitRestrictProd` / `isEmbedding_limitRestrictProd` — the restriction
  map `𝒪_X(V) → ∏ᵢ 𝒪_X(Uᵢ)` is a topological embedding for **every** open cover
  (C4; Wedhorn Remark 8.20's second condition), via the initial/projective-limit
  topology and finite rational refinements;
* `IsLimitSheaf` + `isLimitSheaf_of_isSheafy` — the bundled statement;
* `isSheafy_of_isLimitSheaf` — the converse (C5): the all-open sheaf condition
  restricts along the rational comparison `limitEval` to the finite rational
  criterion. Together: `isSheafy_iff_isLimitSheaf`.

The reduction engine: every open cover of a valid rational open admits a **finite
refinement by valid rational opens** subordinate to the cover
(`exists_finite_rational_refinement` — basis property 7.35(2) + quasi-compactness
7.35(3), from `RationalBasis`), and the refinement assembles into a
`RationalCoveringData` (`refinementCovering`) to which the `IsSheafy` fields apply.
Compatibility inputs cross the legacy all-raw-data interface through the R3 bridge
(`RationalIntersection`).
-/

@[expose] public section

universe u

noncomputable section

open TopologicalSpace Filter Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A] [DecidableEq A] [DecidableEq (RationalLocData A)]
  [IsTateRing A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]

/-! ### Finite rational refinements (7.35(2) + 7.35(3)) -/

/-- The index of a refinement: a valid rational datum together with a cover-member it
is subordinate to. -/
def RefinementIndex (D : RationalLocData A) {ι : Type*} (U : ι → Set ↥(Spa A A⁺)) :
    Type _ :=
  {q : RationalLocData A × ι // q.1.IsRational ∧ spaOpen q.1 ⊆ spaOpen D ∩ U q.2}

omit [DecidableEq (RationalLocData A)] [HasLocLiftPowerBounded A] in
/-- **Finite rational refinement of an open cover on a rational open** (Wedhorn
7.35(2)+(3)): finitely many valid rational opens, each inside `spaOpen D` and inside a
member of the covering family, which cover `spaOpen D`. -/
theorem exists_finite_rational_refinement (D : RationalLocData A) (hD : D.IsRational)
    {ι : Type*} (U : ι → Set ↥(Spa A A⁺)) (hUopen : ∀ i, IsOpen (U i))
    (hUcov : spaOpen D ⊆ ⋃ i, U i) :
    ∃ t : Finset (RefinementIndex D U),
      spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1 := by
  classical
  have hcov : spaOpen D ⊆ ⋃ q : RefinementIndex D U, spaOpen q.1.1 := by
    intro v hv
    obtain ⟨i, hvU⟩ := Set.mem_iUnion.mp (hUcov hv)
    obtain ⟨E, hErat, hvE, hEsub⟩ := exists_isRational_spaOpen_subset
      ((isOpen_spaOpen D).inter (hUopen i)) (Set.mem_inter hv hvU)
    exact Set.mem_iUnion.mpr ⟨⟨(E, i), hErat, hEsub⟩, hvE⟩
  obtain ⟨t, ht⟩ := (isCompact_spaOpen D hD).elim_finite_subcover
    (fun q : RefinementIndex D U => spaOpen q.1.1) (fun q => isOpen_spaOpen _) hcov
  exact ⟨t, ht⟩

/-- The `RationalCoveringData` assembled from a finite rational refinement of `spaOpen D`.
`@[reducible]` so that `.base`/`.covers`-projections reduce at reducible transparency
(v4.33 `kabstract` re-checks; cf. the wave-9 notes). -/
@[reducible]
def refinementCovering (D : RationalLocData A) {ι : Type*}
    {U : ι → Set ↥(Spa A A⁺)} (t : Finset (RefinementIndex D U))
    (ht : spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1) :
    RationalCoveringData A where
  base := D
  covers := t.image (fun q => q.1.1)
  hsubset := by
    intro E hE
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hE
    exact spaOpen_subset_iff.mp (q.2.2.trans Set.inter_subset_left)
  hcover := by
    intro v hv
    have hv' : (⟨v, rationalOpen_subset_spa hv⟩ : ↥(Spa A A⁺)) ∈ spaOpen D := hv
    obtain ⟨q, hqt, hvq⟩ := Set.mem_iUnion₂.mp (ht hv')
    exact ⟨q.1.1, Finset.mem_image_of_mem _ hqt, hvq⟩

omit [DecidableEq A] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] in
@[simp] theorem refinementCovering_covers (D : RationalLocData A) {ι : Type*}
    {U : ι → Set ↥(Spa A A⁺)} (t : Finset (RefinementIndex D U))
    (ht : spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1) :
    (refinementCovering D t ht).covers = t.image (fun q => q.1.1) := rfl

omit [DecidableEq A] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] in
theorem refinementCovering_isRational (D : RationalLocData A) (hD : D.IsRational)
    {ι : Type*} {U : ι → Set ↥(Spa A A⁺)} (t : Finset (RefinementIndex D U))
    (ht : spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1) :
    (refinementCovering D t ht).IsRational := by
  refine ⟨hD, ?_⟩
  intro E hE
  rw [refinementCovering_covers] at hE
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hE
  exact q.2.1

omit [DecidableEq A] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] in
@[simp] theorem refinementCovering_base (D : RationalLocData A) {ι : Type*}
    {U : ι → Set ↥(Spa A A⁺)} (t : Finset (RefinementIndex D U))
    (ht : spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1) :
    (refinementCovering D t ht).base = D := rfl

/-! ### Separation for arbitrary open covers (C3, separation half) -/

variable [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- Pieces of the refinement covering, as indices of the limit at any open `W` that
contains their rational open. -/
def RefinementIndex.toRationalIndex {D : RationalLocData A} {ι : Type*}
    {U : ι → Set ↥(Spa A A⁺)} (q : RefinementIndex D U)
    {W : Opens ↥(Spa A A⁺)} (hW : spaOpen q.1.1 ⊆ (W : Set ↥(Spa A A⁺))) :
    RationalIndex W :=
  ⟨q.1.1, q.2.1, hW⟩

/-- **Separation of the all-open presheaf on arbitrary covers**: two sections of
`𝒪_X(V)` agreeing on every member of an open cover of `V` are equal. Per rational
index `D ≤ V`: refine the cover finitely and rationally on `spaOpen D`
(`exists_finite_rational_refinement`), observe both sections restrict equally to every
refinement piece (through the cover member containing it), and conclude by the
injectivity half of the `IsSheafy` embedding on the refinement covering. -/
theorem limitRestrict_injective [IsSheafy A]
    {V : Opens ↥(Spa A A⁺)} {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    {x y : ↥(limitSections V)}
    (h : ∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) : x = y := by
  classical
  refine Subtype.ext (funext fun D => ?_)
  obtain ⟨t, ht⟩ := exists_finite_rational_refinement D.D D.isRational
    (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2)
    (D.subset.trans hcov)
  set C := refinementCovering D.D t ht with hC
  have hCrat : C.IsRational := refinementCovering_isRational D.D D.isRational t ht
  -- the two sections have equal product restrictions on the refinement covering
  have hprod : productRestrictionSub A C
        ((x : ∀ j : RationalIndex V, presheafValue j.D) D) =
      productRestrictionSub A C
        ((y : ∀ j : RationalIndex V, presheafValue j.D) D) := by
    funext ⟨E, hE⟩
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp
      (show E ∈ t.image (fun q => q.1.1) from hE)
    -- E := q.1.1 is an index of `U q.1.2` and of `V`
    have hEUi : spaOpen q.1.1 ⊆ (U q.1.2 : Set ↥(Spa A A⁺)) :=
      q.2.2.trans Set.inter_subset_right
    have hEV : spaOpen q.1.1 ⊆ (V : Set ↥(Spa A A⁺)) := hEUi.trans (hle q.1.2)
    have hED : rationalOpen q.1.1.T q.1.1.s ⊆ rationalOpen D.D.T D.D.s :=
      spaOpen_subset_iff.mp (q.2.2.trans Set.inter_subset_left)
    -- restriction of the section to the refinement piece, through `V`
    have hx : restrictionMap D.D q.1.1 hED
        ((x : ∀ j : RationalIndex V, presheafValue j.D) D) =
        (x : ∀ j : RationalIndex V, presheafValue j.D) ⟨q.1.1, q.2.1, hEV⟩ :=
      x.2 D ⟨q.1.1, q.2.1, hEV⟩ hED
    have hy : restrictionMap D.D q.1.1 hED
        ((y : ∀ j : RationalIndex V, presheafValue j.D) D) =
        (y : ∀ j : RationalIndex V, presheafValue j.D) ⟨q.1.1, q.2.1, hEV⟩ :=
      y.2 D ⟨q.1.1, q.2.1, hEV⟩ hED
    show restrictionMap D.D q.1.1 hED _ = restrictionMap D.D q.1.1 hED _
    rw [hx, hy]
    -- values at the `V`-index equal values of the restricted sections at the
    -- `U q.1.2`-index (definitional reindexing), which agree by hypothesis
    have := congr_fun (congrArg (fun z : ↥(limitSections (U q.1.2)) =>
      (z : ∀ j : RationalIndex (U q.1.2), presheafValue j.D)) (h q.1.2))
      ⟨q.1.1, q.2.1, hEUi⟩
    exact this
  -- injectivity from the `IsSheafy` embedding on the refinement covering
  have hinj := IsSheafy.separationSub (A := A) C hCrat hprod
  exact hinj

/-! ### Gluing for arbitrary open covers (C3, gluing half) -/

/-- The pieces of the intersection covering: the exact intersections of `E'` with the
pieces of `C` (extracted as a named `Finset` so the covering's field types stay small). -/
def interCoveringPieces (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational) : Finset (RationalLocData A) :=
  C.covers.attach.image fun E => E'.interRational E.1 hE' (hC.piece E.2)

omit [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
theorem mem_interCoveringPieces (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational) {F : RationalLocData A} :
    F ∈ interCoveringPieces E' hE' C hC ↔
      ∃ E : ↥C.covers, E'.interRational E.1 hE' (hC.piece E.2) = F := by
  unfold interCoveringPieces
  simp only [Finset.mem_image, Finset.mem_attach, true_and]

/-- The covering of a valid rational `E'` inside `C.base` by its exact intersections
with the pieces of `C` (R1's `interRational` fold of one datum against a covering). -/
def interCovering (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hsub : rationalOpen E'.T E'.s ⊆ rationalOpen C.base.T C.base.s) :
    RationalCoveringData A where
  base := E'
  covers := interCoveringPieces E' hE' C hC
  hsubset := by
    intro F hF
    obtain ⟨E, hFeq⟩ := (mem_interCoveringPieces E' hE' C hC).mp hF
    exact hFeq ▸ RationalLocData.interRational_subset_left _ _ _ _
  hcover := by
    intro v hv
    obtain ⟨E, hEC, hvE⟩ := C.hcover v (hsub hv)
    refine ⟨E'.interRational E hE' (hC.piece hEC),
      (mem_interCoveringPieces E' hE' C hC).mpr ⟨⟨E, hEC⟩, rfl⟩, ?_⟩
    rw [RationalLocData.interRational_rationalOpen]
    exact ⟨hv, hvE⟩

omit [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
theorem interCovering_isRational (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hsub : rationalOpen E'.T E'.s ⊆ rationalOpen C.base.T C.base.s) :
    (interCovering E' hE' C hC hsub).IsRational := by
  refine ⟨hE', ?_⟩
  intro F hF
  obtain ⟨E, hFeq⟩ := (mem_interCoveringPieces E' hE' C hC).mp hF
  exact hFeq ▸ RationalLocData.interRational_isRational _ _ _ _

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- Agreement of the compatible family across cover members: for a valid rational `E`
inside `U i` and `U j`, the two evaluations agree (evaluate the inf-compatibility at
the `E`-index of `U i ⊓ U j`). -/
theorem limitFamily_eval_eq {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j))
    (E : RationalLocData A) (hErat : E.IsRational) (i j : ι)
    (hEi : spaOpen E ⊆ (U i : Set ↥(Spa A A⁺)))
    (hEj : spaOpen E ⊆ (U j : Set ↥(Spa A A⁺))) :
    (s i).1 ⟨E, hErat, hEi⟩ = (s j).1 ⟨E, hErat, hEj⟩ := by
  have hEinf : spaOpen E ⊆ ((U i ⊓ U j : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) := by
    rw [Opens.coe_inf]
    exact Set.subset_inter hEi hEj
  exact congr_fun (congrArg Subtype.val (hs i j)) ⟨E, hErat, hEinf⟩

/-- **Gluing of the all-open presheaf on arbitrary covers**: a compatible family of
sections over an open cover of `V` glues to a section of `𝒪_X(V)`. Per rational index
`D ≤ V`: refine the cover finitely and rationally, transport the family to the
refinement pieces, check the literature (valid-refinement) compatibility, cross the R3
bridge to the legacy all-raw-data input, and glue by `IsSheafy.gluing`; the glued
values are compatible and restrict correctly by the separation argument on the
intersection coverings (`interCovering`). -/
theorem exists_limitSections_glue [IsSheafy A]
    {V : Opens ↥(Spa A A⁺)} {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) :
    ∃ x : ↥(limitSections V), ∀ i, limitRestrict (hle i) x = s i := by
  classical
  -- ————— the per-rational-datum glued value —————
  -- For every valid rational `D₀ ⊆ V` choose a finite rational refinement and glue.
  have hglue : ∀ (D₀ : RationalLocData A), D₀.IsRational →
      spaOpen D₀ ⊆ (V : Set ↥(Spa A A⁺)) →
      ∃ z : presheafValue D₀,
        ∀ (E : RationalLocData A) (hErat : E.IsRational)
          (hED : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) (i : ι)
          (hEUi : spaOpen E ⊆ (U i : Set ↥(Spa A A⁺))),
          restrictionMap D₀ E hED z = (s i).1 ⟨E, hErat, hEUi⟩ := by
    intro D₀ hD₀ hD₀V
    obtain ⟨t, ht⟩ := exists_finite_rational_refinement D₀ hD₀
      (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (hD₀V.trans hcov)
    set C := refinementCovering D₀ t ht with hCdef
    have hCrat : C.IsRational := refinementCovering_isRational D₀ hD₀ t ht
    -- the candidate family on the refinement pieces
    have hexE : ∀ E : ↥C.covers,
        E.1.IsRational ∧ ∃ i : ι, spaOpen E.1 ⊆ (U i : Set ↥(Spa A A⁺)) := by
      rintro ⟨E, hE⟩
      obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp
        (show E ∈ t.image (fun q => q.1.1) from hE)
      exact ⟨q.2.1, q.1.2, q.2.2.trans Set.inter_subset_right⟩
    set f : ∀ E : ↥C.covers, presheafValue E.1 := fun E =>
      (s (hexE E).2.choose).1 ⟨E.1, (hexE E).1, (hexE E).2.choose_spec⟩ with hfdef
    -- literature compatibility of the candidate family
    have hfcompat : C.RationalRefinementCompatible f := by
      intro E₁ E₂ F hFrat h₁ h₂
      have hFU₁ : spaOpen F ⊆ (U (hexE E₁).2.choose : Set ↥(Spa A A⁺)) :=
        (spaOpen_subset_of_rationalOpen_subset h₁).trans (hexE E₁).2.choose_spec
      have hFU₂ : spaOpen F ⊆ (U (hexE E₂).2.choose : Set ↥(Spa A A⁺)) :=
        (spaOpen_subset_of_rationalOpen_subset h₂).trans (hexE E₂).2.choose_spec
      calc restrictionMap E₁.1 F h₁ (f E₁)
          = (s (hexE E₁).2.choose).1 ⟨F, hFrat, hFU₁⟩ :=
            (s (hexE E₁).2.choose).2 ⟨E₁.1, (hexE E₁).1, (hexE E₁).2.choose_spec⟩
              ⟨F, hFrat, hFU₁⟩ h₁
        _ = (s (hexE E₂).2.choose).1 ⟨F, hFrat, hFU₂⟩ :=
            limitFamily_eval_eq s hs F hFrat _ _ hFU₁ hFU₂
        _ = restrictionMap E₂.1 F h₂ (f E₂) :=
            ((s (hexE E₂).2.choose).2 ⟨E₂.1, (hexE E₂).1, (hexE E₂).2.choose_spec⟩
              ⟨F, hFrat, hFU₂⟩ h₂).symm
    -- cross the R3 bridge and glue
    obtain ⟨z, hz⟩ := IsSheafy.gluing (A := A) C hCrat f
      ((hfcompat.exactIntersection hCrat).allData hCrat)
    refine ⟨z, ?_⟩
    -- ————— the local characterization of the glued value —————
    intro E hErat hED i hEUi
    -- separation at `E` along its intersections with the refinement pieces
    have hEbase : rationalOpen E.T E.s ⊆ rationalOpen C.base.T C.base.s := hED
    set CE := interCovering E hErat C hCrat hEbase with hCEdef
    have hCErat : CE.IsRational := interCovering_isRational E hErat C hCrat hEbase
    refine IsSheafy.separationSub (A := A) CE hCErat ?_
    funext q
    obtain ⟨E₀, hFeq⟩ := (mem_interCoveringPieces E hErat C hCrat).mp q.2
    have hFrat : q.1.IsRational := hCErat.piece q.2
    have hFE : rationalOpen q.1.T q.1.s ⊆ rationalOpen E.T E.s := CE.hsubset q.1 q.2
    have hFE₀ : rationalOpen q.1.T q.1.s ⊆ rationalOpen E₀.1.T E₀.1.s :=
      hFeq ▸ RationalLocData.interRational_subset_right _ _ _ _
    have hFU_i : spaOpen q.1 ⊆ (U i : Set ↥(Spa A A⁺)) :=
      (spaOpen_subset_of_rationalOpen_subset hFE).trans hEUi
    have hi₀ := (hexE E₀).2.choose_spec
    have hFU_i₀ : spaOpen q.1 ⊆ (U (hexE E₀).2.choose : Set ↥(Spa A A⁺)) :=
      (spaOpen_subset_of_rationalOpen_subset hFE₀).trans hi₀
    -- left composite: through the refinement piece `E₀`
    have hcompL := congr_fun (restrictionMap_comp D₀ E₀.1 q.1
      (C.hsubset E₀.1 E₀.2) hFE₀) z
    simp only [Function.comp_apply] at hcompL
    -- right composite: through `E`
    have hcompR := congr_fun (restrictionMap_comp D₀ E q.1 hED hFE) z
    simp only [Function.comp_apply] at hcompR
    show restrictionMap E q.1 hFE (restrictionMap D₀ E hED z) =
      restrictionMap E q.1 hFE ((s i).1 ⟨E, hErat, hEUi⟩)
    calc restrictionMap E q.1 hFE (restrictionMap D₀ E hED z)
        = restrictionMap D₀ q.1 (hFE.trans hED) z := hcompR
      _ = restrictionMap E₀.1 q.1 hFE₀
            (restrictionMap D₀ E₀.1 (C.hsubset E₀.1 E₀.2) z) := hcompL.symm
      _ = restrictionMap E₀.1 q.1 hFE₀ (f E₀) := by rw [hz E₀]
      _ = (s (hexE E₀).2.choose).1 ⟨q.1, hFrat, hFU_i₀⟩ :=
          (s _).2 ⟨E₀.1, (hexE E₀).1, hi₀⟩ ⟨q.1, hFrat, hFU_i₀⟩ hFE₀
      _ = (s i).1 ⟨q.1, hFrat, hFU_i⟩ :=
          limitFamily_eval_eq s hs q.1 hFrat _ _ hFU_i₀ hFU_i
      _ = restrictionMap E q.1 hFE ((s i).1 ⟨E, hErat, hEUi⟩) :=
          ((s i).2 ⟨E, hErat, hEUi⟩ ⟨q.1, hFrat, hFU_i⟩ hFE).symm
  -- ————— choose per-index glued values and assemble the section —————
  choose z hzchar using hglue
  refine ⟨⟨fun D => z D.D D.isRational D.subset, ?_⟩, ?_⟩
  · -- compatibility of the assembled family: separation on the intersection covering
    intro D D' hD'D
    -- both sides agree on every valid rational refinement of `D'` inside a cover
    -- member; conclude by separation at `D'` with its own finite refinement
    obtain ⟨t', ht'⟩ := exists_finite_rational_refinement D'.D D'.isRational
      (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (D'.subset.trans hcov)
    set C' := refinementCovering D'.D t' ht' with hC'def
    have hC'rat : C'.IsRational :=
      refinementCovering_isRational D'.D D'.isRational t' ht'
    refine IsSheafy.separationSub (A := A) C' hC'rat ?_
    funext ⟨E', hE'⟩
    obtain ⟨q', hq't, rfl⟩ := Finset.mem_image.mp
      (show E' ∈ t'.image (fun q => q.1.1) from hE')
    have hE'rat : q'.1.1.IsRational := q'.2.1
    have hE'D' : rationalOpen q'.1.1.T q'.1.1.s ⊆ rationalOpen D'.D.T D'.D.s :=
      spaOpen_subset_iff.mp (q'.2.2.trans Set.inter_subset_left)
    have hE'U : spaOpen q'.1.1 ⊆ (U q'.1.2 : Set ↥(Spa A A⁺)) :=
      q'.2.2.trans Set.inter_subset_right
    have hcomp := congr_fun (restrictionMap_comp D.D D'.D q'.1.1 hD'D hE'D')
      (z D.D D.isRational D.subset)
    simp only [Function.comp_apply] at hcomp
    show restrictionMap D'.D q'.1.1 hE'D'
        (restrictionMap D.D D'.D hD'D (z D.D D.isRational D.subset)) =
      restrictionMap D'.D q'.1.1 hE'D' (z D'.D D'.isRational D'.subset)
    rw [hcomp, hzchar D.D D.isRational D.subset q'.1.1 hE'rat (hE'D'.trans hD'D)
        q'.1.2 hE'U,
      hzchar D'.D D'.isRational D'.subset q'.1.1 hE'rat hE'D' q'.1.2 hE'U]
  · -- the assembled section restricts to the family
    intro i
    refine Subtype.ext (funext fun F => ?_)
    -- value at the `V`-lift of `F`
    show z F.D F.isRational (F.subset.trans (hle i)) = (s i).1 F
    -- separation at `F` with its own refinement covering
    obtain ⟨tF, htF⟩ := exists_finite_rational_refinement F.D F.isRational
      (fun j => (U j : Set ↥(Spa A A⁺))) (fun j => (U j).2)
      ((F.subset.trans (hle i)).trans hcov)
    set CF := refinementCovering F.D tF htF with hCFdef
    have hCFrat : CF.IsRational :=
      refinementCovering_isRational F.D F.isRational tF htF
    refine IsSheafy.separationSub (A := A) CF hCFrat ?_
    funext ⟨E, hE⟩
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp
      (show E ∈ tF.image (fun q => q.1.1) from hE)
    have hErat : q.1.1.IsRational := q.2.1
    have hEF : rationalOpen q.1.1.T q.1.1.s ⊆ rationalOpen F.D.T F.D.s :=
      spaOpen_subset_iff.mp (q.2.2.trans Set.inter_subset_left)
    have hEU : spaOpen q.1.1 ⊆ (U q.1.2 : Set ↥(Spa A A⁺)) :=
      q.2.2.trans Set.inter_subset_right
    have hEUi : spaOpen q.1.1 ⊆ (U i : Set ↥(Spa A A⁺)) :=
      (spaOpen_subset_of_rationalOpen_subset hEF).trans (Set.Subset.trans F.subset
        (by exact fun v hv => hv))
    show restrictionMap F.D q.1.1 hEF (z F.D F.isRational (F.subset.trans (hle i))) =
      restrictionMap F.D q.1.1 hEF ((s i).1 F)
    rw [hzchar F.D F.isRational (F.subset.trans (hle i)) q.1.1 hErat hEF q.1.2 hEU,
      (s i).2 F ⟨q.1.1, hErat, hEUi⟩ hEF]
    exact limitFamily_eval_eq s hs q.1.1 hErat _ _ hEU hEUi

/-! ### The topological embedding on arbitrary covers (C4, Wedhorn Remark 8.20) -/

/-- The restriction map into the product over an open cover. -/
def limitRestrictProd {V : Opens ↥(Spa A A⁺)} {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (x : ↥(limitSections V)) : ∀ i, ↥(limitSections (U i)) :=
  fun i => limitRestrict (hle i) x

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
theorem limitRestrictProd_continuous {V : Opens ↥(Spa A A⁺)} {ι : Type*}
    {U : ι → Opens ↥(Spa A A⁺)} (hle : ∀ i, U i ≤ V) :
    Continuous (limitRestrictProd hle) :=
  continuous_pi fun i => limitRestrict_continuous (hle i)

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- The neighbourhood filter of the limit is the infimum of the comaps of the rational
evaluations (the projective-limit topology, in filter form). -/
theorem nhds_limitSections {V : Opens ↥(Spa A A⁺)} (x : ↥(limitSections V)) :
    𝓝 x = ⨅ D : RationalIndex V,
      Filter.comap (fun y : ↥(limitSections V) =>
        (y : ∀ j : RationalIndex V, presheafValue j.D) D)
        (𝓝 ((x : ∀ j : RationalIndex V, presheafValue j.D) D)) := by
  rw [nhds_subtype, nhds_pi, Filter.pi, Filter.comap_iInf]
  simp only [Filter.comap_comap]
  rfl

/-- **The arbitrary-cover topological embedding** (Wedhorn Remark 8.20's second
condition, for the genuine all-open presheaf): for every open cover of `V`, the
restriction `𝒪_X(V) → ∏ᵢ 𝒪_X(Uᵢ)` is a topological embedding. Inducing: each rational
evaluation is recovered continuously from the cover product through a finite rational
refinement and the finite `IsSheafy` embedding, so the initial (projective-limit)
topology of the source coincides with the topology induced from the product. -/
theorem isEmbedding_limitRestrictProd [IsSheafy A]
    {V : Opens ↥(Spa A A⁺)} {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) :
    Topology.IsEmbedding (limitRestrictProd hle) := by
  classical
  refine ⟨Topology.isInducing_iff_nhds.mpr fun x => le_antisymm ?_ ?_, ?_⟩
  · -- continuity direction
    exact ((limitRestrictProd_continuous hle).tendsto x).le_comap
  · -- the interesting direction: the comap of the product refines every rational
    -- evaluation comap
    rw [nhds_limitSections x]
    refine le_iInf fun D => ?_
    obtain ⟨t, ht⟩ := exists_finite_rational_refinement D.D D.isRational
      (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (D.subset.trans hcov)
    set C := refinementCovering D.D t ht with hCdef
    have hCrat : C.IsRational := refinementCovering_isRational D.D D.isRational t ht
    have hexE : ∀ E : ↥C.covers,
        E.1.IsRational ∧ ∃ i : ι, spaOpen E.1 ⊆ (U i : Set ↥(Spa A A⁺)) := by
      rintro ⟨E, hE⟩
      obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp
        (show E ∈ t.image (fun q => q.1.1) from hE)
      exact ⟨q.2.1, q.1.2, q.2.2.trans Set.inter_subset_right⟩
    -- the extraction map from the cover product to the refinement product
    set Φ : (∀ i, ↥(limitSections (U i))) → (∀ E : ↥C.covers, presheafValue E.1) :=
      fun y E => (y (hexE E).2.choose : ∀ j : RationalIndex (U (hexE E).2.choose),
        presheafValue j.D) ⟨E.1, (hexE E).1, (hexE E).2.choose_spec⟩ with hΦdef
    have hΦcont : Continuous Φ := by
      refine continuous_pi fun E => ?_
      exact ((continuous_apply _).comp continuous_subtype_val).comp
        (continuous_apply (hexE E).2.choose)
    -- the extraction of the restricted family is the finite product restriction of
    -- the evaluation (compatibility of the section)
    have hfactor : ∀ y : ↥(limitSections V),
        Φ (limitRestrictProd hle y) = productRestrictionSub A C
          ((y : ∀ j : RationalIndex V, presheafValue j.D) D) := by
      intro y
      funext E
      have hED : rationalOpen E.1.T E.1.s ⊆ rationalOpen D.D.T D.D.s :=
        C.hsubset E.1 E.2
      have hEV : spaOpen E.1 ⊆ (V : Set ↥(Spa A A⁺)) :=
        (hexE E).2.choose_spec.trans (hle (hexE E).2.choose)
      show (y : ∀ j : RationalIndex V, presheafValue j.D) ⟨E.1, (hexE E).1, hEV⟩ =
        restrictionMap D.D E.1 hED ((y : ∀ j : RationalIndex V, presheafValue j.D) D)
      exact (y.2 D ⟨E.1, (hexE E).1, hEV⟩ hED).symm
    -- the finite `IsSheafy` embedding recovers the evaluation
    have hemb := (IsSheafy.embedding (A := A) C hCrat).isInducing.nhds_eq_comap
      ((x : ∀ j : RationalIndex V, presheafValue j.D) D)
    calc Filter.comap (limitRestrictProd hle) (𝓝 (limitRestrictProd hle x))
        ≤ Filter.comap (limitRestrictProd hle)
            (Filter.comap Φ (𝓝 (Φ (limitRestrictProd hle x)))) :=
          Filter.comap_mono ((hΦcont.tendsto _).le_comap)
      _ = Filter.comap (fun y : ↥(limitSections V) =>
            productRestrictionSub A C
              ((y : ∀ j : RationalIndex V, presheafValue j.D) D))
            (𝓝 (productRestrictionSub A C
              ((x : ∀ j : RationalIndex V, presheafValue j.D) D))) := by
          rw [Filter.comap_comap]
          congr 1
          · exact funext hfactor
          · rw [hfactor x]
      _ = Filter.comap (fun y : ↥(limitSections V) =>
            (y : ∀ j : RationalIndex V, presheafValue j.D) D)
            (Filter.comap (productRestrictionSub A C)
              (𝓝 (productRestrictionSub A C
                ((x : ∀ j : RationalIndex V, presheafValue j.D) D)))) := by
          rw [Filter.comap_comap]
          rfl
      _ = Filter.comap (fun y : ↥(limitSections V) =>
            (y : ∀ j : RationalIndex V, presheafValue j.D) D)
            (𝓝 ((x : ∀ j : RationalIndex V, presheafValue j.D) D)) := by
          rw [← hemb]
  · -- injectivity = separation
    intro x y hxy
    exact limitRestrict_injective hle hcov fun i => congr_fun hxy i

/-! ### The bundled sheaf-of-topological-rings statement and the C5 equivalence -/

/-- **The genuine all-open structure presheaf is a sheaf of topological rings**
(bundled; Wedhorn Remark 8.20 for the projective-limit presheaf): separation and
gluing of the underlying ring presheaf for **every** open cover of **every** open, and
the topological-embedding condition for every open cover. The cover index lives in the
ring's universe (covers in use are (sub)types of `RationalLocData A`-data; larger
index types factor through their ranges). -/
structure IsLimitSheaf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A]
    [HasLocLiftPowerBounded A] : Prop where
  /-- Separation: sections agreeing on a cover agree. -/
  injective : ∀ {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (_ : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    {x y : ↥(limitSections V)},
    (∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) → x = y
  /-- Gluing: compatible families glue. -/
  glue : ∀ {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (_ : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (s : ∀ i, ↥(limitSections (U i))),
    (∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
            limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) →
    ∃ x : ↥(limitSections V), ∀ i, limitRestrict (hle i) x = s i
  /-- The restriction into the product over any open cover is a topological embedding. -/
  isEmbedding : ∀ {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (_ : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))),
    Topology.IsEmbedding (limitRestrictProd hle)

/-- **C3+C4**: the finite rational-cover criterion implies that the genuine all-open
structure presheaf is a sheaf of topological rings. -/
theorem isLimitSheaf_of_isSheafy [IsSheafy A] : IsLimitSheaf A :=
  { injective := fun hle hcov => limitRestrict_injective hle hcov
    glue := fun hle hcov s hs => exists_limitSections_glue hle hcov s hs
    isEmbedding := fun hle hcov => isEmbedding_limitRestrictProd hle hcov }

/-! ### The converse (C5): the all-open sheaf condition restricts to the finite
rational criterion -/

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- The cover-member inclusions of a rational covering, at the `Opens`-level. -/
theorem spaOpens_le_of_covering (C : RationalCoveringData A) (E : ↥C.covers) :
    spaOpens E.1 ≤ spaOpens C.base :=
  spaOpen_subset_of_rationalOpen_subset (C.hsubset E.1 E.2)

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
theorem spaOpens_covering_subset (C : RationalCoveringData A) :
    ((spaOpens C.base : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) ⊆
      ⋃ E : ↥C.covers, ((spaOpens E.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) := by
  intro v hv
  obtain ⟨E, hEC, hvE⟩ := C.hcover v.1 hv
  exact Set.mem_iUnion.mpr ⟨⟨E, hEC⟩, hvE⟩

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- `𝒪_X(R(D₀))` carries the topology comap-ed from the limit along
"restrict everywhere" (the rational comparison is a homeomorphism). -/
theorem nhds_eq_comap_limitOfValue {D₀ : RationalLocData A} (hD₀ : D₀.IsRational)
    (g : presheafValue D₀) :
    𝓝 g = Filter.comap (limitOfValue D₀) (𝓝 (limitOfValue D₀ g)) := by
  refine le_antisymm ((limitOfValue_continuous D₀).tendsto g).le_comap ?_
  have hid : (limitEval hD₀) ∘ (limitOfValue D₀) = id :=
    funext fun y => (limitEval hD₀).apply_symm_apply y
  calc Filter.comap (limitOfValue D₀) (𝓝 (limitOfValue D₀ g))
      ≤ Filter.comap (limitOfValue D₀) (Filter.comap (limitEval hD₀)
          (𝓝 (limitEval hD₀ (limitOfValue D₀ g)))) :=
        Filter.comap_mono ((limitEval_continuous hD₀).tendsto _).le_comap
    _ = Filter.comap ((limitEval hD₀) ∘ (limitOfValue D₀))
          (𝓝 (limitEval hD₀ (limitOfValue D₀ g))) := Filter.comap_comap
    _ = 𝓝 g := by
        rw [hid, Filter.comap_id]
        congr 1
        exact (limitEval hD₀).apply_symm_apply g

-- (`productRestrictionSub_continuous` is provided by `EmbeddingTopo.lean`; the same
-- statement here is re-proved locally to keep this file's import cone small.)
omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
theorem productRestrictionSub_continuous' (C : RationalCoveringData A) :
    Continuous (productRestrictionSub A C) := by
  refine continuous_pi fun E => ?_
  show Continuous fun x : presheafValue C.base =>
    restrictionMap C.base E.1 (C.hsubset E.1 E.2) x
  exact restrictionMapHom_continuous C.base E.1 (C.hsubset E.1 E.2)

omit [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A] in
/-- **C5, converse direction**: if the genuine all-open structure presheaf is a sheaf
of topological rings, the finite rational-cover criterion holds — the sheaf and
embedding conditions restrict along the rational comparison `limitEval` to every
finite rational covering. Together with `isLimitSheaf_of_isSheafy` this identifies the
project's chosen-pair criterion `IsSheafy` with genuine pair-level sheafiness. -/
theorem isSheafy_of_isLimitSheaf (h : IsLimitSheaf A) : IsSheafy A := by
  constructor
  · -- embedding on finite rational covers
    intro C hC
    -- the evaluation of the limit-restrictions at the tautological indices
    set Ψ : (∀ E : ↥C.covers, ↥(limitSections (spaOpens E.1))) →
        (∀ E : ↥C.covers, presheafValue E.1) := fun y E =>
      (y E : ∀ j : RationalIndex (spaOpens E.1), presheafValue j.D)
        (RationalIndex.self E.1 (hC.piece E.2)) with hΨdef
    have hΨcont : Continuous Ψ := by
      refine continuous_pi fun E => ?_
      exact ((continuous_apply _).comp continuous_subtype_val).comp (continuous_apply E)
    -- the product restriction factors through the limit
    have hfac : productRestrictionSub A C =
        Ψ ∘ (limitRestrictProd (spaOpens_le_of_covering C)) ∘ (limitOfValue C.base) := by
      funext g E
      rfl
    have hInj : Function.Injective (productRestrictionSub A C) := by
      intro g g' hgg'
      have hlim : limitOfValue C.base g = limitOfValue C.base g' := by
        refine h.injective (ι := ↥C.covers) (U := fun E : ↥C.covers => spaOpens E.1)
          (spaOpens_le_of_covering C) (spaOpens_covering_subset C) (fun E => ?_)
        refine Subtype.ext (funext fun F => ?_)
        have hFE : rationalOpen F.D.T F.D.s ⊆ rationalOpen E.1.T E.1.s :=
          spaOpen_subset_iff.mp F.subset
        have h1 := congr_fun (restrictionMap_comp C.base E.1 F.D
          (C.hsubset E.1 E.2) hFE) g
        have h1' := congr_fun (restrictionMap_comp C.base E.1 F.D
          (C.hsubset E.1 E.2) hFE) g'
        simp only [Function.comp_apply] at h1 h1'
        have h2 : restrictionMap C.base E.1 (C.hsubset E.1 E.2) g =
            restrictionMap C.base E.1 (C.hsubset E.1 E.2) g' := congr_fun hgg' E
        show restrictionMap C.base F.D _ g = restrictionMap C.base F.D _ g'
        calc restrictionMap C.base F.D (hFE.trans (C.hsubset E.1 E.2)) g
            = restrictionMap E.1 F.D hFE
                (restrictionMap C.base E.1 (C.hsubset E.1 E.2) g) := h1.symm
          _ = restrictionMap E.1 F.D hFE
                (restrictionMap C.base E.1 (C.hsubset E.1 E.2) g') := by rw [h2]
          _ = restrictionMap C.base F.D (hFE.trans (C.hsubset E.1 E.2)) g' := h1'
      calc g = limitEval hC.base (limitOfValue C.base g) :=
            ((limitEval hC.base).apply_symm_apply g).symm
        _ = limitEval hC.base (limitOfValue C.base g') := congrArg _ hlim
        _ = g' := (limitEval hC.base).apply_symm_apply g'
    -- `Ψ` is a product of the rational-comparison homeomorphisms, hence inducing
    have hΨind : Topology.IsInducing Ψ := by
      have hΨmap : Ψ = Pi.map (fun E : ↥C.covers =>
          (limitEval (hC.piece E.2) :
            ↥(limitSections (spaOpens E.1)) → presheafValue E.1)) := rfl
      rw [hΨmap]
      exact Topology.IsInducing.piMap fun E =>
        (Homeomorph.mk (limitEval (hC.piece E.2)).toEquiv
          (limitEval_continuous (hC.piece E.2))
          (limitEval_symm_continuous (hC.piece E.2))).isInducing
    refine ⟨Topology.isInducing_iff_nhds.mpr fun g => ?_, hInj⟩
    have hembL := (h.isEmbedding (ι := ↥C.covers) (U := fun E : ↥C.covers => spaOpens E.1)
      (spaOpens_le_of_covering C)
      (spaOpens_covering_subset C)).isInducing.nhds_eq_comap (limitOfValue C.base g)
    refine Eq.symm ?_
    calc Filter.comap (productRestrictionSub A C) (𝓝 (productRestrictionSub A C g))
        = Filter.comap ((Ψ ∘ limitRestrictProd (spaOpens_le_of_covering C)) ∘
            (limitOfValue C.base)) (𝓝 ((Ψ ∘ limitRestrictProd
              (spaOpens_le_of_covering C)) (limitOfValue C.base g))) := by
          rw [hfac]; rfl
      _ = Filter.comap (limitOfValue C.base) (Filter.comap
            (limitRestrictProd (spaOpens_le_of_covering C)) (Filter.comap Ψ
              (𝓝 (Ψ (limitRestrictProd (spaOpens_le_of_covering C)
                (limitOfValue C.base g)))))) := by
          rw [Filter.comap_comap, Filter.comap_comap]
          rfl
      _ = Filter.comap (limitOfValue C.base) (Filter.comap
            (limitRestrictProd (spaOpens_le_of_covering C))
            (𝓝 (limitRestrictProd (spaOpens_le_of_covering C)
              (limitOfValue C.base g)))) := by
          rw [← hΨind.nhds_eq_comap]
      _ = Filter.comap (limitOfValue C.base) (𝓝 (limitOfValue C.base g)) := by
          rw [← hembL]
      _ = 𝓝 g := (nhds_eq_comap_limitOfValue hC.base g).symm
  · -- gluing on finite rational covers
    intro C hC f hcompat
    set s : ∀ E : ↥C.covers, ↥(limitSections (spaOpens E.1)) :=
      fun E => limitOfValue E.1 (f E) with hsdef
    have hs : ∀ E₁ E₂, limitRestrict (inf_le_left (a := spaOpens E₁.1)
          (b := spaOpens E₂.1)) (s E₁) =
        limitRestrict (inf_le_right (a := spaOpens E₁.1) (b := spaOpens E₂.1)) (s E₂) := by
      intro E₁ E₂
      refine Subtype.ext (funext fun F => ?_)
      have hFsub : spaOpen F.D ⊆ spaOpen E₁.1 ∩ spaOpen E₂.1 := by
        have := F.subset
        rwa [Opens.coe_inf] at this
      have hF₁ : rationalOpen F.D.T F.D.s ⊆ rationalOpen E₁.1.T E₁.1.s :=
        spaOpen_subset_iff.mp (hFsub.trans Set.inter_subset_left)
      have hF₂ : rationalOpen F.D.T F.D.s ⊆ rationalOpen E₂.1.T E₂.1.s :=
        spaOpen_subset_iff.mp (hFsub.trans Set.inter_subset_right)
      show restrictionMap E₁.1 F.D hF₁ (f E₁) = restrictionMap E₂.1 F.D hF₂ (f E₂)
      exact hcompat E₁ E₂ F.D hF₁ hF₂
    obtain ⟨x, hx⟩ := h.glue (ι := ↥C.covers) (U := fun E : ↥C.covers => spaOpens E.1)
      (spaOpens_le_of_covering C) (spaOpens_covering_subset C) s hs
    refine ⟨limitEval hC.base x, fun E => ?_⟩
    have h1 : restrictionMap C.base E.1 (C.hsubset E.1 E.2) (limitEval hC.base x) =
        (x : ∀ j : RationalIndex (spaOpens C.base), presheafValue j.D)
          ⟨E.1, hC.piece E.2, spaOpen_subset_of_rationalOpen_subset
            (C.hsubset E.1 E.2)⟩ :=
      x.2 (RationalIndex.self C.base hC.base)
        ⟨E.1, hC.piece E.2, spaOpen_subset_of_rationalOpen_subset (C.hsubset E.1 E.2)⟩
        (C.hsubset E.1 E.2)
    have h2 := congr_fun (congrArg Subtype.val (hx E))
      (RationalIndex.self E.1 (hC.piece E.2))
    have h3 : restrictionMap E.1 E.1
        (RationalIndex.self E.1 (hC.piece E.2)).rationalOpen_subset (f E) = f E :=
      congr_fun (restrictionMap_id E.1) (f E)
    exact h1.trans (h2.trans h3)

/-- **C5 (fixed-pair equivalence)**: the project's finite rational-cover criterion is
*exactly* pair-level sheafiness — the genuine all-open projective-limit structure
presheaf is a sheaf of topological rings iff `IsSheafy A` holds. -/
theorem isSheafy_iff_isLimitSheaf : IsSheafy A ↔ IsLimitSheaf A :=
  ⟨fun _ => isLimitSheaf_of_isSheafy, isSheafy_of_isLimitSheaf⟩

end ValuationSpectrum
