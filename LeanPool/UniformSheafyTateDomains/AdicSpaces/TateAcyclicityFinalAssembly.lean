/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricReduction
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HubnerSeparation
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor832

/-!
# Final Part-2 assembly: direct per-E route with abstract Lane A/B suppliers

This file exports the caller-ready Part-2 closure theorem on the **direct
per-E route** from `GeometricReduction.lean`:

* `RationalCoveringData.tateAcyclicity_Part2_direct_per_E` — core direct per-E
  Part-2 assembly.
* `RationalCoveringData.tateAcyclicity_Part2_via_hZavyalov_per_E_direct` —
  caller wrapper threading `hZavyalov_per_E` existential through
  `refines_by_standard_cover_per_E` and applying the direct assembly.
* `RationalCoveringData.tateAcyclicity_end_to_end_via_primary_laneA` — full
  separation-and-gluing conjunction from an explicit Part 1 supplier plus the
  Lane-A-internalized direct per-E Part 2 wrapper.

The direct per-E route takes Lane A and Lane B as **abstract universal
supplier hypotheses** (uniformly in the standard cover `S'`), matching the
mathematical shape: both lanes hold for any valid standard cover, so
accepting `∀ S', …` is honest to the mathematics and decouples the lane
content from the classically chosen `S` inside the `hZavyalov_per_E`
existential.

## The exported theorem

`RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary` is the
downstream-facing name; its body is defeq to
`tateAcyclicity_Part2_via_hZavyalov_per_E_direct`, i.e. the direct
per-E wrapper with abstract Lane A/B suppliers.

## Residuals (post-export)

All residuals are caller-supplied as abstract supplier hypotheses:

* `hZavyalov_per_E` — `refines_cover_per_E C S ∧ refines_contain C S ∧
  refines_span_top S`-existential for non-empty `rationalOpen`. Produced by
  `StandardCover.RationalCoveringData.refines_by_standard_cover_per_E` (Zavyalov-
  type Nullstellensatz refinement) modulo the residual
  `StandardCover.exists_nullstellensatz_refinement_of_rationalOpen_nonempty`
  obligation.
* `lane_A_supplier` — universal Laurent-overlap gluing on `refinedVCovers
  S'.elts f₀`, for any valid standard cover `S'`. Post-T-OV-1, dischargeable
  via the Laurent-cover closure route; the caller wires this in at the
  call site (e.g., via `LaurentOverlapConsumer.laurentCover_gluing_presheaf_via_primary`
  and its `hZavyalov_per_E` companion).
* `lane_B_supplier` — universal per-E separation (Wedhorn Cor 8.32
  / `productRestriction_injective_tate_via_prime_extension_closed`) on
  `per_E_local_covering`. Post-T-IDEAL-2, dischargeable via the ideal
  closedness route.
* `fC`, `hC_compat` — the caller's compatible section family on `C.covers`.

## Axiom-hygiene note

The direct per-E Part-2 wrappers in this file are axiom-clean relative to their
explicit supplier hypotheses: `#print axioms` for
`RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary` and the
`_laneA` variants, including the full-conjunction
`tateAcyclicity_end_to_end_via_primary_laneA`, reports only `propext`,
`Classical.choice`, and `Quot.sound`. The remaining non-clean acyclicity
theorem is the legacy final `ValuationSpectrum.tateAcyclicity` in
`LaurentRefinement.lean`, whose Part 1 still calls the retired single-map
`restrictionMapHom_injective` and whose Part 2 still has a raw assembly
`sorry`.

## References

* `Adic spaces/GeometricReduction.lean:5176` —
  `RationalCoveringData.tateAcyclicity_Part2_direct_per_E` (direct per-E core).
* `Adic spaces/GeometricReduction.lean:5361` —
  `RationalCoveringData.tateAcyclicity_Part2_via_hZavyalov_per_E_direct` (caller
  wrapper).
* `Adic spaces/Presheaf.lean:795` —
  `ValuationSpectrum.spa_point_nonOpen_of_rational_subset` (T001 root
  sorry blocking axiom-clean closure of every `restrictionMap`-consuming
  theorem).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- Equality-form cover separation from the current narrow Cor 8.32
zero-kernel theorem.

`productRestriction_injective_tate_via_prime_extension_closed` gives the
zero-kernel form used for Part 1. Most geometric assembly steps consume the
equivalent equality form: if two sections agree after restriction to every
cover piece, then they are equal. This theorem is just the additive shift
`a - b`, with no new mathematical content. -/
theorem RationalCoveringData.separation_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_closed_nonOpen : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ¬IsOpen (p : Set A) →
      @IsClosed _ C.base.topology
        ((Ideal.map (algebraMap A (Localization.Away C.base.s)) p :
            Ideal (Localization.Away C.base.s)) :
          Set (Localization.Away C.base.s))) :
    ∀ a b : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) a =
          restrictionMap C.base D (C.hsubset D hD) b) →
      a = b := by
  intro a b hagree
  have hzero : a - b = 0 := by
    apply productRestriction_injective_tate_via_prime_extension_closed
      P C hne hAplus_le_A₀ hcanonicalMap_cont h_closed_nonOpen
    intro D hD
    change restrictionMapHom C.base D (C.hsubset D hD) (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hagree D hD
  exact sub_eq_zero.mp hzero

/-- Universal nonempty-cover separation supplier from the current narrow
Corollary 8.32 route.

This packages `separation_via_prime_extension_closed` into the exact supplier
shape consumed by the final-assembly wrappers. The hypotheses are still the
known Lane-B residuals, but callers no longer have to rebuild the
`a - b` zero-kernel conversion for `C` and every per-E local covering. -/
theorem RationalCoveringData.nonempty_separation_supplier_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀ : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s))) :
    ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b := by
  intro C' hne a b hagree
  letI : IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s) :=
    hloc_noeth C'
  exact RationalCoveringData.separation_via_prime_extension_closed P C' hne
    (hAplus_le_A₀ C') (hcanonicalMap_cont C') (h_closed_nonOpen C') a b hagree

/-- Gluing over a rational covering whose base rational open is empty.

When the base open is empty, choose any cover piece `F` and restrict its
section back to the base. Compatibility then shows that its restriction to
every other cover piece is the prescribed section; the only geometry used is
that `rationalOpen C.base.T C.base.s = ∅` is contained in every cover piece. -/
theorem RationalCoveringData.gluing_of_rationalOpen_base_empty
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hbase_empty : rationalOpen C.base.T C.base.s = ∅)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂)) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  classical
  obtain ⟨F, hF⟩ := hne
  let F' : { E // E ∈ C.covers } := ⟨F, hF⟩
  have hbase_subset_F : rationalOpen C.base.T C.base.s ⊆ rationalOpen F.T F.s := by
    intro v hv
    rw [hbase_empty] at hv
    exact False.elim (Set.notMem_empty v hv)
  refine ⟨restrictionMap F C.base hbase_subset_F (fC F'), ?_⟩
  intro E
  have hcomp := restrictionMap_comp F C.base E.1 hbase_subset_F (C.hsubset E.1 E.2)
  calc
    restrictionMap C.base E.1 (C.hsubset E.1 E.2)
        (restrictionMap F C.base hbase_subset_F (fC F')) =
        restrictionMap F E.1 ((C.hsubset E.1 E.2).trans hbase_subset_F) (fC F') :=
          congr_fun hcomp (fC F')
    _ = restrictionMap E.1 E.1 (le_refl _) (fC E) :=
          hC_compat F' E E.1 ((C.hsubset E.1 E.2).trans hbase_subset_F) (le_refl _)
    _ = fC E := by
          rw [restrictionMap_id]
          rfl

/-- An empty cover piece is forced by compatibility once the candidate global
section matches one cover piece.

This is the local tool needed to avoid asking Cor 8.32-style separation for
empty per-E local coverings: if `E` has empty rational open, then `E` is an
overlap of any other cover piece with itself, so compatibility determines the
section on `E`. -/
theorem RationalCoveringData.empty_piece_eq_of_matches_piece
    (C : RationalCoveringData A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (x : presheafValue C.base)
    (F : { E // E ∈ C.covers })
    (hF_match : restrictionMap C.base F.1 (C.hsubset F.1 F.2) x = fC F)
    (E : { E // E ∈ C.covers })
    (hE_empty : rationalOpen E.1.T E.1.s = ∅) :
    restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  have hE_subset_F : rationalOpen E.1.T E.1.s ⊆ rationalOpen F.1.T F.1.s := by
    intro v hv
    rw [hE_empty] at hv
    exact False.elim (Set.notMem_empty v hv)
  have hcomp := restrictionMap_comp C.base F.1 E.1 (C.hsubset F.1 F.2) hE_subset_F
  calc
    restrictionMap C.base E.1 (C.hsubset E.1 E.2) x =
        restrictionMap C.base E.1 (hE_subset_F.trans (C.hsubset F.1 F.2)) x := by
          rw [show C.hsubset E.1 E.2 = hE_subset_F.trans (C.hsubset F.1 F.2) from
            Subsingleton.elim _ _]
    _ = restrictionMap F.1 E.1 hE_subset_F
          (restrictionMap C.base F.1 (C.hsubset F.1 F.2) x) :=
          (congr_fun hcomp x).symm
    _ = restrictionMap F.1 E.1 hE_subset_F (fC F) := by
          rw [hF_match]
    _ = restrictionMap E.1 E.1 (le_refl _) (fC E) :=
          hC_compat F E E.1 hE_subset_F (le_refl _)
    _ = fC E := by
          rw [restrictionMap_id]
          rfl

/-- Direct per-E Part 2 gluing, but only requiring local separation on
nonempty original cover pieces.

This is a stricter caller boundary than
`tateAcyclicity_Part2_direct_per_E`: Cor 8.32-style separation is only needed
where it is geometrically meaningful, namely on nonempty cover pieces. If the
base is empty, `gluing_of_rationalOpen_base_empty` closes the whole case. If
the base is nonempty, first prove the candidate section matches one nonempty
piece and every other nonempty piece by local separation; empty pieces are then
forced by compatibility using `empty_piece_eq_of_matches_piece`. -/
theorem RationalCoveringData.tateAcyclicity_Part2_direct_per_E_allow_empty
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) (S : Finset A) (f₀ : A)
    (hS_per_E : refines_cover_per_E C S)
    (hS_contain : refines_contain C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue_refined : ∀
      (fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S f₀ D.1 D.2) x = fV D)
    (hE_sep_direct : ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S f₀ E hS_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  classical
  by_cases hbase_empty : rationalOpen C.base.T C.base.s = ∅
  · exact C.gluing_of_rationalOpen_base_empty hne hbase_empty fC hC_compat
  · have hbase_nonempty : (rationalOpen C.base.T C.base.s).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hbase_empty
    obtain ⟨v, hv_base⟩ := hbase_nonempty
    obtain ⟨F, hF, hvF⟩ := C.hcover v hv_base
    let F' : { E // E ∈ C.covers } := ⟨F, hF⟩
    have hF_nonempty : (rationalOpen F'.1.T F'.1.s).Nonempty := ⟨v, hvF⟩
    have D_f_exists : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        ∃ f, f ∈ S ∧
          (laurentPlusDatum (C.plusDatum f) f₀ = D.1 ∨
           laurentMinusDatum (C.plusDatum f) f₀ = D.1) := fun D ↦ by
      rcases (C.mem_refinedVCovers S f₀).mp D.2 with ⟨f, hf, hf_eq⟩ | ⟨f, hf, hf_eq⟩
      · exact ⟨f, hf, Or.inl hf_eq⟩
      · exact ⟨f, hf, Or.inr hf_eq⟩
    let D_f : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, A := fun D ↦
      Classical.choose (D_f_exists D)
    have D_f_mem_S : ∀ D, D_f D ∈ S :=
      fun D ↦ (Classical.choose_spec (D_f_exists D)).1
    have D_f_eq : ∀ D, laurentPlusDatum (C.plusDatum (D_f D)) f₀ = D.1 ∨
        laurentMinusDatum (C.plusDatum (D_f D)) f₀ = D.1 :=
      fun D ↦ (Classical.choose_spec (D_f_exists D)).2
    have D_sub_plusPiece : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        rationalOpen D.1.T D.1.s ⊆
          rationalOpen (C.plusDatum (D_f D)).T (C.plusDatum (D_f D)).s := fun D ↦ by
      rcases D_f_eq D with heq | heq
      · rw [← heq]; exact laurentPlus_subset (C.plusDatum (D_f D)) f₀
      · rw [← heq]; exact laurentMinus_subset (C.plusDatum (D_f D)) f₀
    have D_sub_plusPiece_insert : ∀ D : { D // D ∈ C.refinedVCovers S f₀ },
        rationalOpen D.1.T D.1.s ⊆
          rationalOpen (insert (D_f D) C.base.T) C.base.s := fun D ↦
      (D_sub_plusPiece D).trans (C.rationalOpen_plusDatum_eq_insert (D_f D)).le
    let D_E : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, RationalLocData A := fun D ↦
      Classical.choose (hS_contain (D_f D) (D_f_mem_S D))
    have D_E_mem : ∀ D, D_E D ∈ C.covers := fun D ↦
      (Classical.choose_spec (hS_contain (D_f D) (D_f_mem_S D))).1
    have D_E_sub : ∀ D,
        rationalOpen (insert (D_f D) C.base.T) C.base.s ⊆
          rationalOpen (D_E D).T (D_E D).s := fun D ↦
      (Classical.choose_spec (hS_contain (D_f D) (D_f_mem_S D))).2
    have D_sub_DE : ∀ D,
        rationalOpen D.1.T D.1.s ⊆ rationalOpen (D_E D).T (D_E D).s :=
      fun D ↦ (D_sub_plusPiece_insert D).trans (D_E_sub D)
    let fV : ∀ D : { D // D ∈ C.refinedVCovers S f₀ }, presheafValue D.1 := fun D ↦
      restrictionMap (D_E D) D.1 (D_sub_DE D) (fC ⟨D_E D, D_E_mem D⟩)
    have fV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂) := by
      intro D₁ D₂ D₃ h₃₁ h₃₂
      have hcomp1 := restrictionMap_comp (D_E D₁) D₁.1 D₃ (D_sub_DE D₁) h₃₁
      have hcomp2 := restrictionMap_comp (D_E D₂) D₂.1 D₃ (D_sub_DE D₂) h₃₂
      have step1 : restrictionMap D₁.1 D₃ h₃₁ (fV D₁) =
          restrictionMap (D_E D₁) D₃ (h₃₁.trans (D_sub_DE D₁))
            (fC ⟨D_E D₁, D_E_mem D₁⟩) :=
        congr_fun hcomp1 _
      have step2 : restrictionMap D₂.1 D₃ h₃₂ (fV D₂) =
          restrictionMap (D_E D₂) D₃ (h₃₂.trans (D_sub_DE D₂))
            (fC ⟨D_E D₂, D_E_mem D₂⟩) :=
        congr_fun hcomp2 _
      rw [step1, step2]
      exact hC_compat ⟨D_E D₁, D_E_mem D₁⟩ ⟨D_E D₂, D_E_mem D₂⟩ D₃ _ _
    obtain ⟨x, hx⟩ := hV_glue_refined fV fV_compat
    have match_of_nonempty : ∀ (E : { E // E ∈ C.covers }),
        (rationalOpen E.1.T E.1.s).Nonempty →
        restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
      intro E hE_nonempty
      apply hE_sep_direct E hE_nonempty
      intro D hD
      have D_in_refined : D ∈ C.refinedVCovers S f₀ := by
        rw [(C.mem_per_E_local_covering_covers S f₀ E hS_per_E D)] at hD
        obtain ⟨f, hf, _h_in_E, h_eq⟩ := hD
        rw [C.mem_refinedVCovers S f₀]
        rcases h_eq with heq | heq
        · exact Or.inl ⟨f, hf, heq⟩
        · exact Or.inr ⟨f, hf, heq⟩
      have hcomp_LHS := restrictionMap_comp C.base E.1 D (C.hsubset E.1 E.2)
        ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD)
      have hLHS_step : restrictionMap E.1 D
            ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD)
            (restrictionMap C.base E.1 (C.hsubset E.1 E.2) x) =
          restrictionMap C.base D
            (((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD).trans
              (C.hsubset E.1 E.2)) x :=
        congr_fun hcomp_LHS x
      rw [hLHS_step]
      have hxD := hx ⟨D, D_in_refined⟩
      rw [show ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD).trans
            (C.hsubset E.1 E.2) =
          C.refinedVCovers_subset_base S f₀ D D_in_refined from
        Subsingleton.elim _ _]
      rw [hxD]
      change restrictionMap (D_E ⟨D, D_in_refined⟩) D (D_sub_DE ⟨D, D_in_refined⟩)
          (fC ⟨D_E ⟨D, D_in_refined⟩, D_E_mem ⟨D, D_in_refined⟩⟩) =
        restrictionMap E.1 D
          ((C.per_E_local_covering S f₀ E hS_per_E).hsubset D hD) (fC E)
      exact hC_compat ⟨D_E ⟨D, D_in_refined⟩, D_E_mem ⟨D, D_in_refined⟩⟩ E D _ _
    refine ⟨x, fun E ↦ ?_⟩
    by_cases hE_nonempty : (rationalOpen E.1.T E.1.s).Nonempty
    · exact match_of_nonempty E hE_nonempty
    · exact C.empty_piece_eq_of_matches_piece fC hC_compat x F'
        (match_of_nonempty F' hF_nonempty) E
        (Set.not_nonempty_iff_eq_empty.mp hE_nonempty)

/-- **Final caller-ready Part-2 theorem** (direct per-E route with abstract
Lane A/B suppliers).

Wraps `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`
(`GeometricReduction.lean:5361`): extracts the standard cover `S` from the
`hZavyalov_per_E` existential via
`RationalCoveringData.refines_by_standard_cover_per_E`, then applies
`tateAcyclicity_Part2_direct_per_E` with the chosen `S` plus the lane
outputs.

**Lane A / Lane B as abstract suppliers.** Both `lane_A_supplier` and
`lane_B_supplier` are universally quantified over `StandardCover A`,
matching the mathematical shape: the Laurent-overlap gluing and per-E
separation statements hold uniformly across all standard covers. This
decouples the lane content from the classically chosen `S` inside the
`hZavyalov_per_E` existential.

**Residuals (caller-supplied):**
* `hZavyalov_per_E` — refinement existential for non-empty `rationalOpen`.
* `lane_A_supplier` — universal Laurent-overlap gluing on refined V-covers.
* `lane_B_supplier` — universal per-E separation on per-E local coverings.
* `fC`, `hC_compat` — compatible section family on `C.covers`.

See the module docblock for the residual map and the T001 axiom-hygiene
caveat. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_via_hZavyalov_per_E_direct hne hZavyalov_per_E f₀
    fC hC_compat lane_A_supplier lane_B_supplier

/-- Caller-ready Part-2 theorem using the empty-piece-tolerant direct per-E
route.

Compared to `tateAcyclicity_Part2_end_to_end_via_primary`, this wrapper only
asks the Lane B supplier for original cover pieces with nonempty rational open.
The empty-base and empty-piece branches are handled structurally by
`gluing_of_rationalOpen_base_empty` and `empty_piece_eq_of_matches_piece`. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  obtain ⟨S, hS_per_E, hS_contain⟩ :=
    C.refines_by_standard_cover_per_E hne hZavyalov_per_E
  exact C.tateAcyclicity_Part2_direct_per_E_allow_empty hne S.elts f₀
    hS_per_E hS_contain fC hC_compat
    (lane_A_supplier S hS_per_E hS_contain)
    (lane_B_supplier S hS_per_E hS_contain)

section ConcreteLaneA

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
  [DecidableEq A]
variable (C : RationalCoveringData A) (f₀ : A)
variable [IsNoetherianRing C.base.P.A₀]
variable [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
variable [LaurentNormalized C.base]

/-- Concrete data needed to discharge the abstract Lane A supplier in the
direct per-E Part 2 wrapper via Primary's overlap route. -/
structure PrimaryLaneAInputs where
  hNoeth_B : IsNoetherianRing (presheafValue C.base)
  hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    HasLocLiftPowerBounded (presheafValue C.base)
  hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
    IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀)
  hA_complete_B : @CompleteSpace (presheafValue C.base)
    (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base))
  hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    IsNoetherianRing ↥(TateAlgebra.pairSubring
      (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition)
  hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
    letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue C.base) :=
      presheafValue_pairOfDefinition_concrete C.base.P C.base
    letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
    @Continuous _ _
      (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
      (inferInstance : TopologicalSpace (presheafValue
        (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
      (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀))
  hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    let D : RationalLocData (presheafValue C.base) :=
      iteratedMinusDatum_B C.base.P C.base f₀
    ∀ hb : TopologicalRing.IsPowerBounded (invS D),
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology D.s)
        (inferInstance : TopologicalSpace (presheafValue D))
        (tateQuotientToPresheafHom D hb)
  τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
    (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
      TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀))
  h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
    (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
        (presheafValue C.base) (C.base.canonicalMap f₀))
        (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
            (laurentOverlapDatum C.base f₀)
            (laurentOverlap_subset_plus C.base f₀) uplus)) =
      LaurentCover.posLift (C.base.canonicalMap f₀)
        (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
          hA_complete_B hnoeth_B hcont_forward_B uplus)
  h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
    (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
        (presheafValue C.base) (C.base.canonicalMap f₀))
        (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
            (laurentOverlapDatum C.base f₀)
            (laurentOverlap_subset_minus C.base f₀) uminus)) =
      LaurentCover.negLift (C.base.canonicalMap f₀)
        (laurentMinusBridge C.base.P C.base f₀ hnoeth_B hcont_eval_B uminus)
  plus_section_refined : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D }
  minus_section_refined : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D }
  hOverlap : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus

/-- Constructor for `PrimaryLaneAInputs` that internalizes the canonical
completion and minus-evaluation continuity inputs for `presheafValue C.base`.

The remaining fields are the genuine Lane A data: noetherian/local-lift
instances, plus-side continuity, the bivariate overlap identification, and the
refined half-section/overlap compatibility suppliers. -/
def PrimaryLaneAInputs.of_canonical_completion
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing C.base.P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete C.base.P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
          (inferInstance : TopologicalSpace (presheafValue
            (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
          (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
      (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
        (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
          TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
          (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
              (presheafValue C.base) (C.base.canonicalMap f₀))
              (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
                  (laurentOverlapDatum C.base f₀)
                  (laurentOverlap_subset_plus C.base f₀) uplus)) =
            LaurentCover.posLift (C.base.canonicalMap f₀)
              (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
                (RationalCoveringData.canonical_complete_presheafValue C)
                hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
          (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
            LaurentCover.negLift (C.base.canonicalMap f₀)
              (laurentMinusBridge C.base.P C.base f₀ hnoeth_B
                (RationalCoveringData.canonical_hcont_eval C f₀)
                uminus))
    (plus_section_refined : ∀ (S' : StandardCover A)
        (_hS'_per_E : refines_cover_per_E C S'.elts)
        (_hS'_contain : refines_contain C S'.elts),
        ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
        (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
        { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
          ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
            (hD_plus : rationalOpen D.1.T D.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T
                           (laurentPlusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D })
    (minus_section_refined : ∀ (S' : StandardCover A)
        (_hS'_per_E : refines_cover_per_E C S'.elts)
        (_hS'_contain : refines_contain C S'.elts),
        ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
        (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
        { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
          ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
            (hD_minus : rationalOpen D.1.T D.1.s ⊆
              rationalOpen (laurentMinusDatum C.base f₀).T
                           (laurentMinusDatum C.base f₀).s),
            restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hOverlap : ∀ (S' : StandardCover A)
        (_hS'_per_E : refines_cover_per_E C S'.elts)
        (_hS'_contain : refines_contain C S'.elts),
        ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1)
        (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
          restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
        (u_plus : presheafValue (laurentPlusDatum C.base f₀))
        (u_minus : presheafValue (laurentMinusDatum C.base f₀))
        (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
        (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
        ∀ (D₃ : RationalLocData A)
          (h₃p : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
          (h₃m : rationalOpen D₃.T D₃.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
            restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus) :
    PrimaryLaneAInputs C f₀ := by
    refine
      { hNoeth_B := hNoeth_B
        hLocLift_B := hLocLift_B
        hA₀Noeth_B := hA₀Noeth_B
        hA_complete_B := by
          exact RationalCoveringData.canonical_complete_presheafValue C
        hnoeth_B := hnoeth_B
        hcont_forward_B := hcont_forward_B
        hcont_eval_B := RationalCoveringData.canonical_hcont_eval C f₀
        τ_preBiv := τ_preBiv
        h_plus_compat := h_plus_compat
        h_minus_compat := h_minus_compat
        plus_section_refined := plus_section_refined
        minus_section_refined := minus_section_refined
        hOverlap := hOverlap }

/-- Canonical Lane A data package.

This is the caller-facing version of `PrimaryLaneAInputs` after internalizing
the two canonical inputs already available for `B = presheafValue C.base`:
completion of `B` and continuity of the minus-side Tate quotient map. The
remaining fields are the actual open Lane A data. -/
structure PrimaryLaneAInputsCanonical where
  hNoeth_B : IsNoetherianRing (presheafValue C.base)
  hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    HasLocLiftPowerBounded (presheafValue C.base)
  hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
    IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete C.base.P C.base).A₀)
  hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    IsNoetherianRing ↥(TateAlgebra.pairSubring
      (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition)
  hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing C.base.P C.base
    letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
    letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue C.base) :=
      presheafValue_pairOfDefinition_concrete C.base.P C.base
    letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
    @Continuous _ _
      (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀))
  τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
    (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
      TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀))
  h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
    (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
        (presheafValue C.base) (C.base.canonicalMap f₀))
        (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
            (laurentOverlapDatum C.base f₀)
            (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge C.base.P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B
            (RationalCoveringData.canonical_complete_presheafValue C)
            hnoeth_B hcont_forward_B uplus)
  h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
    (ValuationSpectrum.bivariateOverlap_equiv_B₁₂gen
        (presheafValue C.base) (C.base.canonicalMap f₀))
        (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
            (laurentOverlapDatum C.base f₀)
            (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge C.base.P C.base f₀ hnoeth_B
            (RationalCoveringData.canonical_hcont_eval C f₀)
            uminus)
  plus_section_refined : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_plus : presheafValue (laurentPlusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D }
  minus_section_refined : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D }
  hOverlap : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂))
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (_huplus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_plus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T
                       (laurentPlusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
      (_huminus : ∀ (D : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (hD_minus : rationalOpen D.1.T D.1.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T
                       (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p u_plus =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m u_minus

/-- Convert the canonical Lane A package to the older full package by filling
the completion and minus-continuity fields canonically. -/
def PrimaryLaneAInputsCanonical.toPrimary
    (h : PrimaryLaneAInputsCanonical C f₀) : PrimaryLaneAInputs C f₀ :=
  PrimaryLaneAInputs.of_canonical_completion C f₀ h.hNoeth_B h.hLocLift_B
    h.hA₀Noeth_B h.hnoeth_B h.hcont_forward_B h.τ_preBiv h.h_plus_compat
    h.h_minus_compat h.plus_section_refined h.minus_section_refined h.hOverlap

/-- Simple-Laurent separation supplied from canonical Lane-A bridge data and
an explicit Krull-intersection input.

This is the separation-side counterpart of the canonical Lane-A gluing
supplier: the plus/minus bridge data are read from
`PrimaryLaneAInputsCanonical`, while completion and minus-continuity are filled
by the canonical presheaf-value helpers. The only remaining mathematical input
is the exact Hübner/Krull condition on `D₀.canonicalMap f₀`. -/
theorem RationalCoveringData.simpleLaurent_separation_via_primary_canonical_of_iInf
    (hInf : (⨅ n : ℕ,
      Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ^ n) = ⊥)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀)
    (x : presheafValue C.base)
    (hplus0 : restrictionMap C.base (laurentPlusDatum C.base f₀)
      (laurentPlus_subset C.base f₀) x = 0)
    (hminus0 : restrictionMap C.base (laurentMinusDatum C.base f₀)
      (laurentMinus_subset C.base f₀) x = 0) :
    x = 0 :=
  laurentCover_separation_presheaf_viaBridges_of_iInf_pow_eq_bot
    C.base.P C.base f₀ hInf
    hLaneA.hNoeth_B hLaneA.hLocLift_B hLaneA.hA₀Noeth_B
    (RationalCoveringData.canonical_complete_presheafValue C)
    hLaneA.hnoeth_B hLaneA.hcont_forward_B
    (RationalCoveringData.canonical_hcont_eval C f₀)
    (laurentPlus_subset C.base f₀) (laurentMinus_subset C.base f₀)
    x hplus0 hminus0

/-- Jacobson-radical specialization of
`simpleLaurent_separation_via_primary_canonical_of_iInf`. -/
theorem RationalCoveringData.simpleLaurent_separation_via_primary_canonical_of_jacobian
    (hf_jac : Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ≤
      Ideal.jacobson (⊥ : Ideal (presheafValue C.base)))
    (hLaneA : PrimaryLaneAInputsCanonical C f₀)
    (x : presheafValue C.base)
    (hplus0 : restrictionMap C.base (laurentPlusDatum C.base f₀)
      (laurentPlus_subset C.base f₀) x = 0)
    (hminus0 : restrictionMap C.base (laurentMinusDatum C.base f₀)
      (laurentMinus_subset C.base f₀) x = 0) :
    x = 0 := by
  letI : IsNoetherianRing (presheafValue C.base) := hLaneA.hNoeth_B
  exact C.simpleLaurent_separation_via_primary_canonical_of_iInf f₀
    (LaurentCover.span_singleton_iInf_pow_eq_bot_of_le_jacobson
      (C.base.canonicalMap f₀) hf_jac)
    hLaneA x hplus0 hminus0

/-- Domain-style specialization of
`simpleLaurent_separation_via_primary_canonical_of_iInf`.

Under the local assumption `[IsDomain (presheafValue C.base)]` together with
`¬IsUnit (C.base.canonicalMap f₀)`, Krull's intersection theorem for domains
(`Ideal.iInf_pow_eq_bot_of_isDomain`) supplies the `hInf` hypothesis
automatically. This wrapper is intentionally optional: `IsDomain` and the
non-unit witness are kept local and never propagate to final acyclicity. -/
theorem RationalCoveringData.simpleLaurent_separation_via_primary_canonical_of_isDomain
    [IsDomain (presheafValue C.base)]
    (hf_nonunit : ¬IsUnit (C.base.canonicalMap f₀))
    (hLaneA : PrimaryLaneAInputsCanonical C f₀)
    (x : presheafValue C.base)
    (hplus0 : restrictionMap C.base (laurentPlusDatum C.base f₀)
      (laurentPlus_subset C.base f₀) x = 0)
    (hminus0 : restrictionMap C.base (laurentMinusDatum C.base f₀)
      (laurentMinus_subset C.base f₀) x = 0) :
    x = 0 := by
  letI : IsNoetherianRing (presheafValue C.base) := hLaneA.hNoeth_B
  have hf_ne_top :
      Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  exact C.simpleLaurent_separation_via_primary_canonical_of_iInf f₀
    (Ideal.iInf_pow_eq_bot_of_isDomain _ hf_ne_top)
    hLaneA x hplus0 hminus0

/-- The two-piece Laurent covering has separation from canonical Lane-A bridge
data plus the explicit Hübner/Krull `iInf` input. -/
theorem RationalCoveringData.laurentCovering_hasSeparation_via_primary_canonical_of_iInf
    (hInf : (⨅ n : ℕ,
      Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ^ n) = ⊥)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (laurentCovering C.base f₀).HasSeparation := by
  classical
  intro x y hxy
  have hplus_eq : restrictionMap C.base (laurentPlusDatum C.base f₀)
        (laurentPlus_subset C.base f₀) x =
      restrictionMap C.base (laurentPlusDatum C.base f₀)
        (laurentPlus_subset C.base f₀) y := by
    simpa [laurentCovering] using
      hxy (laurentPlusDatum C.base f₀) (Finset.mem_insert_self _ _)
  have hminus_eq : restrictionMap C.base (laurentMinusDatum C.base f₀)
        (laurentMinus_subset C.base f₀) x =
      restrictionMap C.base (laurentMinusDatum C.base f₀)
        (laurentMinus_subset C.base f₀) y := by
    simpa [laurentCovering] using
      hxy (laurentMinusDatum C.base f₀)
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  have hzero : x - y = 0 := by
    apply C.simpleLaurent_separation_via_primary_canonical_of_iInf f₀ hInf hLaneA
    · change restrictionMapHom C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) (x - y) = 0
      calc
        restrictionMapHom C.base (laurentPlusDatum C.base f₀)
            (laurentPlus_subset C.base f₀) (x - y) =
            restrictionMap C.base (laurentPlusDatum C.base f₀)
              (laurentPlus_subset C.base f₀) x -
            restrictionMap C.base (laurentPlusDatum C.base f₀)
              (laurentPlus_subset C.base f₀) y := by
              exact map_sub (restrictionMapHom C.base (laurentPlusDatum C.base f₀)
                (laurentPlus_subset C.base f₀)) x y
        _ = 0 := sub_eq_zero.mpr hplus_eq
    · change restrictionMapHom C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) (x - y) = 0
      calc
        restrictionMapHom C.base (laurentMinusDatum C.base f₀)
            (laurentMinus_subset C.base f₀) (x - y) =
            restrictionMap C.base (laurentMinusDatum C.base f₀)
              (laurentMinus_subset C.base f₀) x -
            restrictionMap C.base (laurentMinusDatum C.base f₀)
              (laurentMinus_subset C.base f₀) y := by
              exact map_sub (restrictionMapHom C.base (laurentMinusDatum C.base f₀)
                (laurentMinus_subset C.base f₀)) x y
        _ = 0 := sub_eq_zero.mpr hminus_eq
  exact sub_eq_zero.mp hzero

/-- Jacobson-radical specialization of
`laurentCovering_hasSeparation_via_primary_canonical_of_iInf`. -/
theorem RationalCoveringData.laurentCovering_hasSeparation_via_primary_canonical_of_jacobian
    (hf_jac : Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ≤
      Ideal.jacobson (⊥ : Ideal (presheafValue C.base)))
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (laurentCovering C.base f₀).HasSeparation := by
  letI : IsNoetherianRing (presheafValue C.base) := hLaneA.hNoeth_B
  exact C.laurentCovering_hasSeparation_via_primary_canonical_of_iInf f₀
    (LaurentCover.span_singleton_iInf_pow_eq_bot_of_le_jacobson
      (C.base.canonicalMap f₀) hf_jac)
    hLaneA

/-- Domain-style specialization of
`laurentCovering_hasSeparation_via_primary_canonical_of_iInf`.

Under `[IsDomain (presheafValue C.base)]` together with
`¬IsUnit (C.base.canonicalMap f₀)`, Krull intersection
(`Ideal.iInf_pow_eq_bot_of_isDomain`) discharges the `hInf` hypothesis. -/
theorem RationalCoveringData.laurentCovering_hasSeparation_via_primary_canonical_of_isDomain
    [IsDomain (presheafValue C.base)]
    (hf_nonunit : ¬IsUnit (C.base.canonicalMap f₀))
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (laurentCovering C.base f₀).HasSeparation := by
  letI : IsNoetherianRing (presheafValue C.base) := hLaneA.hNoeth_B
  have hf_ne_top :
      Ideal.span ({C.base.canonicalMap f₀} : Set (presheafValue C.base)) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  exact C.laurentCovering_hasSeparation_via_primary_canonical_of_iInf f₀
    (Ideal.iInf_pow_eq_bot_of_isDomain _ hf_ne_top)
    hLaneA

/-- Variant of the direct per-E wrapper with Lane A internalized via
`lane_A_supplier_via_primary`. This leaves only the per-E refinement
existence and the Lane B supplier abstract at the Part 2 boundary. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA
    (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.tateAcyclicity_Part2_via_hZavyalov_per_E_direct hne hZavyalov_per_E f₀
    fC hC_compat
    (fun S' hS'_per_E hS'_contain ↦
      RationalCoveringData.lane_A_supplier_via_primary C f₀ hLaneA.hNoeth_B hLaneA.hLocLift_B
        hLaneA.hA₀Noeth_B hLaneA.hA_complete_B hLaneA.hnoeth_B hLaneA.hcont_forward_B
        hLaneA.hcont_eval_B hLaneA.τ_preBiv hLaneA.h_plus_compat hLaneA.h_minus_compat
        S' hS'_per_E hS'_contain
        (hLaneA.plus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.minus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.hOverlap S' hS'_per_E hS'_contain))
    lane_B_supplier

/-- Empty-piece-tolerant variant of
`tateAcyclicity_Part2_end_to_end_via_primary_laneA`.

Lane A is internalized through `PrimaryLaneAInputs`; the remaining separation
supplier is only requested for original cover pieces whose rational open is
nonempty. Empty base and empty original pieces are handled structurally by
`tateAcyclicity_Part2_end_to_end_via_primary_allow_empty`. -/
theorem RationalCoveringData.part2_via_primary_laneA_allow_empty
    (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.tateAcyclicity_Part2_end_to_end_via_primary_allow_empty
    (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    (fun S' hS'_per_E hS'_contain ↦
      RationalCoveringData.lane_A_supplier_via_primary C f₀ hLaneA.hNoeth_B hLaneA.hLocLift_B
        hLaneA.hA₀Noeth_B hLaneA.hA_complete_B hLaneA.hnoeth_B hLaneA.hcont_forward_B
        hLaneA.hcont_eval_B hLaneA.τ_preBiv hLaneA.h_plus_compat hLaneA.h_minus_compat
        S' hS'_per_E hS'_contain
        (hLaneA.plus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.minus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.hOverlap S' hS'_per_E hS'_contain))
    lane_B_supplier

/-- Caller-facing variant of
`tateAcyclicity_Part2_end_to_end_via_primary_laneA` where the standard-cover
refinement witness is supplied by explicit per-cover-piece data
`mk_S_D` rather than as an abstract `hZavyalov_per_E` existential.

This packages `StandardCover.hZavyalov_per_E_of_per_D_construction` into the
direct per-E Part 2 closure, keeping Lane A internalized via
`PrimaryLaneAInputs` and leaving only the Lane B supplier abstract. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA_of_per_D
    (hne : C.covers.Nonempty)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  classical
  exact
    ValuationSpectrum.RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA
      (A := A) (C := C) (f₀ := f₀) hne
      (hZavyalov_per_E_of_per_D_construction
        (A := A) (C := C) mk_S_D h_in_D h_cover_D h_span)
      fC hC_compat lane_B_supplier hLaneA

/-- Caller-facing variant of
`tateAcyclicity_Part2_end_to_end_via_primary_laneA` for the standard-shape
case where each cover piece `D` is already presented as
`R(insert (f_D D) C.base.T, C.base.s)`.

This packages `StandardCover.exists_refines_cover_per_E_of_standardShape` into
the direct per-E Part 2 closure. Compared to
`tateAcyclicity_Part2_end_to_end_via_primary_laneA_of_per_D`, the caller no
longer supplies an arbitrary per-D finset family `mk_S_D`; only the
single-generator standard-shape witness `f_D` and the global span-top witness
remain external. -/
theorem RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA_of_standardShape
    (hne : C.covers.Nonempty)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  classical
  exact
    ValuationSpectrum.RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA
      (A := A) (C := C) (f₀ := f₀) hne
      (fun _ ↦
        exists_refines_cover_per_E_of_standardShape
          (A := A) (C := C) f_D h_shape h_span)
      fC hC_compat lane_B_supplier hLaneA

/-- Per-D refinement variant of `part2_via_primary_laneA_allow_empty`.

This is the same per-D construction entry point as
`tateAcyclicity_Part2_end_to_end_via_primary_laneA_of_per_D`, but its
remaining separation supplier is only required on nonempty original cover
pieces. -/
theorem RationalCoveringData.part2_via_primary_laneA_per_D_allow_empty
    (hne : C.covers.Nonempty)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.part2_via_primary_laneA_allow_empty (f₀ := f₀) hne
    (hZavyalov_per_E_of_per_D_construction
      (A := A) (C := C) mk_S_D h_in_D h_cover_D h_span)
    fC hC_compat lane_B_supplier hLaneA

/-- Standard-shape refinement variant of `part2_via_primary_laneA_allow_empty`.

The only remaining geometric input is the span-top witness for the standard
generators; empty original cover pieces do not create separation obligations. -/
theorem RationalCoveringData.part2_via_primary_laneA_standardShape_allow_empty
    (hne : C.covers.Nonempty)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.part2_via_primary_laneA_allow_empty (f₀ := f₀) hne
    (fun _ ↦
      exists_refines_cover_per_E_of_standardShape
        (A := A) (C := C) f_D h_shape h_span)
    fC hC_compat lane_B_supplier hLaneA

/-- Canonical-Lane-A variant of `part2_via_primary_laneA_allow_empty`. -/
theorem RationalCoveringData.part2_via_primary_canonical_allow_empty
    (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.tateAcyclicity_Part2_end_to_end_via_primary_allow_empty
    (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    (fun S' hS'_per_E hS'_contain ↦
      RationalCoveringData.lane_A_supplier_via_primary_canonical C f₀ hLaneA.hNoeth_B
        hLaneA.hLocLift_B hLaneA.hA₀Noeth_B hLaneA.hnoeth_B
        hLaneA.hcont_forward_B hLaneA.τ_preBiv hLaneA.h_plus_compat
        hLaneA.h_minus_compat S' hS'_per_E hS'_contain
        (hLaneA.plus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.minus_section_refined S' hS'_per_E hS'_contain)
        (hLaneA.hOverlap S' hS'_per_E hS'_contain))
    lane_B_supplier

/-- Canonical-Lane-A per-D refinement variant of Part 2. -/
theorem RationalCoveringData.part2_via_primary_canonical_per_D_allow_empty
    (hne : C.covers.Nonempty)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.part2_via_primary_canonical_allow_empty (f₀ := f₀) hne
    (hZavyalov_per_E_of_per_D_construction
      (A := A) (C := C) mk_S_D h_in_D h_cover_D h_span)
    fC hC_compat lane_B_supplier hLaneA

/-- Canonical-Lane-A standard-shape variant of Part 2. -/
theorem RationalCoveringData.part2_via_primary_canonical_standardShape_allow_empty
    (hne : C.covers.Nonempty)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  exact C.part2_via_primary_canonical_allow_empty (f₀ := f₀) hne
    (fun _ ↦
      exists_refines_cover_per_E_of_standardShape
        (A := A) (C := C) f_D h_shape h_span)
    fC hC_compat lane_B_supplier hLaneA

/-- Full Tate-acyclicity conjunction from a Part 1 supplier plus the
Lane-A-internalized direct per-E Part 2 wrapper.

This is the downstream assembly boundary with the same conclusion shape as
`ValuationSpectrum.tateAcyclicity`, but it deliberately keeps the still-open
mathematical suppliers explicit:

* `part1_supplier` is the cover-level separation theorem.
* `hZavyalov_per_E` is the standard/Laurent refinement existence theorem.
* `lane_B_supplier` is the per-E separation used inside the direct per-E
  gluing assembly.
* `hLaneA` packages the now-built overlap/Laurent gluing input.

It does not change the legacy final theorem's hypotheses; it records the
exact remaining proof boundary in an axiom-clean form. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_laneA
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (part1_supplier : ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨part1_supplier, ?_⟩
  intro f hcompat
  exact
    C.tateAcyclicity_Part2_end_to_end_via_primary_laneA
      (f₀ := f₀) hne hZavyalov_per_E f hcompat lane_B_supplier hLaneA

/-- Full Tate-acyclicity conjunction from a **universal cover-level
separation supplier** plus the Lane-A-internalized direct per-E Part 2 wrapper.

Compared to `tateAcyclicity_end_to_end_via_primary_laneA`, this theorem no
longer asks separately for `part1_supplier` and `lane_B_supplier`.
Instead, it takes one uniform separation theorem for arbitrary rational
coverings and applies it:

* to `C`, yielding the final Part 1 zero-kernel clause;
* to each `C.per_E_local_covering ...`, yielding the per-E separation needed
  by the direct per-E gluing assembly.

This is the intended final assembly shape once separation is available as
augmented Čech exactness for all rational covers. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_laneA_of_universal_separation
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A,
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine C.tateAcyclicity_end_to_end_via_primary_laneA (f₀ := f₀) P hne ?_
    hZavyalov_per_E ?_ hLaneA
  · intro x hx
    exact separation_supplier C x 0 fun D hD ↦ by
      rw [hx D hD]
      exact (map_zero (restrictionMapHom C.base D (C.hsubset D hD))).symm
  · intro S' hS'_per_E _hS'_contain E a b hlocal
    exact separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
      a b hlocal

/-- Full Tate-acyclicity conjunction from a separation supplier for
**nonempty** rational coverings.

This is the Cor 8.32-friendly variant of
`tateAcyclicity_end_to_end_via_primary_laneA_of_universal_separation`:
Cor 8.32 cover-level injectivity requires a nonempty cover. The final cover
`C` has `hne`; for the per-E local coverings, the caller supplies the exact
nonemptiness proof. This keeps the empty-cover issue explicit instead of
forcing a false/overstrong universal separation hypothesis. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_laneA_of_nonempty_separation
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine C.tateAcyclicity_end_to_end_via_primary_laneA (f₀ := f₀) P hne ?_
    hZavyalov_per_E ?_ hLaneA
  · intro x hx
    exact separation_supplier C hne x 0 fun D hD ↦ by
      rw [hx D hD]
      exact (map_zero (restrictionMapHom C.base D (C.hsubset D hD))).symm
  · intro S' hS'_per_E hS'_contain E a b hlocal
    exact separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
      (per_E_nonempty S' hS'_per_E hS'_contain E) a b hlocal

/-- Full Tate-acyclicity conjunction from nonempty-cover separation, reducing
the per-E local-cover nonemptiness obligation to nonemptiness of the original
cover pieces.

The direct per-E gluing route needs Cor 8.32-style separation on each local
covering `C.per_E_local_covering ...`; that theorem is only available for
nonempty covers. `per_E_local_covering_nonempty_of_rationalOpen_nonempty`
shows this nonemptiness follows from a point of the original cover piece `E`,
so the caller only supplies the geometrically natural cover-piece
nonemptiness condition. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_laneA_of_nonempty_pieces
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hCoverPieces_nonempty : ∀ E : { E // E ∈ C.covers },
      (rationalOpen E.1.T E.1.s).Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine
    C.tateAcyclicity_end_to_end_via_primary_laneA_of_nonempty_separation
      (f₀ := f₀) P hne separation_supplier ?_ hZavyalov_per_E hLaneA
  intro S' hS'_per_E _hS'_contain E
  exact
    C.per_E_local_covering_nonempty_of_rationalOpen_nonempty S'.elts f₀ E
      hS'_per_E (hCoverPieces_nonempty E)

/-- Full Tate-acyclicity conjunction from nonempty-cover separation, with
empty original cover pieces handled internally.

This is the strongest current Lane-A final-assembly wrapper: it needs
nonempty-cover separation only where Cor 8.32-style input actually applies.
For a nonempty original piece `E`, `per_E_local_covering_nonempty_of_rationalOpen_nonempty`
supplies the nonempty local covering needed by the separation supplier. Empty
base and empty original pieces are discharged by the structural compatibility
lemmas in this file. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact separation_supplier C hne x 0 fun D hD ↦ by
      rw [hx D hD]
      exact (map_zero (restrictionMapHom C.base D (C.hsubset D hD))).symm
  · intro f hcompat
    exact C.tateAcyclicity_Part2_end_to_end_via_primary_allow_empty
      (f₀ := f₀) hne hZavyalov_per_E f hcompat
      (fun S' hS'_per_E hS'_contain ↦
        RationalCoveringData.lane_A_supplier_via_primary C f₀ hLaneA.hNoeth_B hLaneA.hLocLift_B
          hLaneA.hA₀Noeth_B hLaneA.hA_complete_B hLaneA.hnoeth_B hLaneA.hcont_forward_B
          hLaneA.hcont_eval_B hLaneA.τ_preBiv hLaneA.h_plus_compat hLaneA.h_minus_compat
          S' hS'_per_E hS'_contain
          (hLaneA.plus_section_refined S' hS'_per_E hS'_contain)
          (hLaneA.minus_section_refined S' hS'_per_E hS'_contain)
          (hLaneA.hOverlap S' hS'_per_E hS'_contain))
      (fun S' hS'_per_E _hS'_contain E hE_nonempty a b hlocal ↦
        separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
          (C.per_E_local_covering_nonempty_of_rationalOpen_nonempty
            S'.elts f₀ E hS'_per_E hE_nonempty)
          a b hlocal)

/-- Canonical-Lane-A variant of
`tateAcyclicity_end_to_end_via_primary_allow_empty`.

This keeps the same separation and standard-refinement boundary, but consumes
`PrimaryLaneAInputsCanonical`, whose completion and minus-continuity fields are
filled internally. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_canonical_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact separation_supplier C hne x 0 fun D hD ↦ by
      rw [hx D hD]
      exact (map_zero (restrictionMapHom C.base D (C.hsubset D hD))).symm
  · intro f hcompat
    exact C.part2_via_primary_canonical_allow_empty (f₀ := f₀) hne hZavyalov_per_E
      f hcompat
      (fun S' hS'_per_E _hS'_contain E hE_nonempty a b hlocal ↦
        separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
          (C.per_E_local_covering_nonempty_of_rationalOpen_nonempty
            S'.elts f₀ E hS'_per_E hE_nonempty)
          a b hlocal)
      hLaneA

omit [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)] in
/-- Canonical-Lane-A final assembly with the current Corollary 8.32
prime-extension-closed separation route wired in.

This does not add hypotheses to the root `tateAcyclicity` theorem; it is a
caller-ready bridge showing exactly which existing Lane-B residuals are enough
to supply the nonempty-cover separation input for the canonical Lane-A
assembly. -/
theorem RationalCoveringData.tateAcyclicity_end_to_end_via_primary_canonical_primeExtensionClosed
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀ : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  exact C.tateAcyclicity_end_to_end_via_primary_canonical_allow_empty
    (f₀ := f₀) P hne
    (RationalCoveringData.nonempty_separation_supplier_via_prime_extension_closed
      P hloc_noeth hAplus_le_A₀ hcanonicalMap_cont h_closed_nonOpen)
    hZavyalov_per_E hLaneA

/-- Full acyclicity wrapper with Lane A internalized and per-cover-piece
standard refinement data supplied explicitly.

This is the full-conjunction analogue of
`part2_via_primary_laneA_per_D_allow_empty`: empty original cover pieces are
handled internally, and the caller no longer supplies the abstract
`hZavyalov_per_E` refinement existential. -/
theorem RationalCoveringData.tateAcyclicity_via_primary_per_D_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  exact C.tateAcyclicity_end_to_end_via_primary_allow_empty
    (f₀ := f₀) P hne separation_supplier
    (hZavyalov_per_E_of_per_D_construction
      (A := A) (C := C) mk_S_D h_in_D h_cover_D h_span)
    hLaneA

/-- Full acyclicity wrapper with Lane A internalized for covers already in
standard single-generator shape.

This packages `exists_refines_cover_per_E_of_standardShape` into the strongest
current allow-empty final-assembly boundary. The remaining inputs are the
nonempty-cover separation supplier, the standard-shape presentation, the
span-top condition, and the Lane A overlap package. -/
theorem RationalCoveringData.tateAcyclicity_via_primary_standardShape_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  exact C.tateAcyclicity_end_to_end_via_primary_allow_empty
    (f₀ := f₀) P hne separation_supplier
    (fun _ ↦
      exists_refines_cover_per_E_of_standardShape
        (A := A) (C := C) f_D h_shape h_span)
    hLaneA

/-- Canonical-Lane-A per-D refinement wrapper.

Compared to `tateAcyclicity_via_primary_per_D_allow_empty`, this consumes
`PrimaryLaneAInputsCanonical` and fills the canonical completion/minus
continuity fields internally. -/
theorem RationalCoveringData.tateAcyclicity_via_primary_per_D_canonical_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (mk_S_D : RationalLocData A → Finset A)
    (h_in_D : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s)
    (h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  exact C.tateAcyclicity_end_to_end_via_primary_canonical_allow_empty
    (f₀ := f₀) P hne separation_supplier
    (hZavyalov_per_E_of_per_D_construction
      (A := A) (C := C) mk_S_D h_in_D h_cover_D h_span)
    hLaneA

/-- Canonical-Lane-A standard-shape wrapper.

Compared to `tateAcyclicity_via_primary_standardShape_allow_empty`, this
consumes `PrimaryLaneAInputsCanonical` and fills the canonical
completion/minus-continuity fields internally. -/
theorem RationalCoveringData.tateAcyclicity_via_primary_standardShape_canonical_allow_empty
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hne : C.covers.Nonempty)
    (separation_supplier : ∀ C' : RationalCoveringData A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (f_D : RationalLocData A → A)
    (h_shape : ∀ D ∈ C.covers,
      rationalOpen D.T D.s =
        rationalOpen (insert (f_D D) C.base.T) C.base.s)
    (h_span :
      Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤)
    (hLaneA : PrimaryLaneAInputsCanonical C f₀) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
          restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  exact C.tateAcyclicity_end_to_end_via_primary_canonical_allow_empty
    (f₀ := f₀) P hne separation_supplier
    (fun _ ↦
      exists_refines_cover_per_E_of_standardShape
        (A := A) (C := C) f_D h_shape h_span)
    hLaneA

end ConcreteLaneA

/-! ## T141 Laurent embedding → Laurent-cover-level separation (T144 wrapper)

Records the consumer surface that connects the post-T141 Laurent embedding
theorem `laurentCover_isEmbedding_presheaf_of_complete` to the final Tate
acyclicity route. T141 produces `Topology.IsEmbedding` of the two-piece
Laurent pair restriction map at completed `presheafValue D₀` level under
the v3 strict-exactness boundary; this section repackages the
`Topology.IsEmbedding.injective` projection in the **Lane-B-supplier
shape** consumed by the direct per-E gluing assembly
(`tateAcyclicity_Part2_end_to_end_via_primary_laneA`).

The wrapper is a thin no-sorry consumer of T141. It does **not** duplicate:

* Primary's presheafValue OMT prerequisite work (which discharges
  `hSigCp_B`, `hA_complete_B`, `hnoeth_B`, `hnoeth₂_B` from upstream
  Tate / strongly noetherian data); these remain explicit hypotheses
  here, dischargeable per call site.
* Secondary's bridge-inducing work (deriving `hτ_plus_inducing` /
  `hτ_minus_inducing` from `presheafValueCanonicalQuotientEquiv`); these
  also remain explicit hypotheses here, dischargeable in a
  Lane-B-canonical follow-up wrapper once Secondary's lane lands.

No public `[CompleteSpace A]`, `[IsDomain A]`, generic `D.s`-localization,
or parked T113/T119 hypothesis is added to the final Tate acyclicity
boundary; all hypotheses here are presheafValue-level or content-bearing
non-unit / topology hypotheses already in T141's signature. -/

/-- **Laurent-cover-level separation from T141 strict-exactness embedding.**

Given a rational localization datum `D₀` and a splitter `f`, plus all the
prerequisites of `laurentCover_isEmbedding_presheaf_of_complete` (T141), the
two-piece Laurent restriction map out of `presheafValue D₀` is injective
(the `Function.Injective` projection of T141's `Topology.IsEmbedding`).

This wrapper repackages T141's conclusion in the Lane-B separation supplier
shape

```
∀ a b : presheafValue D₀,
  restrictionMap D₀ plus  hplus  a = restrictionMap D₀ plus  hplus  b →
  restrictionMap D₀ minus hminus a = restrictionMap D₀ minus hminus b →
  a = b
```

consumed by the direct per-E gluing assembly (e.g., the `lane_B_supplier`
hypothesis of `tateAcyclicity_Part2_end_to_end_via_primary_laneA`) when the
per-E local cover is the canonical 2-piece Laurent cover
`{laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}`.

The hypotheses are unchanged from T141; the `hτ_plus_inducing`,
`hτ_minus_inducing` τ-bridge inducing hypotheses are kept explicit. The
follow-up Secondary lane (T142/T143) will derive those from
`presheafValueCanonicalQuotientEquiv`-style upstream API and package them
as a `_canonical` variant.

The proof is one line: extract `Topology.IsEmbedding.injective` from T141
and apply it to the `Prod.ext` of the two component-wise hypotheses. -/
theorem laurentCover_separation_via_isEmbedding_presheaf_of_complete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hTate_B : IsTateRing (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI := hTate_B
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI := hTate_B
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (hτ_plus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_plus :
          presheafValue (laurentPlusDatum D₀ f) →
            LaurentCover.B₁_gen (D₀.canonicalMap f)))
    (hτ_minus_inducing : letI := hNoeth_B; letI := hDom_B; letI := hTate_B
      Topology.IsInducing
        (τ_minus :
          presheafValue (laurentMinusDatum D₀ f) →
            LaurentCover.B₂_gen (D₀.canonicalMap f))) :
    ∀ a b : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus a =
        restrictionMap D₀ (laurentPlusDatum D₀ f) hplus b →
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus a =
        restrictionMap D₀ (laurentMinusDatum D₀ f) hminus b →
      a = b := by
  intro a b ha hb
  have hemb :=
    laurentCover_isEmbedding_presheaf_of_complete D₀ f hf_nonunit hNoeth_B
      hDom_B hTate_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B hplus hminus
      τ_plus τ_minus htau_plus htau_minus hτ_plus_inducing hτ_minus_inducing
  exact hemb.injective (Prod.ext ha hb)

/-! ## T153 Lane-B-shape wrapper consuming T149's bridges-baire-auto embedding

The T144 wrapper above consumes T141 (`laurentCover_isEmbedding_presheaf_of_complete`),
which carries the τ-bridges, their compatibility witnesses, the τ-inducing
witnesses, and both Baire hypotheses as explicit parameters. After T142–T149
the τ-bridges and τ-inducing witnesses are constructed internally by
`laurentPlusBridge` / `laurentMinusBridge` / `laurentPlusBridge_isInducing`
/ `laurentMinusBridge_isInducing`, and both Baire hypotheses are discharged
by the T149 generic supplier `presheafValue_baireSpace`. The strongest
post-T150 Laurent embedding theorem at the completed presheafValue level is

  `ValuationSpectrum.laurentCover_isEmbedding_presheaf_via_bridges_baire_auto`

(`Adic spaces/LaurentRefinement.lean`, T149 consumer wrapper).

T153 packages the `Topology.IsEmbedding.injective` projection of this
post-T149 embedding in the same Lane-B-supplier shape used by the direct
per-E gluing assembly (`tateAcyclicity_Part2_end_to_end_via_primary_laneA`).

The wrapper is a thin no-sorry consumer of T149. It does **not** duplicate:

* Primary's T151 lane (presheafValue ring-of-definition Noetherian base
  case in `PresheafTateStructure.lean`); the two noetherian inputs
  `hNoeth_B` and `hA₀Noeth_B` remain explicit hypotheses here,
  dischargeable when T151 lands.
* Secondary's T152 lane (Laurent SigmaCompact / OMT route decision in
  `LaurentRefinement.lean` / `LaurentBaireSupport.lean`); the two
  `hSigma_plus_B` / `hSigma_minus_B` and the source-side `hSigCp_B`
  remain explicit hypotheses here, dischargeable when T152 lands.

When T151 / T152 land their respective discharges, a follow-up
`_canonical` / `_auto` variant of this wrapper can absorb them; that is
out of scope for T153.

No public `[CompleteSpace A]`, `[IsDomain A]`, generic `D.s`-localization,
or parked T113/T119 hypothesis is added to the final Tate acyclicity
boundary. -/

/-- **Post-T149 Lane-B-shape Laurent separation supplier.**

Given a rational localization datum `D₀` with `LaurentNormalized D₀` and a
splitter `f`, plus all the prerequisites of T149's
`laurentCover_isEmbedding_presheaf_via_bridges_baire_auto`, the two-piece
Laurent restriction map out of `presheafValue D₀` is injective (the
`Function.Injective` projection of T149's `Topology.IsEmbedding`).

Compared to T144 (`laurentCover_separation_via_isEmbedding_presheaf_of_complete`),
this wrapper has a **smaller hypothesis surface**: the T141 τ-bridges,
τ-bridge compatibility witnesses, τ-bridge-inducing witnesses, and the two
Baire hypotheses are all internally discharged via T142–T149.  The
remaining supplier obligations are exactly the post-T150 boundary: the
presheafValue noetherian / completion / OMT prerequisites at the completed
`presheafValue D₀` Tate base.

The proof is one line: extract `Topology.IsEmbedding.injective` from T149
and apply it to the `Prod.ext` of the two component-wise hypotheses. -/
theorem laurentCover_separation_via_isEmbedding_presheaf_via_bridges_baire_auto
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigma_plus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          plusFSubXIdeal (presheafValue D₀) (D₀.canonicalMap f))
        (quotientPlusFSubXIdealTopology (presheafValue D₀)
          (D₀.canonicalMap f)))
    (hSigma_minus_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      @SigmaCompactSpace
        (↥(TateAlgebra (presheafValue D₀)) ⧸
          TateAlgebra.oneSubfXIdeal (iteratedMinusDatum_B P D₀ f).s)
        (TateAlgebra.quotientOneSubfXIdealTopology
          (iteratedMinusDatum_B P D₀ f).s))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    ∀ a b : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus a =
        restrictionMap D₀ (laurentPlusDatum D₀ f) hplus b →
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus a =
        restrictionMap D₀ (laurentMinusDatum D₀ f) hminus b →
      a = b := by
  intro a b ha hb
  have hemb :=
    laurentCover_isEmbedding_presheaf_via_bridges_baire_auto P D₀ f hf_nonunit
      hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B hLocLift_B
      hA₀Noeth_B hcont_forward_B hcont_eval_B hSigma_plus_B hSigma_minus_B
      hplus hminus
  exact hemb.injective (Prod.ext ha hb)

/-! ### T-NEW-4: combined Part 1 + Part 2 wrapper via abstract suppliers

**T-NEW-4 (2026-05-11)**.

Final cap on the Tate acyclicity (Wedhorn Theorem 8.28(b)) result for
strongly noetherian Tate rings: produces both Part 1 (separation) and Part 2
(gluing) of the sheaf condition from **abstract lane suppliers** matching the
existing assembly architecture.

Composition:
* Part 1 follows from a cover-level separation supplier
  (`global_separation`) — typically packaged via
  `RationalCoveringData.separation_via_prime_extension_closed` /
  `nonempty_separation_supplier_via_prime_extension_closed` or — in the
  corrected (post-2026-05-11) route — the new
  `productRestriction_faithfullyFlat_tate_laurent_of_hSpa_points` chain
  for Laurent-shape covers.
* Part 2 follows from the existing
  `tateAcyclicity_Part2_end_to_end_via_primary` wrapper, fed `lane_A_supplier`
  and `lane_B_supplier` (the latter is the per-E separation supplier whose
  flatness route is the subject of T-FLAT-PER-E).

This wrapper does NOT propagate the misframed `restrictionMap_isLocalization`
chain — all flatness is delegated to the caller via the lane suppliers. -/
theorem RationalCoveringData.tateAcyclicityComplete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (global_separation : ∀ a b : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) a =
          restrictionMap C.base D (C.hsubset D hD) b) →
      a = b)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    -- Part 1: separation (zero-kernel form).
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · -- Part 1 via `global_separation` with `b := 0`.
    intro x hx
    have hagree : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) 0 := by
      intro D hD
      change restrictionMapHom C.base D (C.hsubset D hD) x =
        restrictionMapHom C.base D (C.hsubset D hD) 0
      rw [map_zero]; exact hx D hD
    exact global_separation x 0 hagree
  · -- Part 2 via the existing assembly wrapper.
    intro fC hC_compat
    exact RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary
      (A := A) C hne hZavyalov_per_E f₀ fC hC_compat
      lane_A_supplier lane_B_supplier

/-! ### Allow-empty Part-2 variant of `tateAcyclicityComplete`

Drop-in variant of `tateAcyclicityComplete` that uses the empty-piece-tolerant
Part-2 assembly. The `lane_B_supplier` only needs to handle E's with nonempty
`rationalOpen`. Empty cases are handled structurally. -/
theorem RationalCoveringData.tateAcyclicityComplete_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (global_separation : ∀ a b : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) a =
          restrictionMap C.base D (C.hsubset D hD) b) →
      a = b)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hagree : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) 0 := by
      intro D hD
      change restrictionMapHom C.base D (C.hsubset D hD) x =
        restrictionMapHom C.base D (C.hsubset D hD) 0
      rw [map_zero]; exact hx D hD
    exact global_separation x 0 hagree
  · intro fC hC_compat
    exact RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_allow_empty
      (A := A) C hne hZavyalov_per_E f₀ fC hC_compat
      lane_A_supplier lane_B_supplier

/-! ### Combined wrapper via the prime-extension-closed route

Composition of `tateAcyclicityComplete_allow_empty` with the existing universal
separation supplier (`nonempty_separation_supplier_via_prime_extension_closed`) —
supplies BOTH `global_separation` and `lane_B_supplier` from the same universal
prime-extension-closed hypothesis bundle.

This produces a less-abstract wrapper at the cost of propagating the existing
`flat_over_base_tate` chain through `restrictionMap_isLocalization` (a known
issue tracked at T-RETIRE-PROP815 / T-FLAT-PER-E). The user can substitute the
new flatness route (T-COR832-FF-LAURENT) once T-FLAT-PER-E is resolved by
swapping out the `_via_prime_extension_closed` chain.

`lane_A_supplier` remains abstract; this wrapper does NOT discharge Lane A
overlap gluing. -/
theorem RationalCoveringData.tateAcyclicityComplete_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    -- Universal hypothesis bundle for the prime-extension-closed Cor 8.32 chain:
    (hloc_noeth : ∀ C' : RationalCoveringData A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀ : ∀ C' : RationalCoveringData A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCoveringData A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCoveringData A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  classical
  have sep_supplier := RationalCoveringData.nonempty_separation_supplier_via_prime_extension_closed
    P hloc_noeth hAplus_le_A₀ hcanonicalMap_cont h_closed_nonOpen
  refine RationalCoveringData.tateAcyclicityComplete_allow_empty (A := A) C hne
    hZavyalov_per_E f₀
    (sep_supplier C hne)
    lane_A_supplier
    ?_
  -- `lane_B_supplier` (allow_empty form): per-E separation only required for
  -- nonempty per-E rationalOpen. Use `hS'_per_E` at any `v` in the nonempty
  -- per-E rationalOpen to produce a cover element, hence nonempty per_E covers,
  -- then apply `sep_supplier`.
  intro S' hS'_per_E _hS'_contain E hE_rop_ne a b hagree
  obtain ⟨v, hv⟩ := hE_rop_ne
  obtain ⟨f, hf_elt, _hv_plus, h_plus_in_E⟩ := hS'_per_E E.1 E.2 v hv
  have hne_per_E :
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty := by
    refine ⟨laurentPlusDatum (C.plusDatum f) f₀, ?_⟩
    rw [RationalCoveringData.mem_per_E_local_covering_covers]
    exact ⟨f, hf_elt, h_plus_in_E, Or.inl rfl⟩
  exact sep_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
    hne_per_E a b hagree

/-! ### Equality-form separation for normalized-Laurent covers (T-SEP-NORMALIZED)

Equality-form companion to T233's zero-kernel form. Combines
`productRestriction_injective_tate_normalizedLaurent_of_hSpa_points` with the
standard `a - b = 0` conversion to produce the `global_separation` hypothesis
required by `tateAcyclicityComplete`. -/
theorem RationalCoveringData.separation_via_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf))) :
    ∀ a b : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) a =
          restrictionMap C.base D (C.hsubset D hD) b) →
      a = b := by
  intro a b hagree
  have hzero : a - b = 0 := by
    apply productRestriction_injective_tate_normalizedLaurent_of_hSpa_points
      P C hne normalized_laurent_witness hSpa_points
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f
    intro D hD
    change restrictionMapHom C.base D (C.hsubset D hD) (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hagree D hD
  exact sub_eq_zero.mp hzero

/-! ### Helper: `invS D` is power-bounded when `1 ∈ D.T`

For any rational locale `D` over any base where `1 ∈ D.T`, the unit
`invS D = (D.canonicalMap D.s)⁻¹` is power-bounded in `presheafValue D`'s
topology. Generalises the per-piece argument used in
`iteratedMinus_B_flat_of_canonical`. -/
theorem invS_isPowerBounded_of_one_mem_T_general
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    (D : RationalLocData A) (h1 : (1 : A) ∈ D.T) :
    TopologicalRing.IsPowerBounded (invS D) := by
  -- invS D = D.coeRingHom (divByS 1 D.s) (via the unit-cancellation identity).
  have hinvS_eq : invS D = D.coeRingHom (divByS (1 : A) D.s) := by
    have h1_eq : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
    have halg : algebraMap A (Localization.Away D.s) D.s * divByS (1 : A) D.s = 1 := by
      rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
    have h2 : D.canonicalMap D.s * D.coeRingHom (divByS (1 : A) D.s) = 1 := by
      change D.coeRingHom (algebraMap A (Localization.Away D.s) D.s) *
        D.coeRingHom (divByS (1 : A) D.s) = 1
      rw [← map_mul, halg, map_one]
    exact (isUnit_s_in_presheafValue D).mul_left_cancel (h1_eq.trans h2.symm)
  rw [hinvS_eq]
  exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T D h1

/-! ### Helper: minimal `invS_isPowerBounded_of_one_mem_T`

Mirrors `invS_isPowerBounded_of_one_mem_T_general` but drops the
`[PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]` typeclass
constraints. The proof body only uses `canonicalMap`, `coeRingHom`,
`divByS`, and `CompletionLocalization.invS_isPowerBounded_of_one_mem_T`,
each of which requires only `[CommRing A] [TopologicalSpace A]
[IsTopologicalRing A]`.

This allows the discharge to work at the B-level (B = presheafValue
C.base) without needing a `HasLocLiftPowerBounded (presheafValue C.base)`
preservation theorem (T-LOCLIFT-PRESERVATION). -/
theorem invS_isPowerBounded_of_one_mem_T_minimal
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (D : RationalLocData A) (h1 : (1 : A) ∈ D.T) :
    TopologicalRing.IsPowerBounded (invS D) := by
  have hinvS_eq : invS D = D.coeRingHom (divByS (1 : A) D.s) := by
    have h1_eq : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
    have halg : algebraMap A (Localization.Away D.s) D.s * divByS (1 : A) D.s = 1 := by
      rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
    have h2 : D.canonicalMap D.s * D.coeRingHom (divByS (1 : A) D.s) = 1 := by
      change D.coeRingHom (algebraMap A (Localization.Away D.s) D.s) *
        D.coeRingHom (divByS (1 : A) D.s) = 1
      rw [← map_mul, halg, map_one]
    exact (CompletionLocalization.isUnit_s_in_presheafValue D).mul_left_cancel
      (h1_eq.trans h2.symm)
  rw [hinvS_eq]
  exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T D h1

/-! ### Helper: `canonicalMap a` is power-bounded for `a ∈ P.A₀`

For any rational locale `D` and any element `a ∈ D.P.A₀` (the ring of
definition's base ring), the image `D.canonicalMap a` is power-bounded in
`presheafValue D`. The proof goes through `algebraMap_mem_locSubring` +
`coeRingHom_image_locSubring_isBounded`. -/
theorem canonicalMap_isPowerBounded_of_mem_A₀
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsHuberRing A]
    (D : RationalLocData A) {a : A} (ha : a ∈ D.P.A₀) :
    TopologicalRing.IsPowerBounded (D.canonicalMap a) := by
  -- D.canonicalMap a = D.coeRingHom (algebraMap A (Localization.Away D.s) a).
  have hcm : D.canonicalMap a =
      D.coeRingHom (algebraMap A (Localization.Away D.s) a) := rfl
  rw [hcm]
  -- algebraMap a ∈ locSubring D.P D.T D.s by algebraMap_mem_locSubring.
  have hmem : algebraMap A (Localization.Away D.s) a ∈ locSubring D.P D.T D.s :=
    algebraMap_mem_locSubring D.P D.T D.s ha
  -- All powers of algebraMap a stay in locSubring (subring closed under powers).
  have hpow : ∀ n : ℕ, (algebraMap A (Localization.Away D.s) a) ^ n ∈
      locSubring D.P D.T D.s :=
    fun n ↦ (locSubring D.P D.T D.s).pow_mem hmem n
  -- The range of (D.coeRingHom (algebraMap a))^· lies in D.coeRingHom '' locSubring.
  have hrange : Set.range
      ((D.coeRingHom (algebraMap A (Localization.Away D.s) a)) ^ · :
        ℕ → presheafValue D) ⊆
      D.coeRingHom '' (locSubring D.P D.T D.s :
        Set (Localization.Away D.s)) := by
    rintro _ ⟨n, rfl⟩
    change (D.coeRingHom (algebraMap A (Localization.Away D.s) a)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(algebraMap A (Localization.Away D.s) a) ^ n, hpow n, rfl⟩
  exact (CompletionLocalization.coeRingHom_image_locSubring_isBounded D).subset hrange

/-! ### `tateAcyclicityComplete` wrapper with normalized-Laurent separation

Composes T234 (`separation_via_normalizedLaurent`) with `tateAcyclicityComplete`
to discharge the `global_separation` hypothesis for covers consisting of
normalized-minus pieces. The Part 2 lane suppliers remain as hypotheses
(existing project infrastructure). -/
theorem RationalCoveringData.tateAcyclicityComplete_via_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    -- Part 1: separation (zero-kernel form).
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  RationalCoveringData.tateAcyclicityComplete C hne hZavyalov_per_E f₀
    (RationalCoveringData.separation_via_normalizedLaurent P C hne
      normalized_laurent_witness hSpa_points hNoeth_B hA_complete_B hnoeth_B
      hP_A₀Noeth_B hb_per_f hT_pb_per_f hcont_eval_per_f)
    lane_A_supplier lane_B_supplier

/-! ### Empty-coverings-tolerant separation/gluing via normalized-Laurent route

Two consumer-facing convenience wrappers mirroring
`rationalCovering_hasSeparation` / `rationalCovering_hasGluing` from
`LaurentRefinement.lean`, but routed through the sorry-free
`tateAcyclicityComplete_via_normalizedLaurent` instead of the legacy
`tateAcyclicity`.

Both wrappers handle the empty-coverings edge case identically to the
legacy extractions (subsingleton when `C.base.s = 0`; contradiction via
Spa-points when `C.base.s ≠ 0`); for nonempty coverings they delegate
to the normalized-Laurent bypass.

These are the migration targets for downstream callers (`Cor832.lean:462`,
`LaurentRefinement.lean:5801`, `StandardCover.lean:1629`) which currently
inherit the legacy `tateAcyclicity` Part 1 retired-sorry and Part 2
literal-sorry chain.

**Axiom hygiene status (2026-05-12)**: `#print axioms` for these wrappers
reports `[propext, sorryAx, Classical.choice, Quot.sound]`. The remaining
`sorryAx` is inherited from `hSpa_surj_from_spanTop` (Cor832.lean:512),
which depends on the retired-as-false `restrictionMap_isLocalization`
(Wedhorn Prop 8.15 in surjective form, false in general per the reviewer's
infinite-convergent-tail counterexample).

Closing the inherited `sorryAx` requires building a sorry-free prime-lifting
route that does NOT identify `presheafValue D` with the algebraic localization
`(presheafValue C.base)[s^{-1}]`. The natural candidates — going-down via
flatness, IsLocalRing characterization of FF, or maximal-only characterization
— all require additional structural arguments beyond what's currently in
the project. This is a separate research item not on the normalized-Laurent
critical path. -/

/-- Separation via the normalized-Laurent bypass, empty-coverings-tolerant. -/
theorem rationalCovering_hasSeparation_via_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf))) :
    ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y := by
  intro x y hxy
  by_cases hne : C.covers.Nonempty
  · exact RationalCoveringData.separation_via_normalizedLaurent P C hne
      normalized_laurent_witness hSpa
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f x y hxy
  · -- Empty covering edge case: identical to legacy `rationalCovering_hasSeparation`.
    by_cases hs : C.base.s = 0
    · haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
      exact Subsingleton.elim x y
    · haveI hprime : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
      have hs_notin : C.base.s ∉ (⊥ : Ideal A) := fun h ↦ hs (Ideal.mem_bot.mp h)
      obtain ⟨v, hv_rat, _⟩ := hSpa ⊥ hprime hs_notin
      obtain ⟨D, hD, _⟩ := C.hcover v hv_rat
      exact absurd ⟨D, hD⟩ hne

/-- Gluing via the normalized-Laurent bypass, empty-coverings-tolerant. -/
theorem rationalCovering_hasGluing_via_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  by_cases hne : C.covers.Nonempty
  · exact (RationalCoveringData.tateAcyclicityComplete_via_normalizedLaurent
      P C hne normalized_laurent_witness hSpa_points
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f
      hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier).2 f hcompat
  · -- Empty covering: any x works, pick 0.
    exact ⟨0, fun ⟨D, hD⟩ ↦ absurd ⟨D, hD⟩ hne⟩

/-! ### Empty-coverings-tolerant `tateAcyclicity` conjunction via normalized-Laurent

A single full-conjunction wrapper combining
`rationalCovering_hasSeparation_via_normalizedLaurent` (zero-kernel form
of Part 1) and `rationalCovering_hasGluing_via_normalizedLaurent` into the
conjunction shape of the legacy `tateAcyclicity` theorem.

This is the **primary drop-in migration target** for downstream callers
that consume the legacy `tateAcyclicity P C hne` conjunction. The signature
matches the legacy form on its conclusion, but adds the normalized-Laurent
hypothesis pack so the proof body is sorry-free (modulo the T001 root sorry
inherited via `hSpa_points`). -/
theorem tateAcyclicity_via_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A] [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    -- Part 1: zero-kernel separation (the same shape as legacy `tateAcyclicity`).
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: derive zero-kernel from equality-form separation via `b := 0`.
    intro x hx
    -- Use the empty-tolerant separation wrapper with hSpa applied to ⊥.
    -- For nonempty covers we delegate to separation_via_normalizedLaurent;
    -- for empty covers the helper handles the subsingleton / Spa-points dichotomy.
    have hsep : ∀ x y : presheafValue C.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
          restrictionMap C.base D (C.hsubset D hD) x =
          restrictionMap C.base D (C.hsubset D hD) y) → x = y :=
      rationalCovering_hasSeparation_via_normalizedLaurent (A := A) P C
        hSpa_points normalized_laurent_witness
        hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
        hb_per_f hT_pb_per_f hcont_eval_per_f
    refine hsep x 0 (fun D hD ↦ ?_)
    rw [show restrictionMap C.base D (C.hsubset D hD) 0 = 0 by
        change restrictionMapHom C.base D _ 0 = 0; exact map_zero _]
    exact hx D hD
  · -- Part 2: directly use gluing wrapper.
    exact rationalCovering_hasGluing_via_normalizedLaurent (A := A) P C
      normalized_laurent_witness hSpa_points
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f
      hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier

/-! ### `tateAcyclicity_via_normalizedLaurent` with auto-discharged `hA_complete_B`

The `hA_complete_B` hypothesis (`CompleteSpace (presheafValue C.base)` w.r.t. the
right-uniform-space) is structurally auto-derivable via
`CompleteSpace_presheafValue_rightUniformSpace`. This wrapper drops the
explicit hypothesis from the signature and discharges it internally,
producing a slightly leaner consumer-facing variant.

All other hypotheses are unchanged from `tateAcyclicity_via_normalizedLaurent`. -/
theorem tateAcyclicity_via_normalizedLaurent_autoComplete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A] [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    -- Part 1: zero-kernel separation.
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    -- Part 2: gluing.
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  tateAcyclicity_via_normalizedLaurent (A := A) P C
    normalized_laurent_witness hSpa_points
    hNoeth_B (CompleteSpace_presheafValue_rightUniformSpace C.base)
    hnoeth_B hP_A₀Noeth_B
    hb_per_f hT_pb_per_f hcont_eval_per_f
    hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier

/-! ### `tateAcyclicity_via_normalizedLaurent` with auto-discharged `hT_pb_per_f`

The `hT_pb_per_f` hypothesis (every `t ∈ T_at_E` is power-bounded) is
structurally auto-derivable using `canonicalMap_isPowerBounded_of_mem_A₀`:
each `t = C.base.canonicalMap d` for `d ∈ (laurentMinusNormalizedDatum C.base f).T`,
and by `LaurentNormalized` (laurentMinusNormalizedDatum C.base f), every such
`d` lies in `C.base.P.A₀`. The helper then gives power-boundedness.

This drops one more hypothesis from the wrapper signature, building on top
of `_autoComplete` (which already dropped `hA_complete_B`). -/
theorem tateAcyclicity_via_normalizedLaurent_autoTPB
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A] [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  tateAcyclicity_via_normalizedLaurent_autoComplete (A := A) P C
    normalized_laurent_witness hSpa_points
    hNoeth_B hnoeth_B hP_A₀Noeth_B
    hb_per_f
    -- Auto-discharge of `hT_pb_per_f`:
    (by
      letI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing P C.base
      letI : DecidableEq A := Classical.decEq A
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      intro f hf
      letI hLN : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      intro t ht
      -- t ∈ T_at_E = (laurentMinusNormalizedDatum C.base f).T.image C.base.canonicalMap
      -- by `relativeRationalLocData_laurentNormalized_T`.
      have ht' : t ∈ (laurentMinusNormalizedDatum C.base f).T.image C.base.canonicalMap := by
        rw [relativeRationalLocData_laurentNormalized_T] at ht
        exact ht
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht'
      -- d ∈ (laurentMinusNormalizedDatum C.base f).T ⊆ insert s T ⊆ P.A₀
      -- by LaurentNormalized (laurentMinusNormalizedDatum C.base f).
      have hd_in_insert : d ∈ insert (laurentMinusNormalizedDatum C.base f).s
          (laurentMinusNormalizedDatum C.base f).T := Finset.mem_insert_of_mem hd
      have hd_A₀ : d ∈ C.base.P.A₀ := hLN.insert_s_T_subset_A₀ d hd_in_insert
      exact canonicalMap_isPowerBounded_of_mem_A₀ C.base hd_A₀)
    hcont_eval_per_f
    hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier

/-! ### Auto-discharged `hb_per_f` for normalized-Laurent

For each `f ∈ C.base.P.A₀`, the relative datum's `T` contains `1` (via
`canonicalMap 1 = 1` and `1 ∈ (laurentMinusNormalizedDatum C.base f).T`).
Applying `invS_isPowerBounded_of_one_mem_T_minimal` gives power-boundedness
of `invS (relativeRationalLocData_laurentNormalized ...)`. -/
theorem hb_per_f_auto_normalizedLaurent
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    letI : IsTateRing (presheafValue C.base) :=
      presheafValue_isTateRing P C.base
    letI : DecidableEq A := Classical.decEq A
    letI : DecidableEq (presheafValue C.base) := Classical.decEq _
    ∀ (f : A) (hf : f ∈ C.base.P.A₀),
    letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
      laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
    TopologicalRing.IsPowerBounded
      (invS (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f))) := by
  letI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing P C.base
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq (presheafValue C.base) := Classical.decEq _
  intro f hf
  letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
    laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
  apply invS_isPowerBounded_of_one_mem_T_minimal
  change 1 ∈ (relativeRationalLocData_laurentNormalized C.base
    (laurentMinusNormalizedDatum C.base f)
    (laurentMinusNormalized_subset C.base f)).T
  rw [relativeRationalLocData_laurentNormalized_T]
  refine Finset.mem_image.mpr ⟨1, ?_, map_one _⟩
  exact Finset.mem_insert_self _ _

/-! ### `tateAcyclicity_via_normalizedLaurent` with auto-discharged `hb_per_f`

Drops the `hb_per_f` hypothesis using `hb_per_f_auto_normalizedLaurent`
(T245). The `hcont_eval_per_f` parameter now refers to the auto-discharged
`hb_per_f` term directly. Combined with `_autoTPB` (T243) and
`_autoComplete` (T240), this leaves only `hNoeth_B`, `hnoeth_B`,
`hP_A₀Noeth_B`, and `hcont_eval_per_f` as structural B-level hypotheses,
plus the application-specific lane suppliers. -/
theorem tateAcyclicity_via_normalizedLaurent_autoB
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A] [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))
          (hb_per_f_auto_normalizedLaurent P C f hf)))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  tateAcyclicity_via_normalizedLaurent_autoTPB (A := A) P C
    normalized_laurent_witness hSpa_points
    hNoeth_B hnoeth_B hP_A₀Noeth_B
    (hb_per_f_auto_normalizedLaurent P C)
    hcont_eval_per_f
    hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier

/-! ### `tateAcyclicity_via_normalizedLaurent` with auto-discharged
`hcont_eval_per_f`

Drops the `hcont_eval_per_f` hypothesis using
`tateQuotientToPresheafHom_continuous_of_tate` at the B-level. The B-level
typeclasses required (`IsTateRing` via `presheafValue_isTateRing`,
`NonarchimedeanRing` via `presheafValueNonarchimedeanRing`) are both
automatically available, so the continuity follows unconditionally for
each `f ∈ C.base.P.A₀`.

Combined with the previous auto-discharges (T240/T243/T246), this wrapper
has 7 hypotheses (down from 11 in T239), with the remaining structural
B-level hypotheses being `hNoeth_B`, `hnoeth_B`, `hP_A₀Noeth_B` (each
requires Stacks 00MA + Example 6.38 preservation). -/
theorem tateAcyclicity_via_normalizedLaurent_autoCont
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A] [DecidableEq A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hZavyalov_per_E : rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S)
    (f₀ : A)
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b) :
    (∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0) ∧
    (∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
      (∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
      ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D) :=
  tateAcyclicity_via_normalizedLaurent_autoB (A := A) P C
    normalized_laurent_witness hSpa_points
    hNoeth_B hnoeth_B hP_A₀Noeth_B
    -- Auto-discharge of hcont_eval_per_f via tateQuotientToPresheafHom_continuous_of_tate.
    (by
      letI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing P C.base
      letI : DecidableEq A := Classical.decEq A
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      haveI : NonarchimedeanRing (presheafValue C.base) :=
        presheafValueNonarchimedeanRing C.base
      intro f hf
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      exact tateQuotientToPresheafHom_continuous_of_tate _ _)
    hZavyalov_per_E f₀ lane_A_supplier lane_B_supplier

end ValuationSpectrum
