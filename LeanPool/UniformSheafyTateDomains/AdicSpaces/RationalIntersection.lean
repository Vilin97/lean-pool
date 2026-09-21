/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativePieceKeystone

/-!
# Arbitrary-pair rational intersections and the compatibility bridge

**R1 (arbitrary-pair intersections).** `interSamePair` (LaurentRefinementCore) realises
`R(D₁) ∩ R(D₂)` only when the two data share a `PairOfDefinition`. Here we construct the
intersection datum for **arbitrary** valid rational data over a Tate ring:
`rationalOpen` does not mention the pair, and for spanning trays the `hopen`-condition
is `genPiece_hopen` (span + absorption), so

    interDatum D E hD hE := genPieceDatum D.P ((insert D.s D.T) * (insert E.s E.T)) (D.s * E.s) _

satisfies `R(interDatum) = R(D) ∩ R(E)` (Wedhorn Proposition 7.31(2)) with **no**
`D.P = E.P` hypothesis. Its pair is (arbitrarily) `D.P` — the rational open, the
presheaf value, and all restriction maps are presentation-robust, so the choice is
immaterial downstream.

**R3 (compatibility bridge).** For a family on the pieces of a rational covering, three
compatibility conditions:

1. `AllDataCompatible` — agreement after restriction to **every raw datum** contained in
   both pieces. This is verbatim the hypothesis of the legacy `IsSheafy.gluing` field.
2. `RationalRefinementCompatible` — agreement on every **valid rational** common
   refinement (the literature's condition).
3. `ExactIntersectionCompatible` — agreement on the **chosen exact intersection datum**
   `interDatum` of each pair of pieces.

Over a Tate ring with a rational covering these are all equivalent
(`allDataCompatible_iff_exactIntersectionCompatible` etc.): (1) ⟹ (2) ⟹ (3) by
specialisation, and (3) ⟹ (1) by factoring the restriction to a raw `D₃ ⊆ R(D₁) ∩ R(D₂)`
through the intersection datum (`restrictionMap_comp` + proof irrelevance of the
containment witnesses). In particular the legacy all-raw-data gluing input of `IsSheafy`
is *equivalent* to the literature-facing valid-refinement condition — the handover's R3
bridge. The (1)⟸(3) direction retains the raw-data restriction infrastructure
(`HasLocLiftPowerBounded`), as permitted for the legacy adapter.

**Regression notes (handover R1/R3 exit criteria).**
* Different pairs of definition: `interDatum` takes no pair-equality hypothesis at all —
  see `interDatum_of_ne_pairs` below, stated for two data with *unrelated* pairs.
* Duplicate presentations: `interDatum_rationalOpen` computes the open from `(T, s)`
  alone, so duplicate presentations of the same subset give data with the same rational
  open (and hence presentation-independent compatibility conditions, which quantify only
  over rational opens).
* Empty intersections: nothing here assumes `R(D) ∩ R(E) ≠ ∅`; `interDatum` is a valid
  datum with (possibly) empty rational open.
-/

noncomputable section

open scoped Pointwise

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DecidableEq A]

/-! ### R1: the intersection datum for arbitrary pairs -/

/-- The intersection tray: `(insert D.s D.T) · (insert E.s E.T)` (Wedhorn 7.31(2)'s
generator set for `R(D) ∩ R(E)`), written as the `Finset`-image the rest of the
rational layer uses. -/
def RationalLocData.interTray (D E : RationalLocData A) : Finset A :=
  ((insert D.s D.T).product (insert E.s E.T)).image (fun p => p.1 * p.2)

theorem RationalLocData.interTray_eq_mul (D E : RationalLocData A) :
    D.interTray E = (insert D.s D.T) * (insert E.s E.T) := by
  rw [Finset.mul_def]; rfl

/-- Spanning trays multiply to a spanning tray (`span (S·T) = span S · span T`). -/
theorem RationalLocData.interTray_span_eq_top (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    Ideal.span ((D.interTray E : Finset A) : Set A) = ⊤ := by
  refine top_unique ?_
  calc (⊤ : Ideal A) = Ideal.span (D.T : Set A) * Ideal.span (E.T : Set A) := by
        rw [hD, hE, Ideal.top_mul]
    _ = Ideal.span ((D.T : Set A) * (E.T : Set A)) := Ideal.span_mul_span' _ _
    _ ≤ Ideal.span ((D.interTray E : Finset A) : Set A) := Ideal.span_mono (by
        rintro _ ⟨t, ht, u, hu, rfl⟩
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(t, u), ?_, rfl⟩)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_of_mem hu⟩)

/-- **The intersection datum for arbitrary valid pairs** (Wedhorn Proposition 7.31(2)):
a rational localization datum presenting `R(D) ∩ R(E)`, with **no shared-pair
hypothesis** — the `hopen`-condition comes from the spanning tray (`genPiece_hopen`),
not from the factors' pairs. The pair of definition is (arbitrarily) `D.P`. -/
def RationalLocData.interDatum (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    RationalLocData A :=
  genPieceDatum D.P (D.interTray E) (D.s * E.s) (D.interTray_span_eq_top E hD hE)

@[simp] theorem RationalLocData.interDatum_T (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    (D.interDatum E hD hE).T = D.interTray E := rfl

@[simp] theorem RationalLocData.interDatum_s (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    (D.interDatum E hD hE).s = D.s * E.s := rfl

theorem RationalLocData.interDatum_P (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    (D.interDatum E hD hE).P = D.P := rfl

/-- **`interDatum` realises the intersection**: `R(interDatum D E) = R(D) ∩ R(E)`.
The computation is pair-free (`rationalOpen` never mentions `P`). -/
theorem RationalLocData.interDatum_rationalOpen [PlusSubring A] (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    rationalOpen (D.interDatum E hD hE).T (D.interDatum E hD hE).s =
      rationalOpen D.T D.s ∩ rationalOpen E.T E.s := by
  rw [RationalLocData.interDatum_T, RationalLocData.interDatum_s,
    RationalLocData.interTray_eq_mul,
    ← rationalOpen_inter (insert D.s D.T) (insert E.s E.T) D.s E.s
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _),
    rationalOpen_insert_s, rationalOpen_insert_s]

/-- The intersection datum is rational (its tray spans `⊤`). -/
theorem RationalLocData.interDatum_isRational (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    (D.interDatum E hD hE).IsRational :=
  RationalLocData.isRational_of_span_eq_top (D.interTray_span_eq_top E hD hE)

theorem RationalLocData.interDatum_subset_left [PlusSubring A] (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    rationalOpen (D.interDatum E hD hE).T (D.interDatum E hD hE).s ⊆
      rationalOpen D.T D.s := by
  rw [RationalLocData.interDatum_rationalOpen]; exact Set.inter_subset_left

theorem RationalLocData.interDatum_subset_right [PlusSubring A] (D E : RationalLocData A)
    (hD : Ideal.span (D.T : Set A) = ⊤) (hE : Ideal.span (E.T : Set A) = ⊤) :
    rationalOpen (D.interDatum E hD hE).T (D.interDatum E hD hE).s ⊆
      rationalOpen E.T E.s := by
  rw [RationalLocData.interDatum_rationalOpen]; exact Set.inter_subset_right

section Tate

variable [IsTateRing A]

/-- Tate form: the intersection datum of two **valid** (Wedhorn 7.29) rational data,
with the spanning conditions supplied by `IsRational.span_eq_top`. -/
def RationalLocData.interRational (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) : RationalLocData A :=
  D.interDatum E hD.span_eq_top hE.span_eq_top

theorem RationalLocData.interRational_rationalOpen [PlusSubring A] (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interRational E hD hE).T (D.interRational E hD hE).s =
      rationalOpen D.T D.s ∩ rationalOpen E.T E.s :=
  D.interDatum_rationalOpen E hD.span_eq_top hE.span_eq_top

theorem RationalLocData.interRational_isRational (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    (D.interRational E hD hE).IsRational :=
  D.interDatum_isRational E hD.span_eq_top hE.span_eq_top

theorem RationalLocData.interRational_subset_left [PlusSubring A] (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interRational E hD hE).T (D.interRational E hD hE).s ⊆
      rationalOpen D.T D.s :=
  D.interDatum_subset_left E hD.span_eq_top hE.span_eq_top

theorem RationalLocData.interRational_subset_right [PlusSubring A] (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interRational E hD hE).T (D.interRational E hD hE).s ⊆
      rationalOpen E.T E.s :=
  D.interDatum_subset_right E hD.span_eq_top hE.span_eq_top

/-- **Regression (handover R1 exit criterion — different pairs of definition):** the
intersection datum exists for data with *unrelated* pairs; no `E.P = D.P` hypothesis is
required or used (compare `interSamePair`, which demands it). -/
example (D E : RationalLocData A) (hD : D.IsRational) (hE : E.IsRational)
    (_ : D.P ≠ E.P) : RationalLocData A :=
  D.interRational E hD hE

end Tate

/-! ### R3: the compatibility bridge -/

section Compatibility

variable [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **All-raw-data compatibility** — agreement after restriction to *every* raw datum
contained in both pieces. This is verbatim the hypothesis shape of the legacy
`IsSheafy.gluing` field (the strongest-looking condition; the legacy adapter). -/
def RationalCoveringData.AllDataCompatible (C : RationalCoveringData A)
    (f : ∀ D : ↥C.covers, presheafValue D.1) : Prop :=
  ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
    restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)

/-- **Valid-rational-refinement compatibility** — agreement on every valid rational
common refinement (the literature's compatibility condition for Čech gluing). -/
def RationalCoveringData.RationalRefinementCompatible (C : RationalCoveringData A)
    (f : ∀ D : ↥C.covers, presheafValue D.1) : Prop :=
  ∀ (D₁ D₂ : ↥C.covers) (E : RationalLocData A), E.IsRational →
    ∀ (h₁ : rationalOpen E.T E.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₂ : rationalOpen E.T E.s ⊆ rationalOpen D₂.1.T D₂.1.s),
    restrictionMap D₁.1 E h₁ (f D₁) = restrictionMap D₂.1 E h₂ (f D₂)

variable [IsTateRing A]

/-- **Exact-intersection compatibility** — agreement on the chosen exact intersection
datum `interRational D₁ D₂` of each pair of pieces (whose rational open is *exactly*
`R(D₁) ∩ R(D₂)`, `interRational_rationalOpen`). -/
def RationalCoveringData.ExactIntersectionCompatible (C : RationalCoveringData A)
    (hC : C.IsRational) (f : ∀ D : ↥C.covers, presheafValue D.1) : Prop :=
  ∀ (D₁ D₂ : ↥C.covers),
    restrictionMap D₁.1 (D₁.1.interRational D₂.1 (hC.piece D₁.2) (hC.piece D₂.2))
      (RationalLocData.interRational_subset_left _ _ _ _) (f D₁) =
    restrictionMap D₂.1 (D₁.1.interRational D₂.1 (hC.piece D₁.2) (hC.piece D₂.2))
      (RationalLocData.interRational_subset_right _ _ _ _) (f D₂)

theorem RationalCoveringData.AllDataCompatible.rationalRefinement
    {C : RationalCoveringData A} {f : ∀ D : ↥C.covers, presheafValue D.1}
    (hf : C.AllDataCompatible f) : C.RationalRefinementCompatible f :=
  fun D₁ D₂ E _ h₁ h₂ => hf D₁ D₂ E h₁ h₂

theorem RationalCoveringData.RationalRefinementCompatible.exactIntersection
    {C : RationalCoveringData A} (hC : C.IsRational)
    {f : ∀ D : ↥C.covers, presheafValue D.1}
    (hf : C.RationalRefinementCompatible f) : C.ExactIntersectionCompatible hC f :=
  fun D₁ D₂ => hf D₁ D₂ _
    (RationalLocData.interRational_isRational _ _ (hC.piece D₁.2) (hC.piece D₂.2)) _ _

/-- **The bridge, hard direction** (handover R3): exact-intersection compatibility
implies all-raw-data compatibility — the restriction to any raw common refinement `D₃`
factors through the exact intersection `I` (`R(D₃) ⊆ R(D₁) ∩ R(D₂) = R(I)`), so the two
direct restrictions are the `I`-restrictions of the agreeing values
(`restrictionMap_comp` + proof irrelevance of the containment witnesses). The raw-data
restriction infrastructure is confined to this legacy adapter. -/
theorem RationalCoveringData.ExactIntersectionCompatible.allData
    {C : RationalCoveringData A} (hC : C.IsRational)
    {f : ∀ D : ↥C.covers, presheafValue D.1}
    (hf : C.ExactIntersectionCompatible hC f) : C.AllDataCompatible f := by
  intro D₁ D₂ D₃ h₃₁ h₃₂
  set I := D₁.1.interRational D₂.1 (hC.piece D₁.2) (hC.piece D₂.2) with hI
  have h₃I : rationalOpen D₃.T D₃.s ⊆ rationalOpen I.T I.s := by
    rw [hI, RationalLocData.interRational_rationalOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hIL : rationalOpen I.T I.s ⊆ rationalOpen D₁.1.T D₁.1.s :=
    RationalLocData.interRational_subset_left _ _ _ _
  have hIR : rationalOpen I.T I.s ⊆ rationalOpen D₂.1.T D₂.1.s :=
    RationalLocData.interRational_subset_right _ _ _ _
  have c₁ := congr_fun (restrictionMap_comp D₁.1 I D₃ hIL h₃I) (f D₁)
  have c₂ := congr_fun (restrictionMap_comp D₂.1 I D₃ hIR h₃I) (f D₂)
  simp only [Function.comp_apply] at c₁ c₂
  calc restrictionMap D₁.1 D₃ h₃₁ (f D₁)
      = restrictionMap I D₃ h₃I (restrictionMap D₁.1 I hIL (f D₁)) := c₁.symm
    _ = restrictionMap I D₃ h₃I (restrictionMap D₂.1 I hIR (f D₂)) := by
        rw [hf D₁ D₂]
    _ = restrictionMap D₂.1 D₃ h₃₂ (f D₂) := c₂

/-- **The R3 bridge, hypothesis-clean form** (handover R3 exit criterion): for a
rational covering of a Tate ring, all-raw-data, valid-rational-refinement, and
exact-intersection compatibility coincide. In particular the legacy `IsSheafy.gluing`
input is equivalent to the literature's valid-refinement condition. -/
theorem RationalCoveringData.allDataCompatible_iff_rationalRefinementCompatible
    {C : RationalCoveringData A} (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1) :
    C.AllDataCompatible f ↔ C.RationalRefinementCompatible f :=
  ⟨fun hf => hf.rationalRefinement,
   fun hf => ((hf.exactIntersection hC)).allData hC⟩

theorem RationalCoveringData.rationalRefinementCompatible_iff_exactIntersectionCompatible
    {C : RationalCoveringData A} (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1) :
    C.RationalRefinementCompatible f ↔ C.ExactIntersectionCompatible hC f :=
  ⟨fun hf => hf.exactIntersection hC,
   fun hf => (hf.allData hC).rationalRefinement⟩

theorem RationalCoveringData.allDataCompatible_iff_exactIntersectionCompatible
    {C : RationalCoveringData A} (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1) :
    C.AllDataCompatible f ↔ C.ExactIntersectionCompatible hC f :=
  (C.allDataCompatible_iff_rationalRefinementCompatible hC f).trans
    (C.rationalRefinementCompatible_iff_exactIntersectionCompatible hC f)

end Compatibility

end ValuationSpectrum
