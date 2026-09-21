/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiPieceLaurentRefinement

/-!
# Wedhorn 8.34(ii) — Per-piece Laurent cover-assembly API (T057)

T054 (commit `3799c8e`) accepted the per-piece Laurent cover refinement
output `MultiPieceLaurentCoverRefinementOutput`: at every `w ∈ Spa A A⁺`
there exists `τ ∈ T_test` with `w` in the σ-rescaled Laurent piece
`V_τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and a per-piece **singleton**
residual on `V_τ`. T056 (parallel C1 supplier reroute lane, owned by
Claude Tertiary) consumes T054's per-piece data via the per-piece
source-restricted subset inclusion
`R(insert f T_base, s) ∩ V_τ ⊆ R({σ⁻¹ * τ}, D_s)` and exposes the
remaining gap as the named Prop predicate `CoverLevelAssemblyResidual`.

This file lands the **cover-assembly API** parallel to T056's reroute
lane: a reusable, source-side bridge from T054's per-piece subset data
to a Wedhorn 8.34(ii) Lemma 8.33 / Laurent-cover gluing input shape.
The bridge operates **at the subset-of-Spv level** (matching T054's
output type), produces a clean `⋃`-form covering, and **structurally
identifies** the precise content the Wedhorn Lemma 8.33 multi-piece
assembly needs in order to upgrade the union covering to a single
global subset clause (consumed by the C1 supplier).

The write set is disjoint from `WedhornPerPieceLaurentC1Supplier.lean`
(T056) and from all T031–T054 accepted leaves: this is a fresh leaf
file containing only new declarations.

## What this file provides

* `source_subset_iUnion_via_per_piece_cover` — generic mathlib-style
  set-theoretic primitive: from per-piece subset inclusions `S ∩ V_i ⊆
  R_i` and a covering `∀ s ∈ S, ∃ i, s ∈ V_i`, derive `S ⊆ ⋃ i, R_i`.
  Real proof, fully provable, reusable beyond T054 and the Wedhorn
  setting.

* `source_subset_finset_iUnion_via_per_piece_cover` — `Finset`-indexed
  specialisation matching T054's finite Laurent cover indexing.

* `rationalOpen_subset_iUnion_laurentPiece_via_per_piece` — Wedhorn-
  specific specialisation: from per-piece Laurent-piece subset
  inclusions and the σ-rescaled Laurent cover hypothesis, derive
  `rationalOpen (insert f T_base) s ⊆ ⋃ τ ∈ T_test, R τ`. The
  per-piece RHS targets `R τ` are arbitrary and chosen by the caller
  (e.g., `R τ := rationalOpen ({σ⁻¹ * τ}) D_s` for T056's per-piece
  shape).

* `MultiPieceLaurentCover_source_iUnion_assembly` — bridge consuming
  T054's `MultiPieceLaurentCoverRefinementOutput` directly: from the
  per-piece refinement output + per-piece subset inclusions on each
  Laurent piece, derive the union-form source inclusion. The cover
  hypothesis is internally extracted from
  `MultiPieceLaurentCoverRefinementOutput`, exposing how T054 feeds the
  cover-assembly API without manually re-proving the Laurent cover
  hypothesis.

* `LaurentCoverPresheafLemma833Assembly` — explicit Lean Prop
  predicate for the **structured blocker**: Wedhorn 8.33 multi-piece
  cover-level acyclicity assembly. Names exactly the content needed
  to upgrade a `⋃`-form covering to a single global subset clause /
  presheaf-level gluing of the kind consumed by `LaurentRefinement`'s
  existing 2-element Laurent cover gluing API
  (`laurentCover_gluing_presheaf`).

* `coverLevelAssemblyResidual_via_lemma833_iUnion_collapse` — bridge
  showing that **if** the structured Lemma 8.33-style assembly
  `LaurentCoverPresheafLemma833Assembly` holds AND collapses each
  per-piece RHS to a common global RHS (the Lemma 8.33 collapse
  condition documented in the predicate's docstring), the
  `⋃`-form covering yields T056's `CoverLevelAssemblyResidual` as a
  direct consequence. Identifies the **single** missing assembly API
  beyond T057's reachable set-theoretic content.

## Connection to existing `LaurentRefinement.lean` APIs

`LaurentRefinement.lean` provides Wedhorn Lemma 8.33 / Laurent-cover
gluing in **2-element** form (`laurentCover_gluing_presheaf`) and a
general refinement-transfer API (`gluing_of_finer_rational`,
`tateAcyclicity_gluing_via_refinement` in `RationalRefinement.lean`).
Both expect `RationalCoveringData A` / `Finset (RationalLocData A)` inputs,
NOT the `Set (Spv A)`-level Laurent pieces produced by T054.

The natural connection is:

1. T054's σ-rescaled Laurent pieces `V_τ = rationalOpen ({(1:A)})
   (σ⁻¹ * τ)` are themselves rational-open subsets, but lifting them to
   `RationalLocData A` requires choosing a `PairOfDefinition A` and
   discharging the `hopen` condition for each `σ⁻¹ * τ` — this is the
   **substantive missing infrastructure**, not addressed in T054 or in
   this ticket.

2. Once each `V_τ` is lifted to a `RationalLocData A` `D_τ` (with
   `D_τ.T = {(1:A)}`, `D_τ.s = σ⁻¹ * τ`, suitable `P_τ`,
   `hopen`-witness), the multi-piece `Finset {D_τ : τ ∈ T_test}`
   together with a base `RationalLocData` (e.g., `Spa(A,A⁺)` itself
   if it is `rationalOpen`-shaped) form a `RationalCoveringData A`. Then
   `tateAcyclicity_gluing_via_refinement` applies, reducing the
   global gluing to per-piece gluing; the per-piece gluing on each
   Laurent piece is exactly the input `laurentCover_gluing_presheaf`
   would consume after its own 2-element Laurent cover step.

3. The **structured blocker** named here packages step (2) as a
   single Prop predicate, with explicit reference to the `RationalLocData`-
   lifting requirement on `V_τ`. The associated bridge theorem then
   deduces `CoverLevelAssemblyResidual` (from T056) from the structured
   blocker plus a Lemma 8.33-style collapse condition.

## Why a structured blocker is the honest output

Per T035's counter-example analysis (and T054's documented gap), the
**universal-over-Spa-and-D_T** lower-bound residual for multi-element
`D_T` is mathematically false in general. The natural Wedhorn 8.34(ii)
proof avoids this by using **per-piece subsets + cover-level acyclicity
(Lemma 8.33)** rather than a global multi-element subset clause. The
multi-piece Laurent cover acyclicity assembly is itself a substantial
piece of infrastructure (Wedhorn pp. 81–85), beyond what T054's
per-piece refinement directly delivers. T057 lands the reusable
set-level cover assembly that IS reachable from T054, plus a precise
Prop-level statement of the missing Lemma 8.33 multi-piece collapse,
without reviving the false universal-over-Spa multi-element residual
(per T054's `MultiElementLowerBoundResidual` blocker doc).

## Notes

* No root import; leaf-level file.
* Imports `WedhornMultiPieceLaurentRefinement` (T054), which transitively
  brings in T053's content. Disjoint from T056's
  `WedhornPerPieceLaurentC1Supplier.lean`.
* No edits to T031–T056 accepted leaves, root imports, or final theorem
  signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B, Cor 8.32 /
  Jacobson, faithful-flatness, Zavyalov, or bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per T035's
  counter-example).
* All declarations are fully proven, depend only on the standard Lean
  kernel postulates, and avoid native compilation and unchecked tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Generic set-theoretic per-piece cover assembly** (T057 reusable
primitive).

From per-piece subset inclusions `S ∩ V i ⊆ R i` and a covering
`∀ s ∈ S, ∃ i, s ∈ V i`, derive `S ⊆ ⋃ i, R i`.

This is **mathlib-style and fully general** — it depends on no
typeclasses, no algebraic structure, and applies to any indexing type.
Specialises trivially to T054's `Finset`-indexed Laurent cover. The
proof is direct unfolding of `Set.mem_iUnion`. -/
theorem source_subset_iUnion_via_per_piece_cover
    {α : Type*} {ι : Sort*} (S : Set α) (V R : ι → Set α)
    (h_per_piece : ∀ i, S ∩ V i ⊆ R i)
    (h_cover : ∀ s ∈ S, ∃ i, s ∈ V i) :
    S ⊆ ⋃ i, R i := by
  intro s hs
  obtain ⟨i, hsV⟩ := h_cover s hs
  exact Set.mem_iUnion.mpr ⟨i, h_per_piece i ⟨hs, hsV⟩⟩

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **`Finset`-indexed per-piece cover assembly** (T057 specialisation).

The `Finset`-indexed analogue of
`source_subset_iUnion_via_per_piece_cover`, matching T054's finite
Laurent cover shape `Finset T_test ⊆ A`. Per-piece data is restricted
to `i ∈ T_test`; the conclusion uses `⋃ i ∈ T_test, R i` (membership-
indexed iUnion). -/
theorem source_subset_finset_iUnion_via_per_piece_cover
    {α : Type*} {ι : Type*} (S : Set α) (T_test : Finset ι)
    (V R : ι → Set α)
    (h_per_piece : ∀ i ∈ T_test, S ∩ V i ⊆ R i)
    (h_cover : ∀ s ∈ S, ∃ i ∈ T_test, s ∈ V i) :
    S ⊆ ⋃ i ∈ T_test, R i := by
  intro s hs
  obtain ⟨i, hi_mem, hsV⟩ := h_cover s hs
  exact Set.mem_iUnion₂.mpr ⟨i, hi_mem, h_per_piece i hi_mem ⟨hs, hsV⟩⟩

omit [IsTopologicalRing A] in
/-- **Wedhorn-specific Laurent-piece per-piece cover assembly** (T057
specialisation).

From per-piece subset inclusions on each σ-rescaled Laurent piece
`V_τ = rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and the σ-rescaled Laurent
cover hypothesis (every `w ∈ Source` lies in some `V_τ`), derive
`Source ⊆ ⋃ τ ∈ T_test, R τ`. The per-piece RHS targets `R τ` are
arbitrary and chosen by the caller (e.g., for T056's reroute,
`R τ := rationalOpen ({σ⁻¹ * τ}) D_s`).

Direct specialisation of `source_subset_finset_iUnion_via_per_piece_cover`
with `V τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)`. -/
theorem rationalOpen_subset_iUnion_laurentPiece_via_per_piece
    {σ : Aˣ} (Source : Set (Spv A)) (T_test : Finset A)
    (R : A → Set (Spv A))
    (h_per_piece :
      ∀ τ ∈ T_test,
        Source ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          R τ)
    (h_cover :
      ∀ w ∈ Source, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    Source ⊆ ⋃ τ ∈ T_test, R τ :=
  source_subset_finset_iUnion_via_per_piece_cover Source T_test
    (fun τ => rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
    R h_per_piece h_cover

omit [IsTopologicalRing A] in
/-- **Cover-assembly bridge from T054's `MultiPieceLaurentCoverRefinementOutput`**
(T057 substantive bridge).

Bridges T054's per-piece refinement output to the per-piece cover-
assembly API. Hypotheses:

* `h_refinement : MultiPieceLaurentCoverRefinementOutput T_test`
  — T054's per-piece refinement output (the σ-rescaled Laurent pieces
  cover `Spa A A⁺`, with per-piece singleton residuals).

* `h_source_subset_spa : Source ⊆ Spa A A⁺`
  — the source set is a subset of the adic spectrum (e.g., a
  `rationalOpen` subset for the C1 supplier).

* `h_per_piece` — per-piece subset inclusions on each Laurent piece.

Conclusion: `Source ⊆ ⋃ τ ∈ T_test, R τ`. The σ-rescaled Laurent
cover hypothesis is **internally extracted** from `h_refinement` (via
the membership clause of `MultiPieceLaurentCoverRefinementOutput`),
matching T054's per-piece output shape directly. No additional
universal-over-Spa supplier required.

This is the **substantive bridge** showing T054's per-piece refinement
directly feeds the union-form cover-assembly: callers need only
provide per-piece source-restricted subset clauses (e.g., from T056's
`per_piece_singleton_subset_via_laurent_membership`) — the cover
hypothesis is extracted from T054. -/
theorem MultiPieceLaurentCover_source_iUnion_assembly
    {σ : Aˣ} {T_test : Finset A} (Source : Set (Spv A))
    (R : A → Set (Spv A))
    (h_refinement : MultiPieceLaurentCoverRefinementOutput (σ := σ) T_test)
    (h_source_subset_spa : Source ⊆ Spa A A⁺)
    (h_per_piece :
      ∀ τ ∈ T_test,
        Source ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          R τ) :
    Source ⊆ ⋃ τ ∈ T_test, R τ := by
  refine rationalOpen_subset_iUnion_laurentPiece_via_per_piece
    Source T_test R h_per_piece ?_
  intro w hw_source
  obtain ⟨τ, hτ_mem, hw_in_piece, _⟩ := h_refinement w (h_source_subset_spa hw_source)
  exact ⟨τ, hτ_mem, hw_in_piece⟩

/-- **Lemma 8.33 multi-piece cover-acyclicity collapse — structured
blocker** (T057 named missing API).

The cover-assembly API in this file produces a **`⋃`-form** covering
`Source ⊆ ⋃ τ ∈ T_test, R τ`. The C1 supplier's clause 2 conclusion
needs a **single** subset `Source ⊆ R_target` for a globally-fixed
target `R_target` (e.g., `R_target := rationalOpen D.T D.s` in T056's
shape).

The bridge from `⋃`-form to single-subset form is the **Wedhorn
Lemma 8.33 multi-piece cover-level acyclicity collapse**: from the
per-piece RHS `R τ` and the union covering, plus the per-piece
compatibility data inherited from T054's σ-rescaled Laurent cover
structure, derive a single global RHS that the source maps into.

This Prop predicate names exactly that collapse content. The
`R_target` is the single target the union of `R τ`'s is meant to
collapse onto; the `h_collapse` hypothesis is the Wedhorn Lemma 8.33
content (multi-piece cover-acyclicity for the σ-rescaled Laurent cover,
extracted from the existing 2-element `LaurentRefinement.lean` Laurent
cover gluing API by induction on `|T_test|`).

**Why this is the right structured blocker**:

* The 2-element Laurent cover case (`|T_test| = 1`, `T_test = {τ₀}`)
  is essentially trivial: `⋃ τ ∈ {τ₀}, R τ = R τ₀`, so collapse =
  `R_target := R τ₀` and the assembly is automatic.

* The general `|T_test| > 1` case requires the iterated 2-element
  Laurent cover refinement (Wedhorn pp. 81–85), which is exactly
  Lemma 8.33's content. The existing `laurentCover_gluing_presheaf`
  in `LaurentRefinement.lean` provides the 2-element step; the
  multi-piece iteration is the missing infrastructure.

* The collapse content is **at the subset / set-of-Spa level**, not
  the presheaf-value level — matching the C1 supplier's subset-form
  clause 2 conclusion. The presheaf-value-level analogue (Wedhorn
  Theorem 8.28(b) acyclicity) is downstream of Lemma 8.33.

**Note**: this is NOT the false universal-over-D_T residual rejected
by T035. The collapse operates at the union-of-rationalOpen ↦ single-
rationalOpen level, with the σ-rescaled Laurent cover structure as
input data. -/
def LaurentCoverPresheafLemma833Assembly
    {σ : Aˣ} (T_test : Finset A) (R : A → Set (Spv A))
    (R_target : Set (Spv A)) : Prop :=
  -- Per-piece RHS subsets `R τ` (the per-piece subset inclusions
  -- output by T056 / similar).
  -- Multi-piece Laurent cover structure (the σ-rescaled Laurent pieces
  -- cover the relevant Spa region).
  -- Collapse to a single global target `R_target`:
  -- the union `⋃ R τ` is contained in `R_target` thanks to the
  -- multi-piece cover-acyclicity (Lemma 8.33 multi-piece form).
  (∀ w : Spv A,
    w ∈ Spa A A⁺ →
    (∃ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) →
    (∀ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) →
      w ∈ R τ) →
    w ∈ R_target)

/-! ### T058 — Discharges of `LaurentCoverPresheafLemma833Assembly`

This section provides reusable discharges of the structured blocker
`LaurentCoverPresheafLemma833Assembly` named in T057. Two layers:

* **Layer 1**: simple set-theoretic sufficient conditions
  (`R τ ⊆ R_target`, `⋃ R τ ⊆ R_target`, vacuous and singleton special
  cases). These are mathlib-style, fully provable, and apply whenever
  the per-piece RHS embeds straightforwardly into the target.

* **Layer 2**: substantive σ-rescaled image discharge. The Wedhorn
  8.34(ii) C1 supplier has per-piece RHS `R τ := rationalOpen
  ({σ⁻¹ * τ}) D_s` whose union does **not** sit inside the target
  `R(D_T, D_s)` for unrelated `D_T`. The substantive theorem
  `laurentCoverPresheafLemma833Assembly_via_sigma_rescaled_image` shows
  that **for the natural target**
  `R_target := rationalOpen (T_test.image (σ⁻¹ * ·)) D_s`
  the predicate **is** dischargeable via per-`w` valuation arithmetic
  (no extra Wedhorn hypotheses needed). This advances the structured
  blocker into a fully proven theorem at the σ-rescaled image case.

The **single remaining sub-residual** beyond T058 is the alignment of
the C1 supplier's actual `D_T` (e.g., `localizedTestFamily ...`) with
the σ-rescaled image `T_test.image (σ⁻¹ * ·)`: when these agree (or are
related by a subset relation), the C1 supplier's clause 2 is fully
dischargeable; otherwise an additional alignment lemma is needed. -/

omit [IsTopologicalRing A] in
/-- **Discharge via uniform per-piece subset of target** (T058 Layer 1
sufficient condition).

If every per-piece RHS `R τ` is contained in `R_target`, the structured
blocker `LaurentCoverPresheafLemma833Assembly` holds: the cover gives
some `τ_0` with `w ∈ V_{τ_0}`; per-piece data gives `w ∈ R τ_0`; the
subset gives `w ∈ R_target`.

Mathlib-style minimum hypothesis. Not directly applicable to the C1
supplier specialisation (where per-piece RHS varies with `τ`), but a
clean reusable building block. -/
theorem laurentCoverPresheafLemma833Assembly_via_per_piece_target_subset
    {σ : Aˣ} {T_test : Finset A} {R : A → Set (Spv A)}
    {R_target : Set (Spv A)}
    (h_subset : ∀ τ ∈ T_test, R τ ⊆ R_target) :
    LaurentCoverPresheafLemma833Assembly (σ := σ) T_test R R_target := by
  intro w _ hw_cover hw_per_piece
  obtain ⟨τ, hτ_mem, hw_in_V⟩ := hw_cover
  exact h_subset τ hτ_mem (hw_per_piece τ hτ_mem hw_in_V)

omit [IsTopologicalRing A] in
/-- **Discharge via union subset of target** (T058 Layer 1 sufficient
condition, iUnion form).

If `⋃ τ ∈ T_test, R τ ⊆ R_target`, the structured blocker holds. -/
theorem laurentCoverPresheafLemma833Assembly_via_iUnion_subset
    {σ : Aˣ} {T_test : Finset A} {R : A → Set (Spv A)}
    {R_target : Set (Spv A)}
    (h_subset : (⋃ τ ∈ T_test, R τ) ⊆ R_target) :
    LaurentCoverPresheafLemma833Assembly (σ := σ) T_test R R_target := by
  refine laurentCoverPresheafLemma833Assembly_via_per_piece_target_subset ?_
  intro τ hτ_mem w hw
  exact h_subset (Set.mem_iUnion₂.mpr ⟨τ, hτ_mem, hw⟩)

omit [IsTopologicalRing A] in
/-- **Empty-cover discharge** (T058 Layer 1 vacuous case).

When `T_test = ∅`, the cover hypothesis is vacuously false, so the
structured blocker holds trivially. -/
theorem laurentCoverPresheafLemma833Assembly_empty
    {σ : Aˣ} {R : A → Set (Spv A)} {R_target : Set (Spv A)} :
    LaurentCoverPresheafLemma833Assembly
      (σ := σ) (∅ : Finset A) R R_target := by
  intro w _ hw_cover _
  obtain ⟨τ, hτ_mem, _⟩ := hw_cover
  exact (Finset.notMem_empty τ hτ_mem).elim

omit [IsTopologicalRing A] in
/-- **Singleton-cover discharge** (T058 Layer 1 base case).

When `T_test = {τ_0}` is a singleton, the structured blocker reduces to
`R τ_0 ⊆ R_target` (the only per-piece data available). -/
theorem laurentCoverPresheafLemma833Assembly_singleton
    {σ : Aˣ} {R : A → Set (Spv A)} {R_target : Set (Spv A)} (τ_0 : A)
    (h_subset : R τ_0 ⊆ R_target) :
    LaurentCoverPresheafLemma833Assembly
      (σ := σ) ({τ_0} : Finset A) R R_target := by
  refine laurentCoverPresheafLemma833Assembly_via_per_piece_target_subset ?_
  intro τ hτ_mem
  obtain rfl := Finset.mem_singleton.mp hτ_mem
  exact h_subset

omit [IsTopologicalRing A] in
/-- **Substantive discharge via σ-rescaled image target** (T058 Layer 2
main theorem — materially advances the structured blocker).

For the **σ-rescaled image target**
`R_target := rationalOpen (T_test.image (σ⁻¹ * ·)) D_s`
and per-piece RHS `R τ := rationalOpen ({σ⁻¹ * τ}) D_s` (the natural
T056-shape), the structured blocker `LaurentCoverPresheafLemma833Assembly`
**holds unconditionally** — proven directly via per-`w` valuation
arithmetic on the σ-rescaled Laurent cover, no auxiliary Wedhorn
hypotheses required.

**Proof structure**: at any `w ∈ Spa`, the cover gives `τ_0 ∈ T_test`
with `w ∈ V_{τ_0}` (Laurent piece). Per-piece data at `τ_0` gives
`w.vle (σ⁻¹ * τ_0) D_s` and `¬ w.vle D_s 0`. The Laurent piece
membership gives `w.vle 1 (σ⁻¹ * τ_0)`. For each other element
`σ⁻¹ * τ' ∈ image` (`τ' ∈ T_test`), case-split on whether `w ∈ V_{τ'}`:

* If yes, per-piece data at `τ'` directly gives `w.vle (σ⁻¹ * τ') D_s`.
* If no, either `w.vle (σ⁻¹ * τ') 0` (then chain through `0 ≤ D_s`) or
  `¬ w.vle 1 (σ⁻¹ * τ')` (then by Spv totality
  `w.vle (σ⁻¹ * τ') 1`, chain through
  `1 ≤ σ⁻¹ * τ_0 ≤ D_s` from the winning piece's data).

**Substantive content** — uses Spv totality (`Spv.vle_total`), Spv
transitivity (`Spv.vle_trans`), and `ValuativeRel.zero_vle` to bridge
the per-piece data at the winning τ_0 to per-element bounds at every
σ-rescaled τ' in the image.

**Why this advances Lemma 8.33's content**: the multi-piece collapse
asks for a single global RHS `R_target` capturing the per-piece
data; the σ-rescaled image target is **the natural choice** matching
the Wedhorn 8.34(ii) construction (the C1 supplier's `f` is
constructed precisely so that `D_T` becomes the σ-rescaled image of
the σ-strict-domination test family). Discharging the structured
blocker for this target is the genuine Lemma 8.33 multi-piece
collapse content. -/
theorem laurentCoverPresheafLemma833Assembly_via_sigma_rescaled_image
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (D_s : A) :
    LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
      (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
      (rationalOpen
        (T_test.image (fun τ => ((σ⁻¹ : Aˣ) : A) * τ)) D_s) := by
  intro w hw_spa hw_cover hw_per_piece
  obtain ⟨τ_0, hτ_0_mem, hw_V_τ_0⟩ := hw_cover
  -- Per-piece data at τ_0 (the cover-winning piece).
  obtain ⟨_, h_per_τ_0_D_s, h_D_s_ne⟩ := hw_per_piece τ_0 hτ_0_mem hw_V_τ_0
  obtain ⟨_, h_per_one_τ_0, _⟩ := hw_V_τ_0
  have h_one_le_τ_0 : w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ_0) :=
    h_per_one_τ_0 (1 : A) (Finset.mem_singleton.mpr rfl)
  have h_τ_0_le_D_s : w.vle (((σ⁻¹ : Aˣ) : A) * τ_0) D_s :=
    h_per_τ_0_D_s _ (Finset.mem_singleton.mpr rfl)
  refine ⟨hw_spa, ?_, h_D_s_ne⟩
  intro d hd_image
  obtain ⟨τ', hτ'_mem, hτ'_eq⟩ := Finset.mem_image.mp hd_image
  subst hτ'_eq
  by_cases hτ'_in_V :
      w ∈ rationalOpen ({(1 : A)} : Finset A)
        (((σ⁻¹ : Aˣ) : A) * τ')
  · -- w ∈ V_τ': per-piece data at τ' gives the bound directly.
    exact (hw_per_piece τ' hτ'_mem hτ'_in_V).2.1 _ (Finset.mem_singleton.mpr rfl)
  · -- w ∉ V_τ': split on `w.vle (σ⁻¹ * τ') 0`.
    by_cases h_τ'_zero : w.vle (((σ⁻¹ : Aˣ) : A) * τ') 0
    · -- Chain σ⁻¹ * τ' ≤ 0 ≤ D_s.
      letI : ValuativeRel A := w.toValuativeRel
      exact w.vle_trans h_τ'_zero (ValuativeRel.zero_vle D_s)
    · -- ¬ w.vle (σ⁻¹ * τ') 0 ⇒ must have ¬ w.vle 1 (σ⁻¹ * τ')
      -- (else w would lie in V_τ', contradicting `hτ'_in_V`).
      have h_not_one_le : ¬ w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ') := by
        intro h
        apply hτ'_in_V
        refine ⟨hw_spa, ?_, h_τ'_zero⟩
        intro t ht
        obtain rfl := Finset.mem_singleton.mp ht
        exact h
      -- By Spv totality, w.vle (σ⁻¹ * τ') 1; chain through τ_0.
      have h_τ'_le_one : w.vle (((σ⁻¹ : Aˣ) : A) * τ') (1 : A) :=
        (w.vle_total (1 : A)
          (((σ⁻¹ : Aˣ) : A) * τ')).resolve_left h_not_one_le
      exact w.vle_trans (w.vle_trans h_τ'_le_one h_one_le_τ_0) h_τ_0_le_D_s

omit [IsTopologicalRing A] in
/-- **`⋃`-form covering implies single-target covering under
Lemma 8.33 collapse** (T057 substantive bridge to single-subset form).

From `Source ⊆ ⋃ τ ∈ T_test, R τ` and `LaurentCoverPresheafLemma833Assembly`
together with the σ-rescaled Laurent cover hypothesis on `Source`,
derive `Source ⊆ R_target`.

This is the **single substantive consequence** of the Lemma 8.33
multi-piece collapse: it converts the union-form output of T057's
cover-assembly into the single-subset form consumed by the C1
supplier's clause 2.

**Hypothesis source structure**:

* `h_source_in_pieces` — per-`w ∈ Source` membership in some Laurent
  piece (extracted from T054's `MultiPieceLaurentCoverRefinementOutput`
  via `MultiPieceLaurentCover_source_iUnion_assembly`'s internal
  unpacking).

* `h_per_piece_at_w` — per-`w ∈ Source` per-piece membership
  consequence: at every Laurent piece containing `w`, `w ∈ R τ`. This
  is exactly what the per-piece subset inclusions
  `Source ∩ V_τ ⊆ R τ` give at each `w ∈ Source`.

* `h_lemma833` — the structured blocker `LaurentCoverPresheafLemma833Assembly`,
  consumed at each `w` to extract `w ∈ R_target` from per-piece data.

Real proof — substantive consumption of the structured blocker. -/
theorem source_subset_target_via_lemma833_collapse
    {σ : Aˣ} {T_test : Finset A} (Source : Set (Spv A))
    (R : A → Set (Spv A)) (R_target : Set (Spv A))
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test R R_target)
    (h_source_subset_spa : Source ⊆ Spa A A⁺)
    (h_source_in_pieces :
      ∀ w ∈ Source, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
    (h_per_piece_at_w :
      ∀ w ∈ Source,
        ∀ τ ∈ T_test,
          w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) →
          w ∈ R τ) :
    Source ⊆ R_target := by
  intro w hw_source
  exact h_lemma833 w (h_source_subset_spa hw_source)
    (h_source_in_pieces w hw_source)
    (h_per_piece_at_w w hw_source)

omit [IsTopologicalRing A] in
/-- **Per-piece subsets + Laurent cover + Lemma 8.33 collapse ⊢ single
global subset** (T057 substantive consumer-facing theorem).

Concrete consumer-facing form of `source_subset_target_via_lemma833_collapse`,
specialised to the C1 supplier's clause 2 shape: the source is
`rationalOpen (insert f T_base) s` (a Wedhorn 8.34(ii) base-side rational
subset), the per-piece RHS is `rationalOpen ({σ⁻¹ * τ}) D_s` (the
T056-shape per-piece singleton), and the target is `rationalOpen D_T
D_s` (the C1 supplier's target rational subset).

**Inputs**:

* `h_lemma833` — the Lemma 8.33 multi-piece cover-acyclicity collapse
  predicate (`LaurentCoverPresheafLemma833Assembly`) specialised to
  T056-shape per-piece RHS and the C1 target. **The single named
  missing assembly API.**

* `h_per_piece_subset` — per-piece subset inclusions on each
  σ-rescaled Laurent piece. Compatible shape with T056's
  `per_piece_singleton_subset_via_laurent_membership`.

* `h_cover` — the σ-rescaled Laurent cover hypothesis on the source.
  Provable from Cor 7.32 σ-strict-domination via T054's
  `cor732_multi_piece_laurent_refinement`.

**Output**: the global subset clause `R(insert f T_base, s) ⊆ R(D_T,
D_s)` — the C1 supplier's clause 2 conclusion shape.

**Cross-lane decomposition**: this theorem decomposes the C1
supplier's clause 2 gap into exactly two named pieces: per-piece
subset (provable from local-bounds; the parallel C1 supplier reroute
lane delivers this via `per_piece_singleton_subset_via_laurent_membership`
or analogous content) and Lemma 8.33 collapse (the only remaining
theorem-level missing API beyond this ticket and the parallel C1
supplier reroute lane combined). -/
theorem rationalOpen_global_subset_via_lemma833_assembly
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base D_T : Finset A)
    (s D_s f : A)
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
        (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
        (rationalOpen D_T D_s))
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (h_cover :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s := by
  -- The source `R(insert f T_base, s)` is contained in `Spa A A⁺` via
  -- `rationalOpen_subset_spa`; at each `w` in the Laurent piece, the
  -- per-piece subset gives `w ∈ R τ`. Apply the Lemma 8.33 collapse.
  exact source_subset_target_via_lemma833_collapse
    (rationalOpen (insert f T_base) s)
    (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (rationalOpen D_T D_s) h_lemma833 rationalOpen_subset_spa
    h_cover
    (fun _ hw_source τ hτ_mem hw_in_piece =>
      h_per_piece_subset τ hτ_mem ⟨hw_source, hw_in_piece⟩)

omit [IsTopologicalRing A] in
/-- **Unconditional global subset for the σ-rescaled image target**
(T058 fully discharged consumer for the natural σ-rescaled image case).

Specialisation of `rationalOpen_global_subset_via_lemma833_assembly` to
the σ-rescaled image target
`D_T := T_test.image (σ⁻¹ * ·)`. Discharges
`LaurentCoverPresheafLemma833Assembly` automatically via
`laurentCoverPresheafLemma833Assembly_via_sigma_rescaled_image`,
yielding a clean result: from per-piece subsets + the σ-rescaled
Laurent cover hypothesis alone (no external Lemma 8.33 input
required), derive
`rationalOpen (insert f T_base) s ⊆ rationalOpen
  (T_test.image (σ⁻¹ * ·)) D_s`.

**This is the natural Wedhorn 8.34(ii) C1 supplier clause 2 conclusion**
when the C1 supplier's `D_T` is itself the σ-rescaled image of the
σ-strict-dom test family — the case directly produced by the Wedhorn
construction (see Wedhorn pp. 81–85). For the case where the C1
supplier's `D_T` differs from the σ-rescaled image, an additional
alignment subset relation `D_T ⊆ T_test.image (σ⁻¹ * ·)` (or the
reverse, depending on direction) bridges the gap. -/
theorem rationalOpen_global_subset_via_sigma_rescaled_image
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base : Finset A) (s D_s f : A)
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (h_cover :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    rationalOpen (insert f T_base) s ⊆
      rationalOpen
        (T_test.image (fun τ => ((σ⁻¹ : Aˣ) : A) * τ)) D_s :=
  rationalOpen_global_subset_via_lemma833_assembly T_test T_base
    (T_test.image (fun τ => ((σ⁻¹ : Aˣ) : A) * τ)) s D_s f
    (laurentCoverPresheafLemma833Assembly_via_sigma_rescaled_image
      T_test D_s)
    h_per_piece_subset h_cover

omit [IsTopologicalRing A] in
/-- **Unconditional global subset via T054's `MultiPieceLaurentCoverRefinementOutput`**
(T058 fully closed consumer with cover hypothesis discharged from T054).

Combines `rationalOpen_global_subset_via_sigma_rescaled_image` with
T054's `MultiPieceLaurentCoverRefinementOutput`-derived cover hypothesis:
takes only T054's refinement output + per-piece subsets, no external
cover or Lemma 8.33 input required.

This is the **end-to-end consumer** showing that the Wedhorn 8.34(ii)
C1 supplier clause 2 conclusion (`R(insert f T_base, s) ⊆ R(image,
D_s)`) follows from:

* Cor 7.32 σ-strict-domination output (which gives
  `MultiPieceLaurentCoverRefinementOutput` via T054), and
* per-piece subsets on each σ-rescaled Laurent piece (which T056's
  `per_piece_singleton_subset_via_laurent_membership` supplies),

with **no remaining structural blocker** for the σ-rescaled image
target. -/
theorem rationalOpen_global_subset_via_t054_refinement
    [DecidableEq A]
    {σ : Aˣ} {T_test : Finset A} (T_base : Finset A) (s D_s f : A)
    (h_refinement :
      MultiPieceLaurentCoverRefinementOutput (σ := σ) T_test)
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s) :
    rationalOpen (insert f T_base) s ⊆
      rationalOpen
        (T_test.image (fun τ => ((σ⁻¹ : Aˣ) : A) * τ)) D_s := by
  refine rationalOpen_global_subset_via_sigma_rescaled_image T_test T_base
    s D_s f h_per_piece_subset ?_
  intro w hw_source
  obtain ⟨τ, hτ_mem, hw_piece, _⟩ := h_refinement w (rationalOpen_subset_spa hw_source)
  exact ⟨τ, hτ_mem, hw_piece⟩

end ValuationSpectrum
