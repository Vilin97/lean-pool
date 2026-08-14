/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.SimplicialCompression
import LeanPool.BooleanIsoperimetry.LayerWindows

/-!
# Frankl-Furedi compression layer

This file formalizes paired compression and terminalization infrastructure for
families in the Boolean cube, connecting compressed families to canonical
simplicial initial segments.
-/

open scoped BigOperators
open scoped FinsetFamily
open Finset

namespace BooleanIsoperimetry

/-- A family of vertices is a simplicial initial segment if it equals the canonical
simplicial prefix of its cardinality. -/
def IsSimplicial {N : ℕ} (A : Finset (Cube N)) : Prop :=
  A = simplicialInitSeg N A.card

/-- The embedded two-slice family in `Q_{N+1}` whose lower slice is `A` and
upper slice is `B`. -/
noncomputable def embeddedPair (N : ℕ) (A B : Finset (Cube N)) : Finset (Cube (N + 1)) :=
  A.image embed0 ∪ B.image embed1

/-- `embed0` is injective.  Kept local to the paired-compression layer so the
embedded-pair slice lemmas do not depend on the later scalar bridge file. -/
lemma compression_embed0_injective {N : ℕ} : Function.Injective (@embed0 N) :=
  Finset.image_injective (Fin.castSucc_injective N)

/-- The top coordinate never lies in an `embed0` image. -/
lemma compression_last_not_mem_embed0 {N : ℕ} (x : Cube N) :
    Fin.last N ∉ embed0 x := by
  simp [embed0]

/-- `embed1` is injective. -/
lemma compression_embed1_injective {N : ℕ} : Function.Injective (@embed1 N) := by
  intro x y h
  unfold embed1 at h
  have key : x.image Fin.castSucc = y.image Fin.castSucc := by
    have := congrArg (·.erase (Fin.last N)) h
    simpa [Finset.erase_insert, compression_last_not_mem_embed0] using this
  exact Finset.image_injective (Fin.castSucc_injective N) key

/-- The lower slice of an embedded pair is exactly its first component. -/
lemma slice0_embeddedPair {N : ℕ} (A B : Finset (Cube N)) :
    slice0 (embeddedPair N A B) = A := by
  ext x
  simp only [slice0, embeddedPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, _hy, hxy⟩)
    · have hyx : y = x := compression_embed0_injective hxy
      simpa [← hyx] using hy
    · have hlast : Fin.last N ∈ embed1 y := by simp [embed1]
      rw [hxy] at hlast
      exact (compression_last_not_mem_embed0 x hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

/-- The upper slice of an embedded pair is exactly its second component. -/
lemma slice1_embeddedPair {N : ℕ} (A B : Finset (Cube N)) :
    slice1 (embeddedPair N A B) = B := by
  ext x
  simp only [slice1, embeddedPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, _hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := by simp [embed1]
      rw [← hxy] at hlast
      exact (compression_last_not_mem_embed0 y hlast).elim
    · have hyx : y = x := compression_embed1_injective hxy
      simpa [← hyx] using hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

/-- Exact neighborhood decomposition for an embedded two-slice family.  This is
the literal cardinality of the closed unit neighborhood in `Q_{N+1}`. -/
lemma neighborhood_embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    (neighborhood 1 (embeddedPair N A B)).card =
      (neighborhood 1 A ∪ B).card + (neighborhood 1 B ∪ A).card := by
  rw [neighborhood_succ, slice0_embeddedPair, slice1_embeddedPair]

lemma disjoint_embeddedPair {N : ℕ} (A B : Finset (Cube N)) :
    Disjoint (A.image embed0) (B.image embed1) := by
  rw [Finset.disjoint_left]
  intro x hx0 hx1
  rcases Finset.mem_image.mp hx0 with ⟨a, _ha, rfl⟩
  rcases Finset.mem_image.mp hx1 with ⟨b, _hb, hb⟩
  have hlast : Fin.last N ∈ embed1 b := by simp [embed1]
  rw [hb] at hlast
  exact compression_last_not_mem_embed0 a hlast

lemma embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    (embeddedPair N A B).card = A.card + B.card := by
  unfold embeddedPair
  rw [Finset.card_union_of_disjoint (disjoint_embeddedPair A B)]
  rw [Finset.card_image_of_injective _ compression_embed0_injective,
      Finset.card_image_of_injective _ compression_embed1_injective]

lemma embeddedPair_eq_of_slice_eq {N : ℕ} {A : Finset (Cube (N + 1))} {P Q : Finset (Cube N)}
    (h0 : slice0 A = P) (h1 : slice1 A = Q) :
    A = embeddedPair N P Q := by
  have h_sub : embeddedPair N (slice0 A) (slice1 A) ⊆ A := by
    intro x hx
    unfold embeddedPair at hx
    rw [Finset.mem_union] at hx
    cases hx with
    | inl h0 =>
      rw [Finset.mem_image] at h0
      rcases h0 with ⟨y, hy, hyx⟩
      unfold slice0 at hy
      rw [Finset.mem_filter] at hy
      rw [← hyx]
      exact hy.2
    | inr h1 =>
      rw [Finset.mem_image] at h1
      rcases h1 with ⟨y, hy, hyx⟩
      unfold slice1 at hy
      rw [Finset.mem_filter] at hy
      rw [← hyx]
      exact hy.2
  have h_card : (embeddedPair N (slice0 A) (slice1 A)).card = A.card := by
    rw [embeddedPair_card, slice_card_add]
  have hA : A = embeddedPair N (slice0 A) (slice1 A) :=
    (Finset.eq_of_subset_of_card_le h_sub (by rw [h_card])).symm
  rw [h0, h1] at hA
  exact hA

/-- The Frankl-Füredi paired compression **slice lower-bound functional** for
two slices `A` and `B`.

For arbitrary slices this is not the literal cardinality of the embedded
family's neighborhood.  The true cardinality has union terms
`|N(A) ∪ B| + |N(B) ∪ A|`; this functional replaces each union by the cheaper
lower bound `max |N(A)| |B|`.  For nested/canonical terminal pairs the two
coincide. -/
noncomputable def PairShadowCost (N : ℕ) (A B : Finset (Cube N)) : ℕ :=
  max (neighborhood 1 A).card B.card + max (neighborhood 1 B).card A.card

/-- The paired slice functional is a lower bound for the literal neighborhood
size of the embedded family. -/
lemma PairShadowCost_le_neighborhood_embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N A B ≤ (neighborhood 1 (embeddedPair N A B)).card := by
  rw [neighborhood_embeddedPair_card]
  unfold PairShadowCost
  have hA : max (neighborhood 1 A).card B.card ≤ (neighborhood 1 A ∪ B).card := by
    exact max_le (Finset.card_le_card (by intro x hx; exact Finset.mem_union_left _ hx))
      (Finset.card_le_card (by intro x hx; exact Finset.mem_union_right _ hx))
  have hB : max (neighborhood 1 B).card A.card ≤ (neighborhood 1 B ∪ A).card := by
    exact max_le (Finset.card_le_card (by intro x hx; exact Finset.mem_union_left _ hx))
      (Finset.card_le_card (by intro x hx; exact Finset.mem_union_right _ hx))
  exact Nat.add_le_add hA hB

/-- On canonical initial segments the paired slice functional is exactly the
scalar max expression used in the cascade recurrence. -/
lemma PairShadowCost_initSeg_eq_max_H {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) =
      max (H N a) b + max (H N b) a := by
  unfold PairShadowCost H
  rw [card_simplicialInitSeg, card_simplicialInitSeg, min_eq_left ha, min_eq_left hb]

/-- For canonical initial segments the literal embedded-neighborhood cardinality
also evaluates to the scalar max expression, because all four slice families are
nested initial segments. -/
lemma neighborhood_embeddedPair_initSeg_card {N a b : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (embeddedPair N (simplicialInitSeg N a) (simplicialInitSeg N b))).card =
      max (H N a) b + max (H N b) a := by
  rw [neighborhood_embeddedPair_card]
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union (H_le_cube N a) hb, card_initSeg_union (H_le_cube N b) ha]

/-- The family-level nesting predicate used by the terminal Frankl-Füredi
configuration: one slice is contained in the other.  Kept as descriptive
scaffolding for the geometric picture; it is intentionally **not** strong enough
on its own to pin down the canonical cascade pair (see `IsCanonicalCascadePair`),
so no theorem below claims a nested pair is automatically canonical. -/
def IsNestedPair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  A ⊆ B ∨ B ⊆ A

/-- A pair of families is *weakly terminal* for paired compression if they are
both simplicial and nested.  This is a necessary (not sufficient) feature of the
genuine terminal configuration: it does **not** by itself force `(A, B)` to be the
canonical cascade split of its total, because the individual volumes
`(A.card, B.card)` need not coincide with the cascade split `(p, q)` of
`A.card + B.card`.  The earlier `terminalPair_cost_eq_canonical` /
`terminalPair_is_cascade_initial` leaves stated equalities for *every* such pair
and were therefore **false**; they have been removed in favour of the honest
descent leaf `pairedCompression_reaches_canonical` below, which targets the strong
`IsCanonicalCascadePair` predicate directly. -/
def IsWeaklyTerminalPair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  IsSimplicial A ∧ IsSimplicial B ∧ IsNestedPair A B

/-- **The strong canonical / terminal predicate.**  A pair `(A, B)` is a canonical
cascade pair when both slices are the simplicial initial segments named by *the*
canonical cascade split `(p, q)` of their combined volume `A.card + B.card`.  This
is the genuine Frankl-Füredi terminal object: it fixes not only that the slices are
simplicial and nested, but that the split of the total is the canonical cascade
split.  By `cascadeSplit_unique` the witnesses `p, q` are determined by the pair. -/
def IsCanonicalCascadePair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  ∃ p q : ℕ, CascadeSplit N (A.card + B.card) p q ∧
    A = simplicialInitSeg N p ∧ B = simplicialInitSeg N q


open Classical in
/-- Returns the canonical cascade pair for a given total volume. -/
noncomputable def canonicalPairOfTotal (N total : ℕ) : Finset (Cube N) × Finset (Cube N) :=
  if h : ∃ p q, CascadeSplit N total p q then
    let p := Classical.choose h
    let q := Classical.choose (Classical.choose_spec h)
    (simplicialInitSeg N p, simplicialInitSeg N q)
  else
    (∅, ∅)

/-- The distance from a pair `(A, B)` to the canonical cascade pair of the same total volume,
measured by symmetric difference size. -/
noncomputable def distanceToCanonical {N : ℕ} (A B : Finset (Cube N)) : ℕ :=
  let (A_can, B_can) := canonicalPairOfTotal N (A.card + B.card)
  (A \ A_can).card + (A_can \ A).card + (B \ B_can).card + (B_can \ B).card

/-- A structurally meaningful paired step on two slice families.

It is either a coordinate-wise Up/Down compression (which preserves individual
sizes), or the oriented weak-terminal cascade phase.  The cascade constructor is
intentionally not just "same total weak-terminal pair": weak terminality alone
does not determine the Frankl-Füredi cascade split.  In particular, at total `4`
in dimension `2`, the canonical split `(3, 1)` and the weakly terminal split
`(2, 2)` have different costs, so an unoriented constructor would allow false
cost-increasing moves out of the canonical pair.

The cascade phase therefore carries the real obligations that still have to be
proved from the PDF/Macaulay argument: the target is the canonical cascade pair
for the same total, the cost does not increase, and the distance potential
strictly decreases.  These fields are deliberately not inferred from weak
terminality alone; they are supplied by the named cascade-exchange lemma below. -/
inductive IsPairedCompressionStep {N : ℕ} (A B : Finset (Cube N)) :
    Finset (Cube N) → Finset (Cube N) → Prop
  | coord (i : Fin N) (A' B' : Finset (Cube N))
      (hA : IsCoordinateUp i A A') (hB : IsCoordinateDown i B B') :
      IsPairedCompressionStep A B A' B'
  | cascade (A' B' : Finset (Cube N))
      (hTerm : IsWeaklyTerminalPair A B)
      (hTarget : IsCanonicalCascadePair A' B')
      (hTotal : A'.card + B'.card = A.card + B.card)
      (hCost : PairShadowCost N A' B' ≤ PairShadowCost N A B)
      (hProgress : distanceToCanonical A' B' < distanceToCanonical A B) :
      IsPairedCompressionStep A B A' B'

lemma paired_step_total_mass {N : ℕ} {A B A' B' : Finset (Cube N)}
    (step : IsPairedCompressionStep A B A' B') :
    A'.card + B'.card = A.card + B.card := by
  cases step with
  | coord i A' B' hA hB =>
      rw [hA.1, hB.1]
  | cascade A' B' hTerm hTarget hTotal hCost hProgress =>
      exact hTotal


/-- One paired coordinate Up/Down compression does not increase the two-slice
Frankl-Füredi cost.

This is now a **sorry-free reduction** to the two named PDF shadow-monotonicity
lemmas above: the slice cardinalities are preserved by the compression
(`hA.1`, `hB.1`), and `max` is monotone in its first argument, so the cost bound
follows term-by-term from `|N(A')| ≤ |N(A)|` and `|N(B')| ≤ |N(B)|`.  No scalar
Harper minimization is used. -/
lemma paired_coordinate_step_cost_nonincrease {N : ℕ} {A B A' B' : Finset (Cube N)}
    {i : Fin N} (hA : IsCoordinateUp i A A') (hB : IsCoordinateDown i B B') :
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  unfold PairShadowCost
  have hAcard : A'.card = A.card := hA.1
  have hBcard : B'.card = B.card := hB.1
  have hNA : (neighborhood 1 A').card ≤ (neighborhood 1 A).card :=
    coordinateUp_neighborhood_card_le hA
  have hNB : (neighborhood 1 B').card ≤ (neighborhood 1 B).card :=
    coordinateDown_neighborhood_card_le hB
  have h1 : max (neighborhood 1 A').card B'.card ≤ max (neighborhood 1 A).card B.card := by
    rw [hBcard]; exact max_le_max hNA le_rfl
  have h2 : max (neighborhood 1 B').card A'.card ≤ max (neighborhood 1 B).card A.card := by
    rw [hAcard]; exact max_le_max hNB le_rfl
  exact Nat.add_le_add h1 h2

lemma paired_step_cost_nonincrease {N : ℕ} {A B A' B' : Finset (Cube N)}
    (step : IsPairedCompressionStep A B A' B') :
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  cases step with
  | coord i A' B' hA hB =>
      exact paired_coordinate_step_cost_nonincrease hA hB
  | cascade A' B' hTerm hTarget hTotal hCost hProgress =>
      exact hCost

-- ============================================================================
-- Frankl–Füredi set-family Up/Down BLOCK operations (the paper's `𝒰`, `𝒟`).
--
-- These are the literal paper objects.  For finite blocks `U, V` the paper sets,
-- on a *single* set `S` of the family `𝒜`,
--
--     𝒰(S) = S - U + V   if  U ⊆ S, V ∩ S = ∅, and S - U + V ∉ 𝒜;   else S,
--     𝒟(S) = S - V + U   if  V ⊆ S, U ∩ S = ∅, and S - V + U ∉ ℬ;   else S,
--
-- and applies `𝒰` to one family, `𝒟` to the other.  Here `S - U + V` is the
-- Finset block replacement `(S \ U) ∪ V`.  The two facts the paper asserts about
-- them — "`𝒰` and `𝒟` are one-to-one, hence `|𝒰(𝒜)| = |𝒜|`, `|𝒟(ℬ)| = |ℬ|`" —
-- are proved here *sorry-free* (`familyUp_card`, `familyDown_card`) from the
-- block-recovery identity `blockReplace_recover`.  This is reusable PDF
-- infrastructure (it does not depend on any later Harper leaf).
-- ============================================================================

/-- PDF block replacement on a single vertex/set: `S - U + V = (S \ U) ∪ V`. -/
noncomputable def blockReplace {N : ℕ} (U V S : Cube N) : Cube N := (S \ U) ∪ V

/-- **Block recovery.**  When `U ⊆ S` and `V` is disjoint from `S`, the inverse
move `· - V + U` undoes `blockReplace U V`.  This is what makes the paper's `𝒰`
one-to-one. -/
lemma blockReplace_recover {N : ℕ} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) :
    (blockReplace U V S \ V) ∪ U = S := by
  unfold blockReplace
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hx, hxV⟩ | hxU)
    · rcases hx with ⟨hxS, _⟩ | hxV'
      · exact hxS
      · exact (hxV hxV').elim
    · exact hUS hxU
  · intro hxS
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · refine Or.inl ⟨Or.inl ⟨hxS, hxU⟩, ?_⟩
      exact fun hxV => (Finset.disjoint_left.mp hVS hxV hxS)

/-- The paper's `𝒰` on a single set, relative to the family `𝒜`. -/
noncomputable def familyUpMap {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N))
    (S : Cube N) : Cube N :=
  if U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ 𝒜 then blockReplace U V S else S

/-- The paper's `𝒟` on a single set, relative to the family `ℬ`. -/
noncomputable def familyDownMap {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N))
    (S : Cube N) : Cube N :=
  if V ⊆ S ∧ Disjoint U S ∧ blockReplace V U S ∉ ℬ then blockReplace V U S else S

/-- The PDF **Up** operation on a whole family: `𝒰(𝒜) = { 𝒰(S) : S ∈ 𝒜 }`. -/
noncomputable def familyUp {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    Finset (Cube N) :=
  𝒜.image (familyUpMap U V 𝒜)

/-- The PDF **Down** operation on a whole family: `𝒟(ℬ) = { 𝒟(S) : S ∈ ℬ }`. -/
noncomputable def familyDown {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    Finset (Cube N) :=
  ℬ.image (familyDownMap U V ℬ)

/-- The paper's `𝒰` is one-to-one on its family. -/
lemma familyUpMap_injOn {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    Set.InjOn (familyUpMap U V 𝒜) ↑𝒜 := by
  intro S hS T hT hST
  have hS' : S ∈ 𝒜 := Finset.mem_coe.mp hS
  have hT' : T ∈ 𝒜 := Finset.mem_coe.mp hT
  unfold familyUpMap at hST
  by_cases hSm : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ 𝒜
  · by_cases hTm : U ⊆ T ∧ Disjoint V T ∧ blockReplace U V T ∉ 𝒜
    · rw [ite_eq_left hSm, ite_eq_left hTm] at hST
      have hrec := congrArg (fun s => (s \ V) ∪ U) hST
      simpa only [blockReplace_recover hSm.1 hSm.2.1,
        blockReplace_recover hTm.1 hTm.2.1] using hrec
    · rw [ite_eq_left hSm, ite_eq_right hTm] at hST
      exact absurd (show blockReplace U V S ∈ 𝒜 by rw [hST]; exact hT') hSm.2.2
  · by_cases hTm : U ⊆ T ∧ Disjoint V T ∧ blockReplace U V T ∉ 𝒜
    · rw [ite_eq_right hSm, ite_eq_left hTm] at hST
      exact absurd (show blockReplace U V T ∈ 𝒜 by rw [← hST]; exact hS') hTm.2.2
    · rw [ite_eq_right hSm, ite_eq_right hTm] at hST
      exact hST

/-- The paper's `𝒟` is one-to-one on its family. -/
lemma familyDownMap_injOn {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    Set.InjOn (familyDownMap U V ℬ) ↑ℬ := by
  intro S hS T hT hST
  have hS' : S ∈ ℬ := Finset.mem_coe.mp hS
  have hT' : T ∈ ℬ := Finset.mem_coe.mp hT
  unfold familyDownMap at hST
  by_cases hSm : V ⊆ S ∧ Disjoint U S ∧ blockReplace V U S ∉ ℬ
  · by_cases hTm : V ⊆ T ∧ Disjoint U T ∧ blockReplace V U T ∉ ℬ
    · rw [ite_eq_left hSm, ite_eq_left hTm] at hST
      have hrec := congrArg (fun s => (s \ U) ∪ V) hST
      simpa only [blockReplace_recover hSm.1 hSm.2.1,
        blockReplace_recover hTm.1 hTm.2.1] using hrec
    · rw [ite_eq_left hSm, ite_eq_right hTm] at hST
      exact absurd (show blockReplace V U S ∈ ℬ by rw [hST]; exact hT') hSm.2.2
  · by_cases hTm : V ⊆ T ∧ Disjoint U T ∧ blockReplace V U T ∉ ℬ
    · rw [ite_eq_right hSm, ite_eq_left hTm] at hST
      exact absurd (show blockReplace V U T ∈ ℬ by rw [← hST]; exact hS') hTm.2.2
    · rw [ite_eq_right hSm, ite_eq_right hTm] at hST
      exact hST

/-- **Cardinality preservation for `𝒰`** (`|𝒰(𝒜)| = |𝒜|`). -/
lemma familyUp_card {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    (familyUp U V 𝒜).card = 𝒜.card :=
  Finset.card_image_of_injOn (familyUpMap_injOn U V 𝒜)

/-- **Cardinality preservation for `𝒟`** (`|𝒟(ℬ)| = |ℬ|`). -/
lemma familyDown_card {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    (familyDown U V ℬ).card = ℬ.card :=
  Finset.card_image_of_injOn (familyDownMap_injOn U V ℬ)

/-- A single paired Up/Down move preserves the total volume `|𝒜| + |ℬ|`. -/
lemma familyUpDown_total {N : ℕ} (U V : Cube N) (𝒜 ℬ : Finset (Cube N)) :
    (familyUp U V 𝒜).card + (familyDown U V ℬ).card = 𝒜.card + ℬ.card := by
  rw [familyUp_card, familyDown_card]

/-- **PDF family Hamming distance** `d(𝒜, ℬ) = min { |A △ B| : A ∈ 𝒜, B ∈ ℬ }`
(item 3 of the desired infrastructure: the separation functional the paper's
paired move is required to preserve).  Defined as `0` on an empty product, which
never occurs for the nonempty families the paper compresses. -/
noncomputable def familyHammingDist {N : ℕ} (𝒜 ℬ : Finset (Cube N)) : ℕ :=
  if h : (𝒜 ×ˢ ℬ).Nonempty then
    (𝒜 ×ˢ ℬ).inf' h (fun p => hDist p.1 p.2)
  else 0

-- ============================================================================
-- Terminal characterization (item 7): the `distanceToCanonical = 0` family is
-- exactly the canonical cascade pair.  Proved sorry-free.
-- ============================================================================

/-- **Terminal characterization.**  A pair at `distanceToCanonical = 0` is *the*
canonical cascade pair of its total.  This is the Lean form of the paper's
terminal statement "no admissible move ⟹ opposite-centered Hamming spheres":
the only fixed point of the descent is the canonical configuration. -/
lemma distanceToCanonical_zero_canonical {N : ℕ} (A B : Finset (Cube N))
    (h : distanceToCanonical A B = 0) : IsCanonicalCascadePair A B := by
  have hex : ∃ p q, CascadeSplit N (A.card + B.card) p q := by
    have htot : A.card + B.card ≤ 2 ^ (N + 1) := by
      have := card_le_two_pow A
      have := card_le_two_pow B
      have h2 : (2 : ℕ) ^ (N + 1) = 2 ^ N + 2 ^ N := by ring
      omega
    obtain ⟨p, q, _, _, _, hcs⟩ := exists_cascade_split N (A.card + B.card) htot
    exact ⟨p, q, hcs⟩
  -- unfold the canonical pair on the `dite_eq_left` branch
  set p := Classical.choose hex with hp
  set q := Classical.choose (Classical.choose_spec hex) with hq
  have hcs : CascadeSplit N (A.card + B.card) p q :=
    Classical.choose_spec (Classical.choose_spec hex)
  have hcanpair : canonicalPairOfTotal N (A.card + B.card)
      = (simplicialInitSeg N p, simplicialInitSeg N q) := by
    unfold canonicalPairOfTotal
    rw [dite_eq_left hex]
  have hsplit : distanceToCanonical A B
      = (A \ simplicialInitSeg N p).card + (simplicialInitSeg N p \ A).card
        + (B \ simplicialInitSeg N q).card + (simplicialInitSeg N q \ B).card := by
    unfold distanceToCanonical
    rw [hcanpair]
  rw [hsplit] at h
  have hA1 : (A \ simplicialInitSeg N p).card = 0 := by omega
  have hA2 : (simplicialInitSeg N p \ A).card = 0 := by omega
  have hB1 : (B \ simplicialInitSeg N q).card = 0 := by omega
  have hB2 : (simplicialInitSeg N q \ B).card = 0 := by omega
  have hAeq : A = simplicialInitSeg N p := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hA1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hA2)
  have hBeq : B = simplicialInitSeg N q := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hB1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hB2)
  exact ⟨p, q, hcs, hAeq, hBeq⟩

-- ============================================================================
-- The two PDF phases of the terminalization, and the assembled theorem.
-- ============================================================================

-- ============================================================================
-- Phase 1, decomposed into the genuine Frankl–Füredi *single-family* compression
-- mechanics.  Phase 1 reduces (sorry-free) to single-family vertex isoperimetry
-- `simplicialInitSeg_neighborhood_card_min`, which is itself assembled
-- (sorry-free) from:
--
--   * the sorry-free coordinate compression non-increase lemmas
--     (`coordinateDown_neighborhood_card_le`, …, in `SimplicialCompression`);
--   * the sorry-free terminal characterization
--     `coordinate_compressed_is_downClosed` + `downwardClosed_eq_initSeg`
--     ("no admissible compression move ⟹ Hamming sphere / simplicial segment");
--   * the well-founded descent on `compressionPotential`;
--
-- leaving the *single* honest PDF leaf `compression_descent_step`: a family that
-- is not yet fully compressed admits an admissible compression move that does not
-- increase the unit neighborhood and strictly decreases the rank potential.  This
-- is one sentence of the Frankl–Füredi/Harper compression proof, NOT a
-- `PairShadowCost`/`max` repackaging of Harper, NOT a scalar `H`/`CascadeSplit`
-- inequality, and NOT routed through any downstream Macaulay/Kruskal–Katona
-- lemma (it lives strictly upstream of `Shadow`/`SetFamilyShadow`/`MacaulayMin`).
-- ============================================================================

/-- A family is **fully compressed** for the Frankl–Füredi single-family
compression process when it is lower-level saturated and fixed by every
within-layer colex shift.  These are exactly the two terminal conditions whose
combination `lowerLevelSaturated_colexFixed_is_downClosed` shows forces simplicial
down-closure (the coordinate-Down-fixedness used in
`coordinate_compressed_is_downClosed` is not even needed — its argument there is
discarded — so it is dropped here to keep the terminal set as large, and the
descent leaf below as weak, as possible). -/
def IsFullyCompressed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  IsLowerLevelSaturated A ∧ IsColexShiftFixed A

/-- **Terminal ⟹ Hamming sphere.**  A fully compressed family is exactly the
simplicial initial segment of its own size.  This is the sorry-free Lean form of
"no admissible compression move ⟹ opposite-centered Hamming sphere": combine the
down-closure produced by the terminal conditions
(`lowerLevelSaturated_colexFixed_is_downClosed`) with the structural fact that a
down-closed family is an initial segment (`downwardClosed_eq_initSeg`). -/
lemma fullyCompressed_eq_initSeg {N : ℕ} (A : Finset (Cube N))
    (h : IsFullyCompressed A) : A = simplicialInitSeg N A.card :=
  downwardClosed_eq_initSeg
    (lowerLevelSaturated_colexFixed_is_downClosed A h.1 h.2)


/-- A rank-lowering single-set swap strictly decreases the rank potential
`compressionPotential = ∑ rank`: replacing `x` by an earlier set `y`
(`simplicialLt y x`, hence `rank y < rank x`) lowers the sum. -/
lemma swap_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {x y : Cube N}
    (hx : x ∈ A) (hy : y ∉ A) (hlt : simplicialLt y x)
    (heq : A' = insert y (A.erase x)) :
    compressionPotential A' < compressionPotential A := by
  have hrank : rank y < rank x := rank_strictMono hlt
  have hynm : y ∉ A.erase x := by simp [Finset.mem_erase, hy]
  have hsum_insert : compressionPotential A' = rank y + ∑ z ∈ A.erase x, rank z := by
    rw [heq]; unfold compressionPotential; rw [Finset.sum_insert hynm]
  have hsum_erase : (∑ z ∈ A.erase x, rank z) + rank x = compressionPotential A := by
    unfold compressionPotential; rw [Finset.sum_erase_add A _ hx]
  omega

/-- **The precise residual Phase-1 descent target.**  `IsDownFixedResidualShift A A'`
records that `A'` is a valid single Frankl–Füredi compression descent target for a
coordinate-Down-fixed family: same size, no larger unit neighborhood, strictly
smaller rank potential.

The intended witnesses are the paper colex/level shifts above, together with the
separate boundary monotonicity theorems for those moves. -/
def IsDownFixedResidualShift {N : ℕ} (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  (neighborhood 1 A').card ≤ (neighborhood 1 A).card ∧
  compressionPotential A' < compressionPotential A

theorem residualShift_card {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsDownFixedResidualShift A A') : A'.card = A.card := h.1

theorem residualShift_neighborhood_card_le {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsDownFixedResidualShift A A') :
    (neighborhood 1 A').card ≤ (neighborhood 1 A).card := h.2.1

theorem residualShift_potential_lt {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsDownFixedResidualShift A A') :
    compressionPotential A' < compressionPotential A := h.2.2

/-- A singleton-coordinate block colex move.  This is a useful special case of the
paper's block operation, but it is **not** the full terminalization move for
`IsColexShiftFixed`: a colex failure may replace an arbitrary same-layer vertex
by an earlier one, not just one coordinate by another. -/
def IsPaperColexBlockMove {N : ℕ}
    (A A' : Finset (Cube N)) (i j : Fin N) : Prop :=
  A' = familyUp {i} {j} A ∧ A' ≠ A ∧ i < j

/-- The **pure** within-layer Frankl–Füredi terminalization move: replace elements
in the same Hamming layer using either a single-vertex colex shift or a
single-coordinate colex block move.

This predicate describes *only the move* (rule 4): it carries **no** boundary
certificate.  Boundary monotonicity is genuinely a property of the *selected*
move, not of every colex shift — the finite checker
`verify_colexShift_boundary_small.py` exhibits an `N = 4` down-fixed,
lower-level-saturated family with a single-vertex colex shift that strictly
*increases* the closed unit neighborhood.  Hence the boundary bound must be
proved for the specific KK-selected move at the existence site
(`not_colexShiftFixed_exists_paperColexShiftMove`), never asserted for the whole
predicate. -/
def IsPaperColexShiftMove {N : ℕ}
    (A A' : Finset (Cube N)) : Prop :=
  IsColexShift A A' ∨ ∃ i j, IsPaperColexBlockMove A A' i j

/-- A nontrivial level-changing block move satisfying the paper's residual conditions. -/
def IsPaperLevelBlockMove {N : ℕ}
    (A A' : Finset (Cube N)) (U V : Cube N) : Prop :=
  A' = familyUp U V A ∧
  A' ≠ A ∧
  Disjoint U V ∧
  V.card < U.card ∧
  (∀ x ∈ V, ∃ y ∈ U, familyUp (U.erase y) (V.erase x) A = A) ∧
  (∀ x ∈ U, ∃ y ∈ V, familyUp (V.erase y) (U.erase x) Aᶜˢ = Aᶜˢ)

/-- One admissible residual compression step in the paper's reduction. -/
inductive IsPaperResidualStep {N : ℕ}
    (A : Finset (Cube N)) : Finset (Cube N) → Prop
  | colexShift {A'} :
      IsPaperColexShiftMove A A' →
      -- Boundary non-increase is *selection data* discharged by the KK existence
      -- leaf `not_colexShiftFixed_exists_paperColexShiftMove`, NOT a certificate
      -- projected off the pure move predicate.
      (neighborhood 1 A').card ≤ (neighborhood 1 A).card →
      IsCoordinateDownFixed A →
      IsLowerLevelSaturated A →
      IsPaperResidualStep A A'
  | levelBlock {A' U V} :
      IsPaperLevelBlockMove A A' U V → IsPaperResidualStep A A'

/-- The transitive closure of admissible residual compression steps. -/
def IsPaperResidualSequence {N : ℕ}
    (A A' : Finset (Cube N)) : Prop :=
  Relation.TransGen IsPaperResidualStep A A'

/-! ### Block-move rank-descent infrastructure

The two `*_potential_lt` leaves are honest rank-descent facts, proved here with no
Kruskal–Katona / Harper input.  `compressionPotential = ∑ rank`, and `familyUp U V`
acts on each set `S` by `familyUpMap`, which either leaves `S` fixed or replaces it
with `blockReplace U V S = (S \ U) ∪ V`.  We show every replaced set is simplicially
smaller, so the rank sum strictly drops once at least one set actually moves
(`familyUp U V A ≠ A`). -/

/-- Binary value is additive over disjoint unions. -/
lemma cubeToNat_union_disjoint {N} {s t : Cube N} (h : Disjoint s t) :
    cubeToNat (s ∪ t) = cubeToNat s + cubeToNat t := by
  unfold cubeToNat; exact Finset.sum_union h

/-- Binary value splits across a subset/complement. -/
lemma cubeToNat_sdiff_add {N} {U S : Cube N} (h : U ⊆ S) :
    cubeToNat (S \ U) + cubeToNat U = cubeToNat S := by
  rw [← cubeToNat_union_disjoint (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset h]

lemma cubeToNat_le_of_subset {N} {U S : Cube N} (h : U ⊆ S) :
    cubeToNat U ≤ cubeToNat S := by
  have := cubeToNat_sdiff_add h; omega

/-- Cardinality of a block replacement `(S \ U) ∪ V` when `U ⊆ S` and `V` is
disjoint from `S`. -/
lemma blockReplace_card {N} {U V S : Cube N} (hUS : U ⊆ S) (hVS : Disjoint V S) :
    (blockReplace U V S).card = S.card - U.card + V.card := by
  unfold blockReplace
  rw [Finset.card_union_of_disjoint (Disjoint.disjoint_sdiff_left (Disjoint.symm hVS)),
    Finset.card_sdiff_of_subset hUS]

/-- Binary value of a block replacement. -/
lemma cubeToNat_blockReplace {N} {U V S : Cube N} (hUS : U ⊆ S) (hVS : Disjoint V S) :
    cubeToNat (blockReplace U V S) = cubeToNat S - cubeToNat U + cubeToNat V := by
  unfold blockReplace
  rw [cubeToNat_union_disjoint (Disjoint.disjoint_sdiff_left (Disjoint.symm hVS))]
  have := cubeToNat_sdiff_add hUS; omega

/-- **Level block move descent.**  Replacing block `U ⊆ S` by a strictly smaller
block `V` (disjoint from `S`, `V.card < U.card`) yields a simplicially smaller set
(lower Hamming weight comes first in the simplicial order). -/
lemma blockReplace_simplicialLt_level {N} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) (hcard : V.card < U.card) :
    simplicialLt (blockReplace U V S) S := by
  have hcle : U.card ≤ S.card := Finset.card_le_card hUS
  have hbc : (blockReplace U V S).card < S.card := by
    rw [blockReplace_card hUS hVS]; omega
  refine ⟨Or.inl hbc, ?_⟩
  rintro (h | ⟨h, _⟩) <;> omega

/-- **Colex block move descent.**  Replacing block `U ⊆ S` by an equal-size block `V`
(disjoint from `S`) that is simplicially below `U` yields a simplicially smaller set:
equal weight, but a strictly larger binary value because `cubeToNat U < cubeToNat V`. -/
lemma blockReplace_simplicialLt_colex {N} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) (hcard : U.card = V.card)
    (hVU : simplicialLt V U) :
    simplicialLt (blockReplace U V S) S := by
  have hbc : (blockReplace U V S).card = S.card := by
    rw [blockReplace_card hUS hVS]
    have : U.card ≤ S.card := Finset.card_le_card hUS
    omega
  have hUV_nat : cubeToNat U < cubeToNat V := by
    obtain ⟨hle, hnle⟩ := hVU
    unfold simplicialLe at hle hnle
    rcases hle with h | ⟨_, h⟩
    · omega
    · rcases lt_or_eq_of_le h with h2 | h2
      · exact h2
      · exfalso; apply hnle; right; exact ⟨hcard, le_of_eq h2.symm⟩
  have hUleS : cubeToNat U ≤ cubeToNat S := cubeToNat_le_of_subset hUS
  have hbr_nat : cubeToNat S < cubeToNat (blockReplace U V S) := by
    rw [cubeToNat_blockReplace hUS hVS]; omega
  refine ⟨Or.inr ⟨hbc, le_of_lt hbr_nat⟩, ?_⟩
  rintro (h | ⟨_, h⟩) <;> omega

/-- **Block-move potential descent (general).**  If every replaced set drops in the
simplicial order, then a nontrivial `familyUp U V` move (`familyUp U V A ≠ A`) strictly
decreases the rank potential `compressionPotential = ∑ rank`. -/
lemma familyUp_potential_lt_of_blockLt {N : ℕ} {U V : Cube N} {A : Finset (Cube N)}
    (hne : familyUp U V A ≠ A)
    (hlt : ∀ S, U ⊆ S → Disjoint V S → simplicialLt (blockReplace U V S) S) :
    compressionPotential (familyUp U V A) < compressionPotential A := by
  have hsum : compressionPotential (familyUp U V A)
      = ∑ S ∈ A, rank (familyUpMap U V A S) := by
    unfold compressionPotential familyUp
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact familyUpMap_injOn U V A hx hy hxy
  rw [hsum]
  change ∑ S ∈ A, rank (familyUpMap U V A S) < compressionPotential A
  unfold compressionPotential
  apply Finset.sum_lt_sum
  · intro S _hS
    unfold familyUpMap
    split
    · next hc => exact le_of_lt (rank_strictMono (hlt S hc.1 hc.2.1))
    · exact le_rfl
  · have hex : ∃ S ∈ A, familyUpMap U V A S ≠ S := by
      by_contra hcon
      push Not at hcon
      apply hne
      unfold familyUp
      rw [Finset.image_congr (g := id) (fun S hS => hcon S hS), Finset.image_id]
    obtain ⟨S, hS, hSne⟩ := hex
    refine ⟨S, hS, ?_⟩
    unfold familyUpMap at hSne ⊢
    split at hSne
    · next hc =>
      rw [ite_eq_left hc]
      exact rank_strictMono (hlt S hc.1 hc.2.1)
    · exact absurd rfl hSne

/-- **Admissibility for a paper block move, in the mathlib `UV` orientation.**
The paper's `𝒰`-move (`familyUp U V`) is `UV.compression V U` (it removes the `U`
block and inserts the disjoint `V` block).  The Frankl–Füredi/Kruskal–Katona
shadow-nonincrease hypothesis for `UV.compression V U A`
(`Finset.UV.card_shadow_compression_le V U`) is
`∀ x ∈ V, ∃ y ∈ U, IsCompressed (V.erase x) (U.erase y) A`; phrased back through the
block-move dictionary (`familyUp_eq_UV_compression`) this is exactly the predicate
below.  Note the quantifier orientation (`x ∈ V`, `y ∈ U`, erasing `U` at `y` and
`V` at `x`) is the one that matches mathlib, not the transposed one. -/
def IsUVAdmissibleForFamily {N : ℕ} (A : Finset (Cube N)) (U V : Cube N) : Prop :=
  ∀ x ∈ V, ∃ y ∈ U, familyUp (U.erase y) (V.erase x) A = A

/-- **Per-set block dictionary.**  For disjoint blocks `U`, `V` the mathlib
single-element compression `UV.compress V U` agrees with the project's block
replacement: it is `blockReplace U V S = (S \ U) ∪ V` exactly when `U ⊆ S` and `V`
is disjoint from `S`, and the identity otherwise.  (Disjointness of `U`, `V` is
what makes `(S ∪ V) \ U = (S \ U) ∪ V`.) -/
lemma compress_VU_eq_blockReplace {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (S : Cube N) :
    UV.compress V U S = (if U ⊆ S ∧ Disjoint V S then blockReplace U V S else S) := by
  unfold UV.compress blockReplace
  by_cases h : U ⊆ S ∧ Disjoint V S
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, Finset.sup_eq_union, Finset.union_sdiff_distrib]
    have hVU : V \ U = V := (Finset.sdiff_eq_self_iff_disjoint).2 hd.symm
    rw [hVU]
  · rw [ite_eq_right h, ite_eq_right (by tauto)]

/-- **Block-move ↔ mathlib `UV`-compression dictionary.**  For disjoint blocks the
project's family `𝒰`-move is literally mathlib's `UV`-compression with the slots
swapped: `familyUp U V A = UV.compression V U A`.  Proved set-theoretically from
`compress_VU_eq_blockReplace`, identifying the image form (`familyUpMap`, which
keeps a set fixed when its replacement already lies in `A`) with mathlib's
"stay / move" split (`UV.mem_compression`). -/
lemma familyUp_eq_UV_compression {N : ℕ} (A : Finset (Cube N)) {U V : Cube N}
    (hd : Disjoint U V) :
    familyUp U V A = UV.compression V U A := by
  ext a
  rw [familyUp, Finset.mem_image, UV.mem_compression]
  constructor
  · rintro ⟨S, hS, rfl⟩
    unfold familyUpMap
    by_cases hc : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ A
    · rw [ite_eq_left hc]
      exact Or.inr ⟨hc.2.2, S, hS, by
        rw [compress_VU_eq_blockReplace hd, ite_eq_left ⟨hc.1, hc.2.1⟩]⟩
    · rw [ite_eq_right hc]
      refine Or.inl ⟨hS, ?_⟩
      rw [compress_VU_eq_blockReplace hd]
      by_cases hsub : U ⊆ S ∧ Disjoint V S
      · rw [ite_eq_left hsub]
        by_contra hni
        exact hc ⟨hsub.1, hsub.2, hni⟩
      · rw [ite_eq_right hsub]; exact hS
  · rintro (⟨haA, hca⟩ | ⟨haA, b, hb, hcb⟩)
    · refine ⟨a, haA, ?_⟩
      unfold familyUpMap
      by_cases hc : U ⊆ a ∧ Disjoint V a ∧ blockReplace U V a ∉ A
      · exfalso
        rw [compress_VU_eq_blockReplace hd, ite_eq_left ⟨hc.1, hc.2.1⟩] at hca
        exact hc.2.2 hca
      · rw [ite_eq_right hc]
    · refine ⟨b, hb, ?_⟩
      unfold familyUpMap
      rw [compress_VU_eq_blockReplace hd] at hcb
      by_cases hsub : U ⊆ b ∧ Disjoint V b
      · rw [ite_eq_left hsub] at hcb
        subst hcb
        rw [ite_eq_left ⟨hsub.1, hsub.2, haA⟩]
      · rw [ite_eq_right hsub] at hcb
        subst hcb
        exact absurd hb haA

/-- **Block move does not increase the shadow** (Frankl–Füredi / Kruskal–Katona).
For disjoint admissible blocks the `𝒰`-move's shadow is no larger than the
original's.  This is the mathlib UV-compression shadow bound
`Finset.UV.card_shadow_compression_le` transported across the block dictionary. -/
lemma familyUp_shadow_card_le_of_admissible {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV : IsUVAdmissibleForFamily A U V) :
    (familyUp U V A).shadow.card ≤ A.shadow.card := by
  rw [familyUp_eq_UV_compression A hd]
  apply UV.card_shadow_compression_le V U
  intro x hx
  obtain ⟨y, hy, hcomp⟩ := hUV x hx
  refine ⟨y, hy, ?_⟩
  have hde : Disjoint (U.erase y) (V.erase x) :=
    hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  change UV.compression (V.erase x) (U.erase y) A = A
  rw [← familyUp_eq_UV_compression A hde]
  exact hcomp

/-- **Block replacement commutes with vertex complementation.**  For disjoint
blocks, complementing the result of replacing `U` by `V` is the same as replacing
`V` by `U` in the complemented set: `(blockReplace U V S)ᶜ = blockReplace V U Sᶜ`.
This is the cube self-duality that turns the lower shadow into the upper shadow. -/
lemma blockReplace_compl {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (S : Cube N) :
    (blockReplace U V S)ᶜ = blockReplace V U Sᶜ := by
  unfold blockReplace
  have hUV := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro h
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · exact Or.inl ⟨fun hxS => h (Or.inl ⟨hxS, hxU⟩), fun hxV => h (Or.inr hxV)⟩
  · rintro (⟨hxnS, hxnV⟩ | hxU)
    · rintro (⟨hxS, _⟩ | hxV)
      · exact hxnS hxS
      · exact hxnV hxV
    · rintro (⟨_, hxnU⟩ | hxV)
      · exact hxnU hxU
      · exact hUV hxU hxV

/-- The per-set `𝒰`-map intertwines with complementation: applying `familyUpMap U V A`
then complementing equals complementing then applying the swapped map
`familyUpMap V U (Aᶜˢ)`.  (The membership guard `∉ A` becomes `∉ Aᶜˢ` under the
complement bijection.) -/
lemma familyUpMap_compl {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    (A : Finset (Cube N)) (S : Cube N) :
    (familyUpMap U V A S)ᶜ = familyUpMap V U (Aᶜˢ) Sᶜ := by
  unfold familyUpMap
  have hbr := blockReplace_compl hd S
  by_cases hc : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ A
  · obtain ⟨hUS, hVS, hnA⟩ := hc
    rw [ite_eq_left ⟨hUS, hVS, hnA⟩]
    have hUSc : Disjoint U Sᶜ := by
      rw [← subset_compl_iff_disjoint_right, compl_compl]; exact hUS
    have hc2 : V ⊆ Sᶜ ∧ Disjoint U Sᶜ ∧ blockReplace V U Sᶜ ∉ Aᶜˢ := by
      refine ⟨subset_compl_iff_disjoint_right.mpr hVS, hUSc, ?_⟩
      rw [Finset.mem_compls, ← hbr, compl_compl]; exact hnA
    rw [ite_eq_left hc2, hbr]
  · rw [ite_eq_right hc]
    have hc2 : ¬ (V ⊆ Sᶜ ∧ Disjoint U Sᶜ ∧ blockReplace V U Sᶜ ∉ Aᶜˢ) := by
      rintro ⟨hVSc, hUSc, hnAc⟩
      apply hc
      refine ⟨?_, subset_compl_iff_disjoint_right.mp hVSc, ?_⟩
      · have : U ⊆ Sᶜᶜ := subset_compl_iff_disjoint_right.mpr hUSc
        rwa [compl_compl] at this
      · rw [Finset.mem_compls, ← hbr, compl_compl] at hnAc; exact hnAc
    rw [ite_eq_right hc2]

/-- **The `𝒰`-move commutes with vertex complementation at family level.**  For
disjoint blocks, `(familyUp U V A)ᶜˢ = familyUp V U (Aᶜˢ)`.  This is what reduces
upper-shadow control of a block move to lower-shadow control of the dual block
move on the complemented family. -/
lemma familyUp_compls {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (A : Finset (Cube N)) :
    (familyUp U V A)ᶜˢ = familyUp V U (Aᶜˢ) := by
  have hL : (familyUp U V A)ᶜˢ = A.image (fun S => (familyUpMap U V A S)ᶜ) := by
    rw [familyUp, ← Finset.image_compl, Finset.image_image]; rfl
  have hR : familyUp V U (Aᶜˢ) = A.image (fun S => familyUpMap V U (Aᶜˢ) Sᶜ) := by
    rw [familyUp, ← Finset.image_compl, Finset.image_image]; rfl
  rw [hL, hR]
  exact Finset.image_congr (fun S _hS => familyUpMap_compl hd A S)

/-- **Block move does not increase the upper shadow** (the dual of
`familyUp_shadow_card_le_of_admissible`).  Phrased via the complement bijection
(`#(∂⁺ F) = #(∂ Fᶜˢ)`, mathlib `Finset.shadow_compls`): the lower shadow of the
complemented image is bounded by that of `Aᶜˢ`.  Needs the *dual* admissibility
`IsUVAdmissibleForFamily (Aᶜˢ) V U` of the complemented family for the swapped
blocks — admissibility of the lower-shadow move alone does **not** control the
upper shadow (a finite counterexample exists already at `N = 3`). -/
lemma familyUp_upperShadow_card_le_of_admissible {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    ((familyUp U V A)ᶜˢ).shadow.card ≤ (Aᶜˢ).shadow.card := by
  rw [familyUp_compls hd]
  exact familyUp_shadow_card_le_of_admissible hd.symm hUV'

/-- **Closed unit neighborhood as the union of the family, its lower shadow, and
its upper shadow.**  In the Boolean cube the closed Hamming ball of radius 1 of a
family `A` is exactly `A ∪ ∂A ∪ ∂⁺A`: a vertex at Hamming distance `≤ 1` of some
`u ∈ A` is either `u` itself, a one-element subset (lower shadow `∂A`), or a
one-element superset (upper shadow `∂⁺A`).  This is the structural dictionary
bridging the project's metric `neighborhood 1` to mathlib's `Finset.shadow` /
`Finset.upShadow`, so the closed-neighborhood leaf below can be analysed with the
standard set-family shadow operators (and the already-proved UV shadow bounds).
Sorry-free. -/
lemma neighborhood_one_eq_self_union_shadow_upShadow {N : ℕ} (A : Finset (Cube N)) :
    neighborhood 1 A = A ∪ Finset.shadow A ∪ Finset.upShadow A := by
  ext v
  simp only [Finset.mem_union, mem_neighborhood_iff]
  constructor
  · rintro ⟨u, huA, hd⟩
    have hsplit : symmDiff u v = (u \ v) ∪ (v \ u) := by
      ext y; simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
    have hdisj : Disjoint (u \ v) (v \ u) := disjoint_sdiff_sdiff
    have hcard : (u \ v).card + (v \ u).card ≤ 1 := by
      have : (symmDiff u v).card ≤ 1 := hd
      rwa [hsplit, Finset.card_union_of_disjoint hdisj] at this
    rcases Nat.eq_zero_or_pos (u \ v).card with huv0 | huvpos
    · rcases Nat.eq_zero_or_pos (v \ u).card with hvu0 | hvupos
      · have hsub1 : u ⊆ v := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact huv0
        have hsub2 : v ⊆ u := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact hvu0
        have huv : u = v := Finset.Subset.antisymm hsub1 hsub2
        exact Or.inl (Or.inl (huv ▸ huA))
      · have hvu1 : (v \ u).card = 1 := by omega
        have hsub : u ⊆ v := by
          rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact huv0
        refine Or.inr ?_
        rw [Finset.mem_upShadow_iff_exists_sdiff]
        exact ⟨u, huA, hsub, hvu1⟩
    · have huv1 : (u \ v).card = 1 := by omega
      have hvu0 : (v \ u).card = 0 := by omega
      have hsub : v ⊆ u := by
        rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]; exact hvu0
      refine Or.inl (Or.inr ?_)
      rw [Finset.mem_shadow_iff_exists_sdiff]
      exact ⟨u, huA, hsub, huv1⟩
  · rintro ((hv | hv) | hv)
    · exact ⟨v, hv, by simp [hDist]⟩
    · rw [Finset.mem_shadow_iff_exists_sdiff] at hv
      obtain ⟨s, hs, hvs, hcard⟩ := hv
      refine ⟨s, hs, ?_⟩
      have hss : symmDiff s v = s \ v := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        constructor
        · rintro (⟨hys, hyv⟩ | ⟨hyv, hys⟩)
          · exact ⟨hys, hyv⟩
          · exact absurd (hvs hyv) hys
        · rintro ⟨hys, hyv⟩; exact Or.inl ⟨hys, hyv⟩
      have : hDist s v = 1 := by unfold hDist; rw [hss]; exact hcard
      omega
    · rw [Finset.mem_upShadow_iff_exists_sdiff] at hv
      obtain ⟨s, hs, hsv, hcard⟩ := hv
      refine ⟨s, hs, ?_⟩
      have hss : symmDiff s v = v \ s := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        constructor
        · rintro (⟨hys, hyv⟩ | ⟨hyv, hys⟩)
          · exact absurd (hsv hys) hyv
          · exact ⟨hyv, hys⟩
        · rintro ⟨hyv, hys⟩; exact Or.inr ⟨hyv, hys⟩
      have : hDist s v = 1 := by unfold hDist; rw [hss]; exact hcard
      omega

lemma card_eq_sum_card_filter_layer {N : ℕ} (A : Finset (Cube N)) :
    A.card = ∑ k ∈ Finset.range (N + 1), (A.filter (fun x => x.card = k)).card := by
  have H : Set.MapsTo (fun (x : Cube N) => x.card) ↑A ↑(Finset.range (N + 1)) := by
    intro x _
    simp only [mem_coe, mem_range]
    have h1 : x.card ≤ Fintype.card (Fin N) := Finset.card_le_univ x
    have h2 : Fintype.card (Fin N) = N := Fintype.card_fin N
    omega
  exact Finset.card_eq_sum_card_fiberwise H

/-- Lower-shadow membership in a fixed output layer only depends on the next
input layer.  This is the local Hamming-window dictionary used by the
layer-by-layer closed-neighborhood argument. -/
lemma shadow_filter_layer_eq {N : ℕ} (A : Finset (Cube N)) (k : ℕ) :
    (Finset.shadow A).filter (fun x => x.card = k) =
      (Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
        (fun x => x.card = k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxsh, hxcard⟩
    rw [Finset.mem_shadow_iff_exists_sdiff] at hxsh ⊢
    rcases hxsh with ⟨s, hsA, hxs, hsdiff⟩
    have hscard : s.card = k + 1 := by
      have hcard_sdiff : (s \ x).card = s.card - x.card := Finset.card_sdiff_of_subset hxs
      rw [hcard_sdiff, hxcard] at hsdiff
      have hxle : k ≤ s.card := by
        rw [← hxcard]
        exact Finset.card_le_card hxs
      omega
    exact ⟨⟨s, by simp [hsA, hscard], hxs, hsdiff⟩, hxcard⟩
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxsh, hxcard⟩
    rw [Finset.mem_shadow_iff_exists_sdiff] at hxsh ⊢
    rcases hxsh with ⟨s, hsA, hxs, hsdiff⟩
    exact ⟨⟨s, (Finset.mem_filter.mp hsA).1, hxs, hsdiff⟩, hxcard⟩

/-- Upper-shadow membership in a fixed output layer only depends on the previous
input layer.  The `k = 0` case is empty on the upper-shadow side, and the
`Nat.pred` formulation keeps the window statement total. -/
lemma upShadow_filter_layer_eq {N : ℕ} (A : Finset (Cube N)) (k : ℕ) :
    (Finset.upShadow A).filter (fun x => x.card = k) =
      (Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
        (fun x => x.card = k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxup, hxcard⟩
    rw [Finset.mem_upShadow_iff_exists_sdiff] at hxup ⊢
    rcases hxup with ⟨s, hsA, hsx, hsdiff⟩
    have hscard : s.card = k - 1 := by
      have hcard_sdiff : (x \ s).card = x.card - s.card := Finset.card_sdiff_of_subset hsx
      rw [hcard_sdiff, hxcard] at hsdiff
      have hsle : s.card ≤ k := by
        rw [← hxcard]
        exact Finset.card_le_card hsx
      omega
    exact ⟨⟨s, by simp [hsA, hscard], hsx, hsdiff⟩, hxcard⟩
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxup, hxcard⟩
    rw [Finset.mem_upShadow_iff_exists_sdiff] at hxup ⊢
    rcases hxup with ⟨s, hsA, hsx, hsdiff⟩
    exact ⟨⟨s, (Finset.mem_filter.mp hsA).1, hsx, hsdiff⟩, hxcard⟩

lemma neighborhood_one_filter_layer_eq_self_shadow_upShadow {N : ℕ}
    (A : Finset (Cube N)) (k : ℕ) :
    (neighborhood 1 A).filter (fun x => x.card = k) =
      (A.filter (fun x => x.card = k)) ∪
        ((Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
          (fun x => x.card = k)) ∪
        ((Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
          (fun x => x.card = k)) := by
  rw [neighborhood_one_eq_self_union_shadow_upShadow]
  ext x
  have hshadow :
      (x ∈ Finset.shadow A ∧ x.card = k) ↔
        (x ∈ Finset.shadow (A.filter (fun x => x.card = k + 1)) ∧ x.card = k) := by
    have hmem := congrArg (fun S : Finset (Cube N) => x ∈ S) (shadow_filter_layer_eq A k)
    exact Iff.of_eq (by simpa only [Finset.mem_filter] using hmem)
  have hupShadow :
      (x ∈ Finset.upShadow A ∧ x.card = k) ↔
        (x ∈ Finset.upShadow (A.filter (fun x => x.card = k - 1)) ∧ x.card = k) := by
    have hmem := congrArg (fun S : Finset (Cube N) => x ∈ S) (upShadow_filter_layer_eq A k)
    exact Iff.of_eq (by simpa only [Finset.mem_filter] using hmem)
  simp only [Finset.mem_filter, Finset.mem_union]
  tauto

lemma familyUp_subset_familyUp {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    {A B : Finset (Cube N)} (hsub : A ⊆ B) :
    familyUp U V A ⊆ familyUp U V B := by
  rw [familyUp_eq_UV_compression A hd, familyUp_eq_UV_compression B hd]
  intro x hx
  rw [UV.mem_compression] at hx ⊢
  rcases hx with ⟨hxA, hcompA⟩ | ⟨hxniA, y, hyA, hcomp⟩
  · exact Or.inl ⟨hsub hxA, hsub hcompA⟩
  · by_cases hxB : x ∈ B
    · refine Or.inl ⟨hxB, ?_⟩
      have H : UV.compress V U x = x := by
        rw [← hcomp, UV.compress_idem]
      rwa [H]
    · exact Or.inr ⟨hxB, y, hsub hyA, hcomp⟩

lemma familyUp_shadow_subset {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV : IsUVAdmissibleForFamily A U V) :
    shadow (familyUp U V A) ⊆ familyUp U V (shadow A) := by
  rw [familyUp_eq_UV_compression A hd, familyUp_eq_UV_compression (shadow A) hd]
  apply UV.shadow_compression_subset_compression_shadow V U
  intro x hx
  obtain ⟨y, hy, hcomp⟩ := hUV x hx
  refine ⟨y, hy, ?_⟩
  have hde : Disjoint (U.erase y) (V.erase x) := hd.mono (erase_subset _ _) (erase_subset _ _)
  change UV.compression (V.erase x) (U.erase y) A = A
  rw [← familyUp_eq_UV_compression A hde]
  exact hcomp

lemma familyUp_upShadow_subset {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    upShadow (familyUp U V A) ⊆ familyUp U V (upShadow A) := by
  have h_shad := familyUp_shadow_subset hd.symm hUV'
  have h_shad_comp := compls_subset_compls.mpr h_shad
  have H1 : compls (shadow (familyUp V U (compls A))) = upShadow (familyUp U V A) := by
    rw [← familyUp_compls hd, Finset.shadow_compls, compls_compls]
  have H2 : compls (familyUp V U (shadow (compls A))) = familyUp U V (upShadow A) := by
    have h_comp_sh : shadow (compls A) = compls (upShadow A) := Finset.shadow_compls
    rw [h_comp_sh, familyUp_compls hd.symm, compls_compls]
  rwa [H1, H2] at h_shad_comp

/-- **Closed unit-neighborhood compression inclusion.**
If a block move is doubly admissible for `A`, the neighborhood of the compressed
family is a subset of the compression of the neighborhood. This avoids layer-by-layer
bounds which are false when `|V| < |U|`, instead providing a global inclusion that
preserves cardinality. -/
lemma neighborhood_one_subset_familyUp_neighborhood_of_admissible {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    neighborhood 1 (familyUp U V A) ⊆ familyUp U V (neighborhood 1 A) := by
  rw [neighborhood_one_eq_self_union_shadow_upShadow,
    neighborhood_one_eq_self_union_shadow_upShadow]
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with (hxA | hxSh) | hxUp
  · have : x ∈ familyUp U V A := hxA
    have H_sub : A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub this
  · have : x ∈ shadow (familyUp U V A) := hxSh
    have H : x ∈ familyUp U V (shadow A) := familyUp_shadow_subset hd hadm this
    have H_sub : shadow A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub H
  · have : x ∈ upShadow (familyUp U V A) := hxUp
    have H : x ∈ familyUp U V (upShadow A) := familyUp_upShadow_subset hd hadm' this
    have H_sub : upShadow A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub H

/-- **Closed unit-neighborhood nonincrease for a doubly-admissible block move.**
This is the genuine Frankl–Füredi boundary-monotonicity leaf: an admissible
disjoint block `𝒰`-move that is admissible in *both* directions (primal
`IsUVAdmissibleForFamily A U V`, controlling the lower shadow, and dual
`IsUVAdmissibleForFamily (Aᶜˢ) V U`, controlling the upper shadow) does not
increase the closed unit neighborhood `neighborhood 1 A`.

It is proved via the global inclusion `neighborhood_one_subset_familyUp_neighborhood_of_admissible`,
avoiding false layer-by-layer bounds for moves where `|V| < |U|`. -/
lemma neighborhood_one_card_le_for_admissible_block {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    (neighborhood 1 (familyUp U V A)).card ≤ (neighborhood 1 A).card := by
  have h_sub := neighborhood_one_subset_familyUp_neighborhood_of_admissible hd hadm hadm'
  have h_le := Finset.card_le_card h_sub
  rw [familyUp_card U V (neighborhood 1 A)] at h_le
  exact h_le

theorem paperColexBlockMove_card {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : A'.card = A.card := by
  have heq := h.1
  subst heq
  exact familyUp_card {i} {j} A

theorem paperColexBlockMove_neighborhood_card_le {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have h_adm : IsUVAdmissibleForFamily A {i} {j} := by
    intro x hx
    use i
    constructor
    · apply Finset.mem_singleton_self
    · have hx_eq : x = j := Finset.mem_singleton.mp hx
      subst hx_eq
      rw [Finset.erase_singleton, Finset.erase_singleton]
      unfold familyUp familyUpMap
      ext S
      simp [blockReplace]
  have h_adm_c : IsUVAdmissibleForFamily Aᶜˢ {j} {i} := by
    intro x hx
    use j
    constructor
    · apply Finset.mem_singleton_self
    · have hx_eq : x = i := Finset.mem_singleton.mp hx
      subst hx_eq
      rw [Finset.erase_singleton, Finset.erase_singleton]
      unfold familyUp familyUpMap
      ext S
      simp [blockReplace]
  have hdisj : Disjoint ({i} : Finset (Fin N)) ({j} : Finset (Fin N)) := by
    rw [Finset.disjoint_singleton]
    intro heq; subst heq; exact (lt_self_iff_false i).mp h.2.2
  have heq := h.1
  subst heq
  exact neighborhood_one_card_le_for_admissible_block hdisj h_adm h_adm_c

theorem paperColexBlockMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : compressionPotential A' < compressionPotential A := by
  have heq := h.1
  have hne := h.2.1
  have hlt := h.2.2
  subst heq
  refine familyUp_potential_lt_of_blockLt hne ?_
  intro S hsub hdisj
  have hcard : ({i} : Finset (Fin N)).card = ({j} : Finset (Fin N)).card := by
    rw [Finset.card_singleton, Finset.card_singleton]
  have hlt_simp : simplicialLt {j} {i} := by
    have h_nat : cubeToNat {i} < cubeToNat {j} := by
      unfold cubeToNat
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact Nat.pow_lt_pow_right (by norm_num) hlt
    refine ⟨Or.inr ⟨hcard, by omega⟩, ?_⟩
    rintro (H | ⟨_, H⟩) <;> omega
  exact blockReplace_simplicialLt_colex hsub hdisj hcard hlt_simp


theorem paperColexBlockMove_isResidualShift {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j)
    (_hdown : IsCoordinateDownFixed A)
    (_hlower : IsLowerLevelSaturated A) : IsDownFixedResidualShift A A' :=
  ⟨paperColexBlockMove_card h, paperColexBlockMove_neighborhood_card_le h,
    paperColexBlockMove_potential_lt h⟩

theorem paperColexShiftMove_card {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A') : A'.card = A.card := by
  rcases h with h_colex | ⟨i, j, h_block⟩
  · exact h_colex.1
  · exact paperColexBlockMove_card h_block

/-- Rank-potential strict descent for a pure within-layer colex move.  This is a
genuine dictionary consequence of the move (`swap_potential_lt` for a single
colex swap, `paperColexBlockMove_potential_lt` for a block move) — no boundary or
KK input. -/
theorem paperColexShiftMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A') : compressionPotential A' < compressionPotential A := by
  rcases h with h_colex | ⟨i, j, h_block⟩
  · rcases h_colex with ⟨_hcard, x, y, hx, hy, _hxycard, hlt, heq⟩
    exact swap_potential_lt hx hy hlt heq
  · exact paperColexBlockMove_potential_lt h_block

/-- Assemble the descent target from a pure within-layer colex move **and** the
separately supplied boundary non-increase `hnbhd`.  The boundary bound is genuine
selection data (from the KK existence leaf), not a projection off the move
predicate: `paperColexShiftMove_neighborhood_card_le` no longer exists because it
is false for arbitrary colex shifts (see the `IsPaperColexShiftMove` docstring). -/
theorem paperColexShiftMove_isResidualShift {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A')
    (hnbhd : (neighborhood 1 A').card ≤ (neighborhood 1 A).card) :
    IsDownFixedResidualShift A A' :=
  ⟨paperColexShiftMove_card h, hnbhd, paperColexShiftMove_potential_lt h⟩

theorem paperLevelBlockMove_card {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : A'.card = A.card := by
  rw [h.1]
  exact familyUp_card U V A

theorem paperLevelBlockMove_neighborhood_card_le {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have hd : Disjoint U V := h.2.2.1
  have hadm : IsUVAdmissibleForFamily A U V := h.2.2.2.2.1
  have hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U := h.2.2.2.2.2
  rw [h.1]
  exact neighborhood_one_card_le_for_admissible_block hd hadm hadm'

theorem paperLevelBlockMove_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : compressionPotential A' < compressionPotential A := by
  obtain ⟨heq, hne, _hd, hcard, _, _⟩ := h
  rw [heq]
  refine familyUp_potential_lt_of_blockLt (heq ▸ hne) ?_
  intro S hUS hVS
  exact blockReplace_simplicialLt_level hUS hVS hcard

lemma paperResidualStep_isResidualShift {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperResidualStep A A') : IsDownFixedResidualShift A A' := by
  cases h with
  | colexShift hmove hnbhd _hdown _hlower =>
      exact paperColexShiftMove_isResidualShift hmove hnbhd
  | levelBlock hmove =>
      exact ⟨paperLevelBlockMove_card hmove, paperLevelBlockMove_neighborhood_card_le hmove,
        paperLevelBlockMove_potential_lt hmove⟩

lemma paperResidualSequence_isResidualShift {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperResidualSequence A A') : IsDownFixedResidualShift A A' := by
  induction h with
  | single hstep => exact paperResidualStep_isResidualShift hstep
  | tail _ hstep ih =>
      have h2 := paperResidualStep_isResidualShift hstep
      exact ⟨by rw [h2.1, ih.1],
             le_trans h2.2.1 ih.2.1,
             lt_trans h2.2.2 ih.2.2⟩

/-- A coordinate-Down-fixed family is closed under deleting any present
coordinate: if `x ∈ A` and `i ∈ x` then `x.erase i ∈ A`.  This is the forward
direction of the `IsCoordinateDown i A A` fixed-point characterization. -/
lemma downFixed_erase_mem {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {x : Cube N} (hx : x ∈ A) {i : Fin N} (hi : i ∈ x) :
    x.erase i ∈ A := by
  have hfix := (hdown i).2 x
  have hmem : x ∈ A := hx
  rw [hfix] at hmem
  rcases hmem with ⟨_, hcase⟩ | ⟨hi', _, _⟩
  · rcases hcase with hni | herase
    · exact absurd hi hni
    · exact herase
  · exact absurd hi hi'

/-- Iterating `downFixed_erase_mem`: a coordinate-Down-fixed family is closed
under removing any sub-block `W ⊆ S`. -/
lemma downFixed_sdiff_mem {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {S W : Cube N} (hS : S ∈ A) (hWS : W ⊆ S) :
    S \ W ∈ A := by
  classical
  induction W using Finset.induction generalizing S with
  | empty => simpa using hS
  | @insert i W hiW ih =>
      have hiS : i ∈ S := hWS (Finset.mem_insert_self i W)
      have hWsub : W ⊆ S := fun a ha => hWS (Finset.mem_insert_of_mem ha)
      have hSi : S.erase i ∈ A := downFixed_erase_mem hdown hS hiS
      have hWsubErase : W ⊆ S.erase i := by
        intro a ha
        rw [Finset.mem_erase]
        exact ⟨fun hai => hiW (hai ▸ ha), hWsub ha⟩
      have := ih hSi hWsubErase
      have hrw : (S.erase i) \ W = S \ insert i W := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rwa [hrw] at this

/-- The `familyUp W ∅` move is trivial on a coordinate-Down-fixed family: removing
a block from any of its sets stays inside the (down-closed) family, so no set is
actually moved.  This is one of the two admissibility ingredients of a paper
level block move whose `V` is a single coordinate. -/
lemma downFixed_familyUp_erase_eq {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (W : Cube N) :
    familyUp W ∅ A = A := by
  classical
  have hmap : ∀ S ∈ A, familyUpMap W ∅ A S = S := by
    intro S hS
    unfold familyUpMap
    by_cases hc : W ⊆ S ∧ Disjoint (∅ : Cube N) S ∧ blockReplace W ∅ S ∉ A
    · exfalso
      have hbr : blockReplace W ∅ S = S \ W := by
        unfold blockReplace; simp
      rw [hbr] at hc
      exact hc.2.2 (downFixed_sdiff_mem hdown hS hc.1)
    · rw [ite_eq_right hc]
  unfold familyUp
  rw [Finset.image_congr (g := id) (fun S hS => hmap S hS), Finset.image_id]

/-- Dual admissibility ingredient: `familyUp ∅ W` is trivial on the complemented
family `Aᶜˢ` of a coordinate-Down-fixed `A`.  Follows from
`downFixed_familyUp_erase_eq` through the complement dictionary `familyUp_compls`. -/
lemma downFixed_familyUp_add_compls_eq {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (W : Cube N) :
    familyUp ∅ W (Aᶜˢ) = Aᶜˢ := by
  have hd : Disjoint (∅ : Cube N) W := by simp
  have key : (familyUp ∅ W (Aᶜˢ))ᶜˢ = Aᶜˢᶜˢ := by
    rw [familyUp_compls hd, compls_compls, downFixed_familyUp_erase_eq hdown W]
  have := congrArg (fun X => Xᶜˢ) key
  simpa [compls_compls] using this

/-- **Existence of a paper level block from lower-level-saturation failure.**

For a coordinate-Down-fixed family `A` that is not lower-level-saturated, there is
a present block `U ∈ A` with `2 ≤ U.card` and a coordinate `j ∉ U` such that the
single-coordinate level move `familyUp U {j} A` is nontrivial: some `S ∈ A`
containing `U` and avoiding `j` has its block replacement `(S \ U) ∪ {j}` outside
`A`.

This is the genuine combinatorial core (a strictly smaller terminalization
lemma): the admissibility of the resulting move is automatic from down-fixedness
(`downFixed_familyUp_erase_eq`, `downFixed_familyUp_add_compls_eq`), so only this
pure existence statement remains.  It is finite-checked NO_COUNTEREXAMPLE for
`N ≤ 4` by `verify_paperBlock_existence_small.py` (clean-form column). -/
lemma downFixed_downClosed {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {R S : Cube N} (hS : S ∈ A) (hRS : R ⊆ S) :
    R ∈ A := by
  have h := downFixed_sdiff_mem hdown hS (show S \ R ⊆ S from Finset.sdiff_subset)
  have hrw : S \ (S \ R) = R := by
    ext a
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨haS, h2⟩; by_contra hc; exact h2 ⟨haS, hc⟩
    · intro haR; exact ⟨hRS haR, fun h2 => h2.2 haR⟩
  rwa [hrw] at h

/-- Direct witness form of lower-level-saturation failure. -/
lemma not_lowerLevelSaturated_exists_witness {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card := by
  classical
  unfold IsLowerLevelSaturated at h
  push Not at h
  rcases h with ⟨T, S, hcard, hS, hT⟩
  exact ⟨T, S, hT, hS, hcard⟩

/-- The block replacement associated to an absent lower vertex `T` and a present
larger vertex `S`: remove `S \ T` and insert `T \ S`. -/
lemma blockReplace_sdiff_sdiff_eq_right {N : ℕ} (S T : Cube N) :
    blockReplace (S \ T) (T \ S) S = T := by
  unfold blockReplace
  ext a
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨haS, hnot⟩ | ⟨haT, _⟩)
    · by_contra haT
      exact hnot ⟨haS, haT⟩
    · exact haT
  · intro haT
    by_cases haS : a ∈ S
    · exact Or.inl ⟨haS, fun h => h.2 haT⟩
    · exact Or.inr ⟨haT, haS⟩

/-- Cardinality comparison for the block replacement associated to
`T.card < S.card`: the inserted block `T \ S` is strictly smaller than the
removed block `S \ T`. -/
lemma sdiff_card_lt_sdiff_card_of_card_lt {N : ℕ} {S T : Cube N}
    (hcard : T.card < S.card) : (T \ S).card < (S \ T).card := by
  have hTsplit : (T ∩ S).card + (T \ S).card = T.card :=
    Finset.card_inter_add_card_sdiff T S
  have hSsplit : (S ∩ T).card + (S \ T).card = S.card :=
    Finset.card_inter_add_card_sdiff S T
  have hcomm : (S ∩ T).card = (T ∩ S).card := by rw [Finset.inter_comm]
  omega

/-- **Extremal witness selection for lower-saturation failure (proved).**

If `A` is not lower-level-saturated, there is a `⊆`-minimal absent block `T`
(every proper subset of `T` lies in `A`) together with a maximum-cardinality
present block `S`, and `T.card < S.card`.  This is the honest, dimension-free
*selection* half of the Frankl–Füredi level-terminalization step; it needs only
failure of saturation, not down-fixedness.

It does **not** by itself give an admissible block: the finite checker
`verify_nearMiss_false_small.py` shows (claim `UA`, N = 5) that not every such
extremal pair is jointly admissible, so the eventual proof of
`downFixed_not_lowerSat_exists_admissibleBlock` must still select *which* extremal
pair works.  But every candidate produced here is a genuine minimal-absent /
max-present witness, exactly the objects the paper move ranges over. -/
lemma not_lowerSat_exists_minimalAbsent_maxPresent {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ (∀ R : Cube N, R ⊂ T → R ∈ A) ∧
      S ∈ A ∧ (∀ R ∈ A, R.card ≤ S.card) ∧ T.card < S.card := by
  classical
  -- A raw witness of saturation failure.
  obtain ⟨T₀, S₀, hT₀, hS₀, hcard₀⟩ := not_lowerLevelSaturated_exists_witness h
  -- A maximum-cardinality present block.
  obtain ⟨S, hSA, hSmax⟩ :
      ∃ S ∈ A, ∀ R ∈ A, R.card ≤ S.card :=
    A.exists_max_image (fun R => R.card) ⟨S₀, hS₀⟩
  have hS0_le : S₀.card ≤ S.card := hSmax S₀ hS₀
  -- A ⊆-minimal absent block contained in T₀ (so all its proper subsets lie in A).
  set B := T₀.powerset.filter (fun R => R ∉ A) with hBdef
  have hT0B : T₀ ∈ B := by
    simp only [hBdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, hT₀⟩
  obtain ⟨T, hTB, hTmin⟩ := B.exists_min_image (fun R => R.card) ⟨T₀, hT0B⟩
  rw [hBdef, Finset.mem_filter, Finset.mem_powerset] at hTB
  obtain ⟨hTsub, hTA⟩ := hTB
  refine ⟨T, S, hTA, ?_, hSA, hSmax, ?_⟩
  · -- every proper subset of `T` is present, by ⊆-minimality of `T` among absent subsets of `T₀`.
    intro R hR
    by_contra hRA
    have hRB : R ∈ B := by
      simp only [hBdef, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(hR.subset).trans hTsub, hRA⟩
    have hle := hTmin R hRB
    have hlt : R.card < T.card := Finset.card_lt_card hR
    omega
  · have hTcard : T.card ≤ T₀.card := Finset.card_le_card hTsub
    omega

/-- **Minimal-symmetric-difference extremal witness selection (proved).**

Refines `not_lowerSat_exists_minimalAbsent_maxPresent` by additionally selecting,
among all minimal-absent / maximum-present witness pairs `(T, S)` with
`T.card < S.card`, one that **minimizes the Hamming symmetric difference**
`|S \ T| + |T \ S| = |S △ T|`.  This is the exact selection criterion that the
finite checker `test_min_delta_extremal.py` confirms (exhaustive `N = 4`) yields a
jointly admissible Frankl–Füredi level block move `U = S \ T`, `V = T \ S`: among
the extremal frontier the pair whose blocks are as small as possible is the one
whose primal/dual erase-admissibility clauses hold.

Only the *selection* is proved here (sorry-free, pure finite minimization over the
nonempty frontier of extremal pairs); the admissibility consequence for the
selected pair is the remaining research content of
`downFixed_not_lowerSat_exists_admissibleBlock`.  This upgrades the previously
external min-`|S △ T|` finite evidence to an in-Lean theorem, giving the exact
selected objects the paper move ranges over. -/
lemma not_lowerSat_exists_minDelta_pair {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
      (∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) := by
  classical
  set Q : Cube N × Cube N → Prop := fun p =>
    p.1 ∉ A ∧ p.2 ∈ A ∧ p.1.card < p.2.card with hQ
  set P : Finset (Cube N × Cube N) := Finset.univ.filter Q with hP
  have hPne : P.Nonempty := by
    obtain ⟨T, S, h1, h2, h3, h4, h5⟩ := not_lowerSat_exists_minimalAbsent_maxPresent h
    exact ⟨(T, S), by
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, hQ]
      exact ⟨h1, h3, h5⟩⟩
  obtain ⟨p, hpP, hpmin⟩ :=
    P.exists_min_image (fun p => (p.2 \ p.1).card + (p.1 \ p.2).card) hPne
  rw [hP, Finset.mem_filter] at hpP
  obtain ⟨-, hT, hS, hcard⟩ := hpP
  refine ⟨p.1, p.2, hT, hS, hcard, ?_⟩
  intro T' S' h1 h3 h5
  have hp'P : (T', S') ∈ P := by
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, hQ]
    exact ⟨h1, h3, h5⟩
  exact hpmin (T', S') hp'P

/-- **Characterization of a trivial `𝒰`-move (Mathlib dictionary lemma).**

The family `𝒰`-move `familyUp W₁ W₂ A` fixes `A` setwise exactly when no set of `A`
is actually moved: for every `R ∈ A` with `W₁ ⊆ R` and `W₂` disjoint from `R`, the
block replacement `blockReplace W₁ W₂ R = (R \ W₁) ∪ W₂` already lies in `A`.  This
is a pure image/injectivity dictionary fact about `familyUp = A.image (familyUpMap …)`
and the definitional guard of `familyUpMap`; it carries no combinatorial content and
is reused by both directional admissibility leaves. -/
lemma familyUp_eq_self_iff {N : ℕ} (W₁ W₂ : Cube N) (A : Finset (Cube N)) :
    familyUp W₁ W₂ A = A ↔
      ∀ R ∈ A, W₁ ⊆ R → Disjoint W₂ R → blockReplace W₁ W₂ R ∈ A := by
  classical
  constructor
  · intro hEq R hR hsub hdisj
    by_contra hnot
    have hguard : W₁ ⊆ R ∧ Disjoint W₂ R ∧ blockReplace W₁ W₂ R ∉ A := ⟨hsub, hdisj, hnot⟩
    have hmap : familyUpMap W₁ W₂ A R = blockReplace W₁ W₂ R := by
      unfold familyUpMap; rw [ite_eq_left hguard]
    have hmem : blockReplace W₁ W₂ R ∈ familyUp W₁ W₂ A := by
      rw [familyUp, Finset.mem_image]; exact ⟨R, hR, hmap⟩
    rw [hEq] at hmem; exact hnot hmem
  · intro hClosed
    have hmap : ∀ R ∈ A, familyUpMap W₁ W₂ A R = R := by
      intro R hR
      unfold familyUpMap
      by_cases hguard : W₁ ⊆ R ∧ Disjoint W₂ R ∧ blockReplace W₁ W₂ R ∉ A
      · exact absurd (hClosed R hR hguard.1 hguard.2.1) hguard.2.2
      · rw [ite_eq_right hguard]
    unfold familyUp
    rw [Finset.image_congr (g := id) (fun R hR => hmap R hR), Finset.image_id]

/- **Joint admissible level-block existence from lower-saturation failure.**
(Design note for `downFixed_not_lowerSat_exists_admissibleBlock`, below.)

For a coordinate-Down-fixed `A` that is not lower-level-saturated there exists a
witness pair `T ∉ A`, `S ∈ A` with `T.card < S.card` whose associated block
`U = S \ T`, `V = T \ S` is **simultaneously** primal-admissible for `A`
(`IsUVAdmissibleForFamily A (S \ T) (T \ S)`, controlling the lower shadow) and
dual-admissible for the complemented family
(`IsUVAdmissibleForFamily Aᶜˢ (T \ S) (S \ T)`, controlling the upper shadow).

This replaces the previous two-leaf split `downFixed_not_lowerSat_exists_primal`
plus `downFixed_not_lowerSat_exists_dual`.  That split was **unsound**: the dual
leaf claimed that *every* primal-admissible witness pair is automatically
dual-admissible, and that is **false**.  A minimal counterexample (verified
exhaustively N ≤ 4 clean, exhibited at N = 5 by `verify_dual_leaf_false_small.py`)
is the coordinate-Down-fixed family
`A = {∅, {0},{1},{2},{3},{4}, {0,1},{0,2},{0,3},{0,4},{1,3},{2,4},{3,4},
      {0,1,3},{0,3,4}}`
with `T = {1,2}`, `S = {0,3,4}`: here `T ∉ A`, `S ∈ A`, `|T| < |S|`, the primal
admissibility clause holds, yet the dual clause fails at the coordinate `x = 4`.
The dual-from-primal implication only held under finite checks because those
checkers cap at `N ≤ 4`, below the first counterexample.

The correct terminalization statement is therefore this *joint* existence: the
finite checker confirms (N ≤ 4 exhaustive, N = 5,6 sampled, NO_COUNTEREXAMPLE)
that a pair satisfying **both** admissibility clauses always exists, which is
exactly what `IsPaperLevelBlockMove` (hence the public
`not_lowerLevelSaturated_exists_paperLevelBlock`) consumes.  Boundary
monotonicity is still proved from the move, never bundled into it.

The current strengthened frontier additionally requires `T` to be ⊆-minimal
absent and `S` to have maximum cardinality in `A`.  The exact extremal selection
claim is now pinned by `verify_extremal_admissible_pair_small.py` (exhaustive
through `N ≤ 4`, sampled at `N = 5`, no counterexample), separating it from the
known-false universal-extremal-admissibility claim. -/

/- **Admissibility of the selected minimal-symmetric-difference extremal pair.**
(Design note for `minDelta_extremal_pair_admissible`, assembled below from the two
directional leaves.)

This is the residual admissibility content of
`downFixed_not_lowerSat_exists_admissibleBlock` once the *selection* half has been
discharged sorry-free by `not_lowerSat_exists_minDelta_extremal_pair`.  It assumes
the paper's exact selected witness: `T` is ⊆-minimal absent, `S` is maximum
cardinality present, `T.card < S.card`, and `(T, S)` **minimizes the Hamming
symmetric difference** `|S \ T| + |T \ S|` over the extremal frontier.  It
concludes both the primal erase-admissibility clause (controlling the lower
shadow of `A`) and the dual erase-admissibility clause on the vertex-complement
family `Aᶜˢ` (controlling the upper shadow).

Why this is the honest strictly-smaller leaf.  The bare existence statement gave
the eventual proof *no handle on which pair to use*; not every extremal pair is
jointly admissible (`verify_nearMiss_false_small.py`, claim `UA`).  This leaf
fixes the pair to the minimizer and asks only that it be admissible.  The finite
checker `verify_minDelta_admissible_correctCompl.py` verifies, **exhaustively
through `N ≤ 5`** and using the *correct* mathlib vertex-complement family `Aᶜˢ`
(`Finset.compls`, not the family set-complement `Aᶜ` that the earlier
`test_min_delta_extremal.py` mistakenly used), that **every** min-`|S △ T|`
extremal pair satisfies both clauses.  So the arbitrary minimizer produced by
`not_lowerSat_exists_minDelta_extremal_pair` is guaranteed to work; the two proofs
compose. -/

/-- **Primal directional leaf.**  The lower-shadow (primal) erase-admissibility
clause for the minimal-symmetric-difference extremal pair.  For each `x` in the
inserted block `T \ S` some coordinate `y` of the removed block `S \ T` can be
spared so that the trimmed level-block move `familyUp ((S\T).erase y)
((T\S).erase x) A` fixes `A` setwise.  Proved (or to be proved) via the trivial-move
characterization `familyUp_eq_self_iff` and a contradiction against the
symmetric-difference minimality `hmin`. -/
lemma minDelta_pair_admissible_primal {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (_ : IsCoordinateDownFixed A)
    (_ : T ∉ A)
    (_ : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A := by
  intro x hx
  by_contra hcontra
  simp only [familyUp_eq_self_iff] at hcontra
  push Not at hcontra
  have hU_nonempty : (S \ T).Nonempty := by
    by_contra hE
    simp only [not_nonempty_iff_eq_empty] at hE
    have hle : S.card ≤ T.card := by
      calc
        S.card = (S \ T).card + (S ∩ T).card := by rw [card_sdiff_add_card_inter]
        _ = 0 + (S ∩ T).card := by rw [hE, card_empty]
        _ = (T ∩ S).card := by rw [zero_add, inter_comm]
        _ ≤ T.card := Finset.card_le_card Finset.inter_subset_left
    omega
  obtain ⟨y, hy⟩ := hU_nonempty
  obtain ⟨Ry, hRyA, hRy_sub, hRy_disj, hRy_notin⟩ := hcontra y hy
  let Uy := (S \ T).erase y
  let Vx := (T \ S).erase x
  let Ty := blockReplace Uy Vx Ry
  have hd : Disjoint (Ry \ Uy) Vx := Disjoint.symm (Disjoint.mono_right sdiff_subset hRy_disj)
  have hx_pos : 0 < (T \ S).card := card_pos.mpr ⟨x, hx⟩
  have hy_pos : 0 < (S \ T).card := card_pos.mpr ⟨y, hy⟩
  have hUy_card : Uy.card = (S \ T).card - 1 := card_erase_of_mem hy
  have hVx_card : Vx.card = (T \ S).card - 1 := card_erase_of_mem hx
  have hRy_eq : Ry.card = (Ry \ Uy).card + Uy.card := by
    exact (card_sdiff_add_card_eq_card hRy_sub).symm
  have hTy_eq : Ty.card = (Ry \ Uy).card + Vx.card := by
    have hd_union : Disjoint (Ry \ Uy) Vx := hd
    exact card_union_of_disjoint hd_union
  have h_diff : (T \ S).card < (S \ T).card := by
    have hS_eq := card_sdiff_add_card_inter S T
    have hT_eq := card_sdiff_add_card_inter T S
    rw [inter_comm] at hT_eq
    omega
  have hTy_card : Ty.card < Ry.card := by omega
  have h_hmin := hmin Ty Ry hRy_notin hRyA hTy_card
  have h_Ry_Ty : (Ry \ Ty).card = Uy.card := by
    have h1 : Ry \ Ty = Uy := by
      ext a
      simp only [Ty, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Ry := h.1
        have ha_not_Ty := h.2
        push Not at ha_not_Ty
        have ha_not_Ry_Uy := ha_not_Ty.1
        by_contra h_not_Uy
        exact h_not_Uy (ha_not_Ry_Uy ha_Ry)
      · intro ha_Uy
        have ha_Ry : a ∈ Ry := hRy_sub ha_Uy
        have ha_not_Ry_Uy : ¬(a ∈ Ry ∧ a ∉ Uy) := by
          intro h; exact h.2 ha_Uy
        have ha_not_Vx : a ∉ Vx := by
          have hd1 : Disjoint Uy Vx :=
            Disjoint.mono (erase_subset y (S \ T)) (erase_subset x (T \ S)) disjoint_sdiff_sdiff
          exact disjoint_left.mp hd1 ha_Uy
        exact ⟨ha_Ry, fun h => h.elim ha_not_Ry_Uy ha_not_Vx⟩
    rw [h1]
  have h_Ty_Ry : (Ty \ Ry).card = Vx.card := by
    have h1 : Ty \ Ry = Vx := by
      ext a
      simp only [Ty, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Ty := h.1
        have ha_not_Ry := h.2
        cases ha_Ty with
        | inl hRy_Uy => exact False.elim (ha_not_Ry hRy_Uy.1)
        | inr hVx => exact hVx
      · intro ha_Vx
        have ha_not_Ry : a ∉ Ry := by
          exact disjoint_left.mp hRy_disj ha_Vx
        exact ⟨Or.inr ha_Vx, ha_not_Ry⟩
    rw [h1]
  omega

lemma minDelta_pair_admissible_dual_A {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((S \ T).erase x) ((T \ S).erase y) A = A := by
  intro y hy
  by_contra hcontra
  simp only [familyUp_eq_self_iff] at hcontra
  push Not at hcontra
  have hV_nonempty : (T \ S).Nonempty := by
    by_contra hE
    simp only [not_nonempty_iff_eq_empty] at hE
    have h_sub : T ⊆ S := sdiff_eq_empty_iff_subset.mp hE
    have h_T_eq : S \ (S \ T) = T := Finset.sdiff_sdiff_eq_self h_sub
    have h_in_A : T ∈ A := by
      have h1 : S \ (S \ T) ∈ A := downFixed_sdiff_mem hdown hS sdiff_subset
      rwa [h_T_eq] at h1
    exact hT h_in_A
  obtain ⟨x, hx⟩ := hV_nonempty
  obtain ⟨Rx, hRxA, hRx_sub, hRx_disj, hRx_notin⟩ := hcontra x hx
  let Uy := (S \ T).erase y
  let Vx := (T \ S).erase x
  let Tx := blockReplace Uy Vx Rx
  have hd : Disjoint (Rx \ Uy) Vx := Disjoint.symm (Disjoint.mono_right sdiff_subset hRx_disj)
  have hx_pos : 0 < (T \ S).card := card_pos.mpr ⟨x, hx⟩
  have hy_pos : 0 < (S \ T).card := card_pos.mpr ⟨y, hy⟩
  have hUy_card : Uy.card = (S \ T).card - 1 := card_erase_of_mem hy
  have hVx_card : Vx.card = (T \ S).card - 1 := card_erase_of_mem hx
  have hRx_eq : Rx.card = (Rx \ Uy).card + Uy.card := by
    exact (card_sdiff_add_card_eq_card hRx_sub).symm
  have hTx_eq : Tx.card = (Rx \ Uy).card + Vx.card := by
    have hd_union : Disjoint (Rx \ Uy) Vx := hd
    exact card_union_of_disjoint hd_union
  have h_diff : (T \ S).card < (S \ T).card := by
    have hS_eq := card_sdiff_add_card_inter S T
    have hT_eq := card_sdiff_add_card_inter T S
    rw [inter_comm] at hT_eq
    omega
  have hTx_card : Tx.card < Rx.card := by omega
  have h_hmin := hmin Tx Rx hRx_notin hRxA hTx_card
  have h_Rx_Tx : (Rx \ Tx).card = Uy.card := by
    have h1 : Rx \ Tx = Uy := by
      ext a
      simp only [Tx, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Rx := h.1
        have ha_not_Tx := h.2
        push Not at ha_not_Tx
        have ha_not_Rx_Uy := ha_not_Tx.1
        by_contra h_not_Uy
        exact h_not_Uy (ha_not_Rx_Uy ha_Rx)
      · intro ha_Uy
        have ha_Rx : a ∈ Rx := hRx_sub ha_Uy
        have ha_not_Rx_Uy : ¬(a ∈ Rx ∧ a ∉ Uy) := by
          intro h; exact h.2 ha_Uy
        have ha_not_Vx : a ∉ Vx := by
          have hd1 : Disjoint Uy Vx :=
            Disjoint.mono (erase_subset y (S \ T)) (erase_subset x (T \ S)) disjoint_sdiff_sdiff
          exact disjoint_left.mp hd1 ha_Uy
        exact ⟨ha_Rx, fun h => h.elim ha_not_Rx_Uy ha_not_Vx⟩
    rw [h1]
  have h_Tx_Rx : (Tx \ Rx).card = Vx.card := by
    have h1 : Tx \ Rx = Vx := by
      ext a
      simp only [Tx, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Tx := h.1
        have ha_not_Rx := h.2
        cases ha_Tx with
        | inl hRx_Uy => exact False.elim (ha_not_Rx hRx_Uy.1)
        | inr hVx => exact hVx
      · intro ha_Vx
        have ha_not_Rx : a ∉ Rx := by
          exact disjoint_left.mp hRx_disj ha_Vx
        exact ⟨Or.inr ha_Vx, ha_not_Rx⟩
    rw [h1]
  omega

lemma minDelta_pair_admissible_dual {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ := by
  intro x hx
  obtain ⟨y, hy, hAeq⟩ :=
    minDelta_pair_admissible_dual_A hdown hT hS hcard hmin x hx
  refine ⟨y, hy, ?_⟩
  have hd : Disjoint ((S \ T).erase x) ((T \ S).erase y) :=
    (disjoint_sdiff_sdiff).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hbridge := familyUp_compls hd A
  rw [hAeq] at hbridge
  exact hbridge.symm

lemma minDelta_pair_admissible {N : ℕ} {A : Finset (Cube N)} {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    (∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A) ∧
    (∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ) :=
  ⟨minDelta_pair_admissible_primal hdown hT hS hcard hmin,
   minDelta_pair_admissible_dual hdown hT hS hcard hmin⟩

lemma downFixed_not_lowerSat_exists_admissibleBlock {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
    (∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A) ∧
    (∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ) := by
  obtain ⟨T, S, hT, hS, hcard, hmin⟩ :=
    not_lowerSat_exists_minDelta_pair h
  obtain ⟨hprimal, hdual⟩ :=
    minDelta_pair_admissible hdown hT hS hcard hmin
  exact ⟨T, S, hT, hS, hcard, hprimal, hdual⟩

/-- **Terminalization core for lower-level-saturation failure.**

The previous singleton "near-miss" formulation was too strong: a down-closed
family can fail lower-level saturation because of an absent block `T` that differs
from every larger present block in several new coordinates.  The PDF-faithful
move is the full block replacement `U = S \ T`, `V = T \ S`, with `V.card <
U.card`.

This leaf is the remaining local terminalization content: from a coordinate
Down-fixed, non-lower-saturated family, select an admissible Frankl-Furedi level
block move.  It is intentionally a pure move statement; boundary monotonicity is
still proved from `IsPaperLevelBlockMove`, not bundled into the predicate. -/
lemma downFixed_not_lowerSat_exists_levelBlock {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (h : ¬ IsLowerLevelSaturated A) :
    ∃ U V, IsPaperLevelBlockMove A (familyUp U V A) U V := by
  obtain ⟨T, S, hT, hS, hcard, hprimal, hdual⟩ :=
    downFixed_not_lowerSat_exists_admissibleBlock hdown h
  use S \ T, T \ S
  unfold IsPaperLevelBlockMove
  refine ⟨rfl, ?_, disjoint_sdiff_sdiff, sdiff_card_lt_sdiff_card_of_card_lt hcard, hprimal, hdual⟩
  intro heq
  have hblock : blockReplace (S \ T) (T \ S) S = T := blockReplace_sdiff_sdiff_eq_right S T
  have hT_in : T ∈ familyUp (S \ T) (T \ S) A := by
    unfold familyUp familyUpMap
    rw [Finset.mem_image]
    use S
    refine ⟨hS, ?_⟩
    split_ifs with h_if
    · exact hblock
    · push Not at h_if
      have h_subset : S \ T ⊆ S := sdiff_subset
      have h_disj : Disjoint (T \ S) S := Disjoint.symm disjoint_sdiff
      have h_not_in : blockReplace (S \ T) (T \ S) S ∉ A := by
        rw [hblock]
        exact hT
      exfalso
      exact h_not_in (h_if h_subset h_disj)
  rw [heq] at hT_in
  exact hT hT_in

theorem not_lowerLevelSaturated_exists_paperLevelBlock
    {N : ℕ} (A : Finset (Cube N))
    (hdown : IsCoordinateDownFixed A)
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ A' U V, IsPaperLevelBlockMove A A' U V := by
  obtain ⟨U, V, hmove⟩ := downFixed_not_lowerSat_exists_levelBlock hdown h
  exact ⟨familyUp U V A, U, V, hmove⟩


/-- **General layer-localized neighborhood monotonicity.**  If `A` and `A'` are
both concentrated in layers `≤ r` and both contain every set of card `< r`, then
comparing their unit neighborhoods reduces to comparing their layer-`(r+1)` upper
shadows.  (This is the swap-free generalization of the body of the old
`neighborhood_card_le_of_upperLayerShadow_le_of_colexShift`.) -/
lemma neighborhood_card_le_of_layers_upperShadow_le {N r : ℕ}
    {A A' : Finset (Cube N)} (hr : 1 ≤ r)
    (hA_le : ∀ w ∈ A, w.card ≤ r) (hA'_le : ∀ w ∈ A', w.card ≤ r)
    (hA_full : ∀ z : Cube N, z.card < r → z ∈ A)
    (hA'_full : ∀ z : Cube N, z.card < r → z ∈ A')
    (h_shadow : (upperLayerShadow N r A').card ≤ (upperLayerShadow N r A).card) :
    (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have hmem_gen : ∀ (B : Finset (Cube N)), (∀ z : Cube N, z.card < r → z ∈ B) →
      ∀ z : Cube N, z.card ≤ r → z ∈ neighborhood 1 B := by
    intro B hBfull z hz
    rw [mem_neighborhood_iff]
    rcases lt_or_eq_of_le hz with hlt | heq
    · exact ⟨z, hBfull z hlt, by unfold hDist; simp⟩
    · have hzne : z.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hzne
      refine ⟨z.erase a, hBfull _ ?_, ?_⟩
      · rw [Finset.card_erase_of_mem ha]; omega
      · have hsub : symmDiff (z.erase a) z ⊆ {a} := by
          intro w hw
          rw [Finset.mem_symmDiff] at hw
          simp only [Finset.mem_singleton]
          rcases hw with ⟨hwe, hwnz⟩ | ⟨hwz, hwne⟩
          · exact absurd (Finset.mem_of_mem_erase hwe) hwnz
          · by_contra hne
            exact hwne (Finset.mem_erase.mpr ⟨hne, hwz⟩)
        unfold hDist
        calc (symmDiff (z.erase a) z).card ≤ ({a} : Finset (Fin N)).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton a
  have hmemA := hmem_gen A hA_full
  have hmemA' := hmem_gen A' hA'_full
  have nbhd_layer_top : ∀ (B : Finset (Cube N)), (∀ w ∈ B, w.card ≤ r) →
      (neighborhood 1 B).filter (fun z => z.card = r + 1) = upperLayerShadow N r B := by
    intro B hB
    rw [neighborhood_one_filter_layer_eq_self_shadow_upShadow]
    have e1 : B.filter (fun z => z.card = r + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e2 : B.filter (fun z => z.card = r + 1 + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    simp only [e1, e2, Finset.shadow_empty, Finset.filter_empty, Finset.empty_union]
    rw [← upShadow_filter_layer_eq B (r + 1)]
    rfl
  have nbhd_layer_high : ∀ (B : Finset (Cube N)) (k : ℕ), (∀ w ∈ B, w.card ≤ r) → r + 1 < k →
      (neighborhood 1 B).filter (fun z => z.card = k) = ∅ := by
    intro B k hB hk
    rw [neighborhood_one_filter_layer_eq_self_shadow_upShadow]
    have e0 : B.filter (fun z => z.card = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e1 : B.filter (fun z => z.card = k + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e2 : B.filter (fun z => z.card = k - 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    simp only [e0, e1, e2, Finset.shadow_empty, Finset.upShadow_empty, Finset.filter_empty,
        Finset.union_empty]
  have key : ∀ k ∈ Finset.range (N + 1),
      ((neighborhood 1 A').filter (fun z => z.card = k)).card
        ≤ ((neighborhood 1 A).filter (fun z => z.card = k)).card := by
    intro k _
    by_cases hkr : k ≤ r
    · have eqA : (neighborhood 1 A).filter (fun z => z.card = k)
          = Finset.univ.filter (fun z : Cube N => z.card = k) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun hc => ⟨hmemA z (by omega), hc⟩⟩
      have eqA' : (neighborhood 1 A').filter (fun z => z.card = k)
          = Finset.univ.filter (fun z : Cube N => z.card = k) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun hc => ⟨hmemA' z (by omega), hc⟩⟩
      rw [eqA, eqA']
    · have hkr' : r < k := not_le.mp hkr
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hkr') with hk1 | hk2
      · have hkeq : k = r + 1 := hk1.symm
        subst hkeq
        rw [nbhd_layer_top A' hA'_le, nbhd_layer_top A hA_le]
        exact h_shadow
      · rw [nbhd_layer_high A' k hA'_le hk2, nbhd_layer_high A k hA_le hk2]
  rw [card_eq_sum_card_filter_layer (neighborhood 1 A'),
      card_eq_sum_card_filter_layer (neighborhood 1 A)]
  exact Finset.sum_le_sum key


/-- **Slice-reduction dictionary lemma.**  The upper layer shadow at layer `r`
depends only on the card-`r` slice of the family, because a card-`(r+1)` set lies
in `upShadow B` iff it contains some card-`r` member of `B`.  This is a direct
specialization of `upShadow_filter_layer_eq` at `k = r + 1`. -/
lemma upperLayerShadow_eq_filter_layer {N r : ℕ} (B : Finset (Cube N)) :
    upperLayerShadow N r B = upperLayerShadow N r (B.filter (fun z => z.card = r)) := by
  unfold upperLayerShadow
  have h := upShadow_filter_layer_eq B (r + 1)
  simpa using h

/-- `simplicialInitSeg N 0 = ∅`. -/
lemma simplicialInitSeg_zero {N : ℕ} : simplicialInitSeg N 0 = ∅ := by
  simp [simplicialInitSeg]

/-- `rank (∅) = 0`. -/
lemma rank_empty {N : ℕ} : rank (∅ : Cube N) = 0 := by
  classical
  unfold rank
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ h
  rcases h with ⟨hle, hnle⟩
  unfold simplicialLe at hle hnle
  rcases hle with h | ⟨hc, _⟩
  · simp at h
  · have hy : y = ∅ := Finset.card_eq_zero.mp hc
    subst hy
    exact hnle (Or.inr ⟨rfl, le_rfl⟩)

/-- `simplicialInitSeg N 1 = {∅}`. -/
lemma simplicialInitSeg_one {N : ℕ} : simplicialInitSeg N 1 = {(∅ : Cube N)} := by
  have hmem : (∅ : Cube N) ∈ simplicialInitSeg N 1 := by
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and, rank_empty]
    norm_num
  have hcard : (simplicialInitSeg N 1).card = 1 := by
    rw [card_simplicialInitSeg]; exact min_eq_left (Nat.one_le_two_pow)
  exact (Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun x hx => by
    have := Finset.card_le_one.mp (le_of_eq hcard) x hx (∅ : Cube N) hmem
    exact this⟩)

/-- **Lower-saturated KK-jump.**  For a lower-level-saturated family `A`, the
simplicial initial segment of size `A.card` has unit neighborhood no larger than
`A`'s.  Proof: `A` is a full ball below its top layer `r` plus a card-`r` slice
`L`; the initial segment shares that ball and carries the *colex-initial* `r`-slice
`layerInitSeg N r |L|`, whose upper shadow is minimal by the Kruskal–Katona
theorem `upperLayerShadow_min`.  `neighborhood_card_le_of_layers_upperShadow_le`
then transfers the layer bound to the full neighborhood. -/
lemma simplicialInitSeg_neighborhood_le_of_lowerSaturated {N : ℕ} {A : Finset (Cube N)}
    (hl : IsLowerLevelSaturated A) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [simplicialInitSeg_zero]
  · set r := (A.image Finset.card).max' (hne.image Finset.card) with hr_def
    -- membership witness of the top layer
    have hrmem : r ∈ A.image Finset.card := Finset.max'_mem _ _
    obtain ⟨w0, hw0A, hw0card⟩ := Finset.mem_image.mp hrmem
    have hA_le : ∀ w ∈ A, w.card ≤ r := fun w hw =>
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hw)
    have hA_full : ∀ z : Cube N, z.card < r → z ∈ A := by
      intro z hz; exact hl (by rw [hw0card]; exact hz) hw0A
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · -- r = 0 : A = {∅}, initial segment equals A
      have hAeq : A = {(∅ : Cube N)} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨?_, ?_⟩
        · have h0 : w0.card = 0 := by rw [hw0card, hr0]
          have : w0 = (∅ : Cube N) := Finset.card_eq_zero.mp h0
          exact this ▸ hw0A
        · intro x hx
          have : x.card ≤ 0 := by rw [← hr0]; exact hA_le x hx
          exact Finset.card_eq_zero.mp (Nat.le_zero.mp this)
      rw [hAeq]
      have : ({(∅ : Cube N)} : Finset (Cube N)).card = 1 := Finset.card_singleton _
      rw [this, simplicialInitSeg_one]
    · -- r ≥ 1 : the KK jump
      set L := A.filter (fun z => z.card = r) with hL_def
      have hL : ∀ x ∈ L, x.card = r := fun x hx => (Finset.mem_filter.mp hx).2
      set t := L.card with ht_def
      have ht_choose : t ≤ Nat.choose N r := card_le_choose_of_uniform hL
      -- A splits as (full ball below r) ∪ L
      have hAeq : A = (Finset.univ.filter (fun z : Cube N => z.card < r)) ∪ L := by
        ext z
        simp only [hL_def, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hz
          rcases lt_or_eq_of_le (hA_le z hz) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hz, h⟩
        · rintro (h | ⟨hz, _⟩)
          · exact hA_full z h
          · exact hz
      have hdisj : Disjoint (Finset.univ.filter (fun z : Cube N => z.card < r)) L := by
        rw [Finset.disjoint_left]; intro z hz hzL
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have := (Finset.mem_filter.mp hzL).2; omega
      have hAcard : A.card = binomPrefix N r + t := by
        rw [hAeq, Finset.card_union_of_disjoint hdisj, ← binomPrefix_eq_card_lt, ht_def]
      -- the initial segment
      set IS := simplicialInitSeg N A.card with hIS_def
      have hlow : simplicialInitSeg N (binomPrefix N r) =
          Finset.univ.filter (fun z : Cube N => z.card < r) := by
        ext z
        simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and,
          rank_lt_binomPrefix_iff]
      have hIS_eq : IS = (Finset.univ.filter (fun z : Cube N => z.card < r))
          ∪ layerInitSeg N r t := by
        rw [hIS_def, hAcard, simplicialInitSeg_decomp ht_choose, hlow]
      -- L1 hypotheses for A' = IS
      have hIS_le : ∀ w ∈ IS, w.card ≤ r := by
        intro w hw; rw [hIS_eq] at hw
        rcases Finset.mem_union.mp hw with h | h
        · exact le_of_lt (Finset.mem_filter.mp h).2
        · exact le_of_eq (layerInitSeg_uniform w h)
      have hIS_full : ∀ z : Cube N, z.card < r → z ∈ IS := by
        intro z hz; rw [hIS_eq]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      have hIS_slice : IS.filter (fun z => z.card = r) = layerInitSeg N r t := by
        ext z
        constructor
        · intro hz
          rcases Finset.mem_filter.mp hz with ⟨hzIS, hzc⟩
          rw [hIS_eq] at hzIS
          rcases Finset.mem_union.mp hzIS with h | h
          · exact absurd (Finset.mem_filter.mp h).2 (by omega)
          · exact h
        · intro hz
          refine Finset.mem_filter.mpr ⟨?_, layerInitSeg_uniform z hz⟩
          rw [hIS_eq]; exact Finset.mem_union_right _ hz
      have h_shadow : (upperLayerShadow N r IS).card ≤ (upperLayerShadow N r A).card := by
        rw [upperLayerShadow_eq_filter_layer IS, upperLayerShadow_eq_filter_layer A,
          hIS_slice, ← hL_def]
        have hmin := upperLayerShadow_min hL
        rwa [← ht_def] at hmin
      have := neighborhood_card_le_of_layers_upperShadow_le hrpos hA_le hIS_le hA_full
        hIS_full h_shadow
      rw [hIS_def] at this
      exact this

/-- The simplicial initial segment is fully compressed (lower-level saturated and
colex-shift fixed): it is a rank-downward-closed set, so no colex shift or level
fill can apply. -/
lemma simplicialInitSeg_isFullyCompressed {N m : ℕ} :
    IsFullyCompressed (simplicialInitSeg N m) := by
  constructor
  · -- lower level saturated
    intro x y hcard hy
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hlt : simplicialLt x y := by
      refine ⟨Or.inl hcard, ?_⟩
      simp only [simplicialLe, not_or]
      exact ⟨by omega, fun ⟨heq, _⟩ => by omega⟩
    exact lt_trans (rank_strictMono hlt) hy
  · -- colex shift fixed
    intro A' hshift
    obtain ⟨_, x, y, hx, hy, _, hlt, _⟩ := hshift
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hy (lt_trans (rank_strictMono hlt) hx)

/-- **Reduction step to a lower-saturated, down-fixed family** (no colex shift).
If `A` is not yet both coordinate-Down-fixed and lower-level saturated, one
coordinate Down-compression or one level-block fill gives a family of the same
size, no larger neighborhood, and strictly smaller potential.  Both moves are
sorry-free; no within-layer colex swap is used. -/
theorem lowerSatDownFixed_descent_step {N : ℕ} (A : Finset (Cube N))
    (h : ¬ (IsCoordinateDownFixed A ∧ IsLowerLevelSaturated A)) :
    ∃ A' : Finset (Cube N), A'.card = A.card ∧
      (neighborhood 1 A').card ≤ (neighborhood 1 A).card ∧
      compressionPotential A' < compressionPotential A := by
  by_cases hdf : IsCoordinateDownFixed A
  · have hl : ¬ IsLowerLevelSaturated A := fun hlsat => h ⟨hdf, hlsat⟩
    obtain ⟨A', U, V, hmove⟩ := not_lowerLevelSaturated_exists_paperLevelBlock A hdf hl
    exact ⟨A', paperLevelBlockMove_card hmove,
      paperLevelBlockMove_neighborhood_card_le hmove, paperLevelBlockMove_potential_lt hmove⟩
  · unfold IsCoordinateDownFixed at hdf
    push Not at hdf
    obtain ⟨i, hi⟩ := hdf
    have hne : coordinateDown i A ≠ A := by
      intro heq
      have hspec := coordinateDown_spec i A
      rw [heq] at hspec
      exact hi hspec
    exact ⟨coordinateDown i A, coordinateDown_card_eq (coordinateDown_spec i A),
      coordinateDown_neighborhood_card_le (coordinateDown_spec i A),
      coordinateDown_potential_lt_of_ne i A hne⟩

/-- Well-founded descent (strong induction on potential) to a lower-saturated,
Down-fixed family, using only coordinate-Down and level-block moves. -/
lemma exists_lowerSatDownFixed_le_aux {N : ℕ} :
    ∀ n (A : Finset (Cube N)), compressionPotential A = n →
      ∃ A₁ : Finset (Cube N), IsCoordinateDownFixed A₁ ∧ IsLowerLevelSaturated A₁ ∧
        A₁.card = A.card ∧ (neighborhood 1 A₁).card ≤ (neighborhood 1 A).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA
    by_cases h : IsCoordinateDownFixed A ∧ IsLowerLevelSaturated A
    · exact ⟨A, h.1, h.2, rfl, le_rfl⟩
    · obtain ⟨A', hcard, hnbhd, hpot⟩ := lowerSatDownFixed_descent_step A h
      rw [hA] at hpot
      obtain ⟨A₁, hdf, hls, hc, hn⟩ := ih (compressionPotential A') hpot A' rfl
      exact ⟨A₁, hdf, hls, hc.trans hcard, hn.trans hnbhd⟩

/-- **Every family compresses to a fully-compressed family of the same size whose
unit neighborhood is no larger** — now via the honest Kruskal–Katona jump.  Reduce
`A` to a lower-saturated, Down-fixed `A₁` (coordinate-Down + level-block moves,
sorry-free), then replace `A₁` by the simplicial initial segment of its size; the
neighborhood does not increase by `simplicialInitSeg_neighborhood_le_of_lowerSaturated`
(whose crux is the mathlib theorem `Finset.kruskal_katona` via `upperLayerShadow_min`). -/
lemma exists_fullyCompressed_le {N : ℕ} (A : Finset (Cube N)) :
    ∃ C : Finset (Cube N), IsFullyCompressed C ∧ C.card = A.card ∧
      (neighborhood 1 C).card ≤ (neighborhood 1 A).card := by
  obtain ⟨A₁, _hdf, hls, hc, hn⟩ :=
    exists_lowerSatDownFixed_le_aux (compressionPotential A) A rfl
  refine ⟨simplicialInitSeg N A₁.card, simplicialInitSeg_isFullyCompressed, ?_, ?_⟩
  · rw [card_simplicialInitSeg, min_eq_left (card_le_two_pow A₁), hc]
  · exact le_trans (simplicialInitSeg_neighborhood_le_of_lowerSaturated hls) hn

/-- **Single-family vertex isoperimetry (dimension `N`), via compression.**  The
simplicial initial segment of size `A.card` has the smallest unit neighborhood
among all families of that size.  This is `H N A.card ≤ |N A|` in unfolded form.

It is proved here *independently of the scalar Macaulay route*: by compressing `A`
to a fully-compressed family `C` (`exists_fullyCompressed_le`, boundary
non-increasing), which by `fullyCompressed_eq_initSeg` is the simplicial initial
segment of size `C.card = A.card`.  It does NOT use `harper_compression_descent`
or `harper_macaulay_min` (both downstream of this file).  The compression bottoms
out at the honest Kruskal–Katona jump: `exists_fullyCompressed_le` reduces `A` to
a lower-saturated, Down-fixed family (coordinate-Down + level-block moves) and
then replaces its top slice by the colex-initial segment, whose upper shadow is
minimal by mathlib's `Finset.kruskal_katona` (`upperLayerShadow_min`).  This
replaced the earlier single-swap colex descent, whose selection leaf
(`exists_colex_swap_upperLayerShadow_le_of_layerUpShifted`) was **false** —
up-shifted-but-not-colex-initial layers are stuck under single swaps
(`verify_colex_singlelayer_false_small.py`), so the Kruskal–Katona jump to the
whole initial segment is essential. -/
theorem simplicialInitSeg_neighborhood_card_min {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  obtain ⟨C, hC, hCcard, hCnbhd⟩ := exists_fullyCompressed_le A
  have hCeq : C = simplicialInitSeg N C.card := fullyCompressed_eq_initSeg C hC
  rw [← hCcard, ← hCeq]
  exact hCnbhd

/-- **Phase 1 — within-slice compression to simplicial slices** (the paper's
"compress each family to a Hamming sphere of its own size").

For arbitrary slices `(A, B)`, replacing each by the simplicial initial segment of
its own cardinality does not increase the two-slice boundary cost.  Individual
cardinalities are preserved (`card (simplicialInitSeg N A.card) = A.card`), so this
is a within-slice move and the second arguments of the two `max`'s are unchanged;
the inequality then follows term-by-term from single-family vertex isoperimetry
`simplicialInitSeg_neighborhood_card_min` applied to each slice.

This is now **sorry-free**: it is a direct consequence of the single-family
compression result `simplicialInitSeg_neighborhood_card_min`, which in turn rests
on the Kruskal–Katona jump `exists_fullyCompressed_le` (via `upperLayerShadow_min`
= mathlib `Finset.kruskal_katona`). -/
theorem compress_to_simplicial_pair {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N (simplicialInitSeg N A.card) (simplicialInitSeg N B.card)
      ≤ PairShadowCost N A B := by
  unfold PairShadowCost
  have hNA := simplicialInitSeg_neighborhood_card_min A
  have hNB := simplicialInitSeg_neighborhood_card_min B
  have hAcard : (simplicialInitSeg N A.card).card = A.card := by
    rw [card_simplicialInitSeg]; exact min_eq_left (card_le_two_pow A)
  have hBcard : (simplicialInitSeg N B.card).card = B.card := by
    rw [card_simplicialInitSeg]; exact min_eq_left (card_le_two_pow B)
  rw [hAcard, hBcard]
  exact Nat.add_le_add (max_le_max hNA le_rfl) (max_le_max hNB le_rfl)

/-- **Degenerate (`q = 0`) regime of the cross-slice exchange — proved by pure
cascade arithmetic, no Kruskal–Katona needed.**  When the canonical cascade split
of `a + b` puts the whole mass in one slice (`q = 0`, hence `p = a + b`), the
canonical cross-boundary cost `H N p + p` is already at most the arbitrary-split
functional.  The cascade arithmetic lives upstream in
`Macaulay.harper_bc_min_q_zero_core` (it depends only on
`Cube`/`Cascade`/`Macaulay`); this restatement discharges the
degenerate regime of the Phase-2 leaf below. -/
lemma H_exchange_q_zero {N a b p : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) (hp : p ≤ 2 ^ N)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit N (a + b) p 0) :
    H N p + p ≤ max (H N a) b + max (H N b) a :=
  harper_bc_min_q_zero_core N ha hb hp hb_le_a hpq hcasc

/-- **Phase-2 layer-window bridge (now sorry-free).**  On simplicial initial
segments the geometric two-slice cost `PairShadowCost` is exactly the explicit
layer-window cost `initSegPairLayerWindowCost` from `LayerWindows.lean`.

This is pure proof engineering, *not* Kruskal–Katona: on initial segments
`PairShadowCost` collapses to `max (H N a) b + max (H N b) a`
(`PairShadowCost_initSeg_eq_max_H`), and each boundary term `H N ·` is by
`neighborhoodLayerCost_eq_H` the finite sum over Hamming layers of the
neighborhood's per-layer window counts.  Filling the bridge removes the previous
"definition still missing" hole: `initSegPairLayerWindowCost` is now a real
layer-window sum, and the only remaining Phase-2 obligation is the genuine
cross-slice Kruskal–Katona minimization `cascade_layerWindowCost_min` below. -/
theorem PairShadowCost_initSeg_eq_layerWindowCost
    {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) =
      initSegPairLayerWindowCost N a b := by
  rw [PairShadowCost_initSeg_eq_max_H ha hb]
  unfold initSegPairLayerWindowCost
  rw [neighborhoodLayerCost_eq_H, neighborhoodLayerCost_eq_H]

/-- **The genuine residual Phase-2 Kruskal–Katona/Macaulay leaf.**

For a positive canonical cascade split `(p, q)` (with `q ≥ 1`) of `a + b`, the
canonical cascade pair has no larger *layer-window* cost than the arbitrary
sphere pair of sizes `(a, b)`.  Both sides are now genuine layer-window sums
(`initSegPairLayerWindowCost`, defined in `LayerWindows.lean`), so this is the
honest cross-slice Macaulay/Kruskal–Katona shadow-sum minimization stated over
explicit Hamming-layer windows.

This is the single remaining Phase-2 obligation.  By
`neighborhoodLayerCost_eq_H` it unfolds to the scalar exchange
`max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a`, but its *intended*
proof goes through the per-layer windows `layerCount N r (neighborhood 1 ·)`,
discharging each Hamming layer with the upstream single-layer Kruskal–Katona
minimum `upperShadowVal_numeric_min` / `upperLayerShadow_min`
(`KruskalKatona.lean`) and summing across layers.  The degenerate `q = 0`
companion is already discharged sorry-free by `H_exchange_q_zero`; this file does
**not** route through any downstream Harper/Macaulay-minimality theorem.  The
blueprint records that single-layer KK plus pure cascade telescoping is
insufficient on its own: the multi-layer Macaulay summation is the remaining
content. -/
structure CascadeLayerData (N r p q : ℕ) : Type where
  /-- The remainder of `p` after the binomial prefix through layer `r - 1`. -/
  pRem : ℕ
  /-- The remainder of `q` after the binomial prefix through layer `r - 2`. -/
  qRem : ℕ
  hp : p = binomPrefix N r + pRem
  hq : q = binomPrefix N (r - 1) + qRem
  hrange : pRem ≤ Nat.choose N r ∧ qRem ≤ Nat.choose N (r - 1)

/-- The assertion that `p` and `q` lie in the corresponding adjacent cascade windows. -/
def CascadeLayerWindow (N r p q : ℕ) : Prop :=
  Nonempty (CascadeLayerData N r p q)

/-- The signed slack between two pair-layer window costs. -/
noncomputable def PairLayerWindowSlack (N r a b p q : ℕ) : ℤ :=
  (PairLayerWindowCost N r a b : ℤ) - (PairLayerWindowCost N r p q : ℤ)

/-- The total pair-window slack summed over all relevant layers. -/
noncomputable def PairWindowSlackSum (N a b p q : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (N + 2), PairLayerWindowSlack N r a b p q

/-- **Per-layer Macaulay closed form of the pair-window cost (sorry-free bridge).**

The opaque double-`max` cost `PairLayerWindowCost N r a b` is, *layer by layer*,
the sum of the layer-`r` counts of two **nested simplicial initial segments**
`simplicialInitSeg N (max (H N a) b)` and `simplicialInitSeg N (max (H N b) a)`.

The identification uses only two sorry-free dictionary facts already in
`LayerWindows.lean`:

* `layerWindowShadowCost_eq_remainder_H`: the shadow window of `a` is the
  remainder window of the neighborhood size `H N a` (the unit neighborhood of an
  initial segment is again an initial segment); and
* `max_layerWindow_eq_union_card`: since simplicial initial segments are nested,
  the per-layer `max` of two remainder windows is the remainder window of the
  segment of the larger size.

This turns every cross-slice window into an honest **Macaulay layer window** of a
single initial segment, so the cascade leaf below is a genuine Kruskal–Katona
initial-segment comparison rather than a scalar `H` inequality (rule 3).  It
needs no capacity hypotheses. -/
lemma PairLayerWindowCost_eq_maxInitSeg (N r a b : ℕ) :
    PairLayerWindowCost N r a b
      = layerWindowRemainder N r (max (H N a) b)
        + layerWindowRemainder N r (max (H N b) a) := by
  unfold PairLayerWindowCost
  rw [layerWindowShadowCost_eq_remainder_H, layerWindowShadowCost_eq_remainder_H]
  simp only [layerWindowRemainder]
  rw [max_layerWindow_eq_union_card, max_layerWindow_eq_union_card]

/-- **Suffix layer-window sum in closed form (sorry-free Macaulay bridge).**

The upper-tail (Hamming layers `≥ k`) sum of the per-layer pair-window cost is,
exactly, the sum of the two truncated Macaulay neighborhood values
`max (H N a) b - binomPrefix N k` and `max (H N b) a - binomPrefix N k`
(truncated `ℕ` subtraction).  This is the composition of the two proved
dictionary facts `PairLayerWindowCost_eq_maxInitSeg` (each layer cost is a sum of
two nested initial-segment layer counts) and `suffix_layerWindowRemainder_eq`
(the suffix sum of an initial segment's layer counts is `m - binomPrefix N k`).
It turns the opaque suffix window sum into an explicit truncated-neighborhood
comparison over the Macaulay layer threshold `binomPrefix N k`. -/
lemma sum_Ico_PairLayerWindowCost_eq (N a b k : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), PairLayerWindowCost N r a b
      = (max (H N a) b - binomPrefix N k) + (max (H N b) a - binomPrefix N k) := by
  have hMa : max (H N a) b ≤ 2 ^ N := max_le (H_le_cube N a) hb
  have hMb : max (H N b) a ≤ 2 ^ N := max_le (H_le_cube N b) ha
  rw [Finset.sum_congr rfl (fun r _ => PairLayerWindowCost_eq_maxInitSeg N r a b),
      Finset.sum_add_distrib,
      suffix_layerWindowRemainder_eq N (max (H N a) b) k hMa,
      suffix_layerWindowRemainder_eq N (max (H N b) a) k hMb]

/-- **Suffix layer-window sum as a Hamming upper-tail count of a neighborhood union.**

The upper-tail (Hamming layers `≥ k`) sum of the remainder windows of the value
`max (H N x) y` is exactly the number of vertices of cardinality `≥ k` in the
union of the unit neighborhood of the initial segment of size `x` with the
initial segment of size `y`.  This is a sorry-free dictionary identity: the unit
neighborhood of an initial segment is again an initial segment
(`neighborhood_initSeg_eq`), initial segments are nested so their union is the
initial segment of the larger size, and the suffix layer sum of an initial
segment counts exactly its vertices of cardinality `≥ k`
(`sum_Ico_layerCount_eq_filter_card_ge`).  It converts the opaque window sum into
the genuine set-family Hamming upper-tail count on which the dimension recursion
operates. -/
lemma sum_Ico_layerWindowRemainder_max_eq (N x y k : ℕ) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r (max (H N x) y)
      = ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card := by
  have hset : neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y
      = simplicialInitSeg N (max (H N x) y) := by
    rw [neighborhood_initSeg_eq]
    rcases le_total (H N x) y with h | h
    · rw [max_eq_right h, Finset.union_eq_right.mpr (initSeg_nested h)]
    · rw [max_eq_left h, Finset.union_eq_left.mpr (initSeg_nested h)]
  rw [hset,
      ← sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N (max (H N x) y))]
  rfl

/-- **The genuine Kruskal–Katona vertex-boundary upper-tail leaf (set-family form).**

This is the honest Frankl–Füredi/Macaulay content of `cascade_KK_tail_min`, stated
directly on Boolean-cube set families, Hamming layers, and unit neighborhoods —
no `ℤ`, no window bookkeeping, no scalar `H` arithmetic.  For a canonical cascade
split `(p, q)` of `a + b` that Macaulay-interleaves the arbitrary split `(a, b)`,
the number of high-Hamming-layer (`card ≥ k`) vertices in the two cross-slice
neighborhood unions of `(p, q)` is no larger than that of `(a, b)`:
`|{z ∈ N(IS p) ∪ IS q : |z| ≥ k}| + |{z ∈ N(IS q) ∪ IS p : |z| ≥ k}|`
`≤ |{z ∈ N(IS a) ∪ IS b : |z| ≥ k}| + |{z ∈ N(IS b) ∪ IS a : |z| ≥ k}|`,
where `IS m := simplicialInitSeg N m`.

At `k = 0` this is Harper's vertex-boundary recursion (`neighborhood_succ` gives
`|N(IS p) ∪ IS q| + |N(IS q) ∪ IS p| = H (N+1) (a+b)`); for `k ≥ 1` it is the
same comparison restricted to the upper Hamming layers, the Macaulay grid tail.
The faithful proof is the dimension recursion on `N` (`H_succ_slice` /
`neighborhood_succ`): slicing at the top coordinate reduces the level-`N`
upper-tail count with cutoff `k` to the level-`(N-1)` counts of the two slices
with cutoffs `k` (slice 0) and `k - 1` (slice 1), and the interleaving
majorization is inherited by the slice sub-splits via `CascadeInterleaves.lower_succ`.
This is the exact `dimension recursion + single-layer KK` route requested by the
Frankl–Füredi PDF, not a scalar reduction. -/
lemma slice0_union {N : ℕ} (A B : Finset (Cube (N + 1))) :
    slice0 (A ∪ B) = slice0 A ∪ slice0 B := by
  ext x
  simp [slice0]

lemma slice1_union {N : ℕ} (A B : Finset (Cube (N + 1))) :
    slice1 (A ∪ B) = slice1 A ∪ slice1 B := by
  ext x
  simp [slice1]

lemma slice0_simplicialInitSeg_eq_cascadeSplit {N x p q : ℕ} (h : CascadeSplit N x p q) :
    slice0 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N p := by
  rw [slice0_initSeg_eq, (slice_card_eq_cascade h).1]

lemma slice1_simplicialInitSeg_eq_cascadeSplit {N x p q : ℕ} (h : CascadeSplit N x p q) :
    slice1 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N q := by
  rw [slice1_initSeg_eq, (slice_card_eq_cascade h).2]

lemma cascade_upper_slice_subset_neighborhood_lower {N x p q : ℕ}
    (h : CascadeSplit N x p q) :
    simplicialInitSeg N q ⊆ neighborhood 1 (simplicialInitSeg N p) := by
  intro z hz
  have hqp : q ≤ p := cascade_q_le_p h
  have hz_p : z ∈ simplicialInitSeg N p := initSeg_nested hqp hz
  rw [mem_neighborhood_iff]
  exact ⟨z, hz_p, by simp [hDist]⟩

lemma slice0_neighborhoodUnion {N x y px qx py qy : ℕ}
    (hx : CascadeSplit N x px qx) (hy : CascadeSplit N y py qy) :
    slice0 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N px) ∪ simplicialInitSeg N py := by
  rw [slice0_union, slice0_neighborhood,
    slice0_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hx,
    slice0_simplicialInitSeg_eq_cascadeSplit hy]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_left _
          (cascade_upper_slice_subset_neighborhood_lower hx hz)
    · exact Finset.mem_union_right _ hz
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    · exact Finset.mem_union_right _ hz

lemma slice1_neighborhoodUnion {N x y px qx py qy : ℕ}
    (hx : CascadeSplit N x px qx) (hy : CascadeSplit N y py qy) :
    slice1 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N qx) ∪ simplicialInitSeg N px ∪
          simplicialInitSeg N qy := by
  rw [slice1_union, slice1_neighborhood,
    slice0_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hy]

lemma card_filter_neighborhoodUnion_initSeg (N x y k : ℕ) (hy : y ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card
    = max (H N x) y - binomPrefix N k := by
  rw [← sum_Ico_layerWindowRemainder_max_eq]
  exact suffix_layerWindowRemainder_eq N (max (H N x) y) k (max_le (H_le_cube N x) hy)

lemma card_filter_neighborhoodUnion_initSeg_three (N x y z k : ℕ)
    (h_le : H N x ≤ y) (hy : y ≤ 2 ^ N) (hz : z ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y ∪ simplicialInitSeg N z).filter
          (fun z => k ≤ z.card)).card
    = max y z - binomPrefix N k := by
  have hset : neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y ∪ simplicialInitSeg N z
      = simplicialInitSeg N (max y z) := by
    rw [neighborhood_initSeg_eq]
    rw [Finset.union_eq_right.mpr (initSeg_nested h_le)]
    rcases le_total y z with hyz | hzy
    · rw [max_eq_right hyz, Finset.union_eq_right.mpr (initSeg_nested hyz)]
    · rw [max_eq_left hzy, Finset.union_eq_left.mpr (initSeg_nested hzy)]
  rw [hset, ← sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N (max y z))]
  exact suffix_layerWindowRemainder_eq N (max y z) k (max_le hy hz)

/-- **Phase-3 cascade exchange (sorry-free).**

A pair of simplicial initial segments `(simplicialInitSeg N a, simplicialInitSeg N b)`
of total `a + b` can be compressed across the top coordinate to *the* canonical
cascade pair `(simplicialInitSeg N p, simplicialInitSeg N q)` of the same total,
without increasing the two-slice boundary cost.

The proof embeds both pairs into the `(N + 1)`-cube via `embeddedPair`, where the
two-slice cost becomes a plain neighborhood size; the canonical pair embeds to the
simplicial initial segment of size `a + b` (`embeddedPair_eq_of_slice_eq`), so the
cost comparison is exactly the dimension-`(N + 1)` Harper minimality
`simplicialInitSeg_neighborhood_card_min`.

The existence/total parts are immediate from the chosen canonical witnesses. -/
theorem cascade_split_reaches_canonical {N : ℕ} (a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = a + b ∧
      PairShadowCost N A' B'
        ≤ PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) := by
  have htot : a + b ≤ 2 ^ (N + 1) := by
    have h2 : (2 : ℕ) ^ (N + 1) = 2 ^ N + 2 ^ N := by ring
    omega
  obtain ⟨p, q, hp, hq, hsum, hcasc⟩ := exists_cascade_split N (a + b) htot
  use simplicialInitSeg N p, simplicialInitSeg N q
  have hpcard : (simplicialInitSeg N p).card = p := by
    rw [card_simplicialInitSeg, min_eq_left hp]
  have hqcard : (simplicialInitSeg N q).card = q := by
    rw [card_simplicialInitSeg, min_eq_left hq]
  constructor
  · exact ⟨p, q, by rw [hpcard, hqcard, hsum]; exact hcasc, rfl, rfl⟩
  · constructor
    · rw [hpcard, hqcard]
      exact hsum
    · let A := simplicialInitSeg N a
      let B := simplicialInitSeg N b
      let F := embeddedPair N A B
      have hFcard : F.card = a + b := by
        rw [embeddedPair_card, card_simplicialInitSeg, card_simplicialInitSeg]
        · rw [min_eq_left ha, min_eq_left hb]
      have hF_nbhd : PairShadowCost N A B = (neighborhood 1 F).card := by
        rw [PairShadowCost_initSeg_eq_max_H ha hb]
        exact (neighborhood_embeddedPair_initSeg_card ha hb).symm
      let P := simplicialInitSeg N p
      let Q := simplicialInitSeg N q
      let C := embeddedPair N P Q
      have hC_is_init : C = simplicialInitSeg (N + 1) (a + b) := by
        symm
        apply embeddedPair_eq_of_slice_eq
        · rw [slice0_initSeg_eq]
          have h0card := (slice_card_eq_cascade hcasc).1
          rw [h0card]
        · rw [slice1_initSeg_eq]
          have h1card := (slice_card_eq_cascade hcasc).2
          rw [h1card]
      have hC_nbhd : PairShadowCost N P Q = (neighborhood 1 C).card := by
        rw [PairShadowCost_initSeg_eq_max_H hp hq]
        exact (neighborhood_embeddedPair_initSeg_card hp hq).symm
      have h_min := simplicialInitSeg_neighborhood_card_min F
      rw [hFcard] at h_min
      rw [← hC_is_init] at h_min
      rw [hF_nbhd, hC_nbhd]
      exact h_min

/-- **Frankl–Füredi terminalization theorem.**

For any two slice families `(A, B)` there is *the* canonical cascade pair
`(A', B')` of the same total volume `|A| + |B|` with two-slice boundary cost no
larger than that of `(A, B)`.  This is the genuine set-family heart of the
Frankl–Füredi proof of Harper's theorem, stated as an existence/termination
statement so that the downstream scalar Macaulay leaves are *corollaries* of it
rather than the root of the development.

It is now assembled (sorry-free at this level) from the two PDF phases:

* `compress_to_simplicial_pair` — compress the arbitrary slices to simplicial
  initial segments of their own sizes (dimension-`N` single-family Harper);
* `cascade_split_reaches_canonical` — compress the resulting sphere pair across the
  top coordinate to the canonical cascade split (Kruskal–Katona/Macaulay).

Everything Harper-facing (`franklFuredi_pairedCompression_exchange`,
`H_exchange_max_form_pos`, `H_shadow_LE_sum` / `H_shadow_GT_sum`, the scalar leaves
`macaulay_extremal_pos_step_LE/GT`, `harper_macaulay_min`,
`harper_compression_descent`, `harper_vertex_iso`) is a sorry-free consequence of
these two phases. -/
theorem pairedCompression_reaches_canonical {N : ℕ} (A B : Finset (Cube N)) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = A.card + B.card ∧
      PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  have hphase1 :
      PairShadowCost N (simplicialInitSeg N A.card) (simplicialInitSeg N B.card)
        ≤ PairShadowCost N A B := compress_to_simplicial_pair A B
  obtain ⟨A', B', hcan, htot, hphase2⟩ :=
    cascade_split_reaches_canonical A.card B.card (card_le_two_pow A) (card_le_two_pow B)
  exact ⟨A', B', hcan, htot, le_trans hphase2 hphase1⟩

/-- The Frankl-Füredi exchange theorem: arbitrary slices `A, B` can be
paired-compressed into the canonical cascade split `(p, q)` of the total volume
`|A| + |B|` without increasing the two-slice boundary cost.

This is now a **sorry-free bridge** from the set-family terminalization theorem
`pairedCompression_reaches_canonical`: the reached canonical pair has the same
total volume `|A| + |B|`, so by `cascadeSplit_unique` its two slices are exactly
the canonical initial segments `simplicialInitSeg N p`, `simplicialInitSeg N q` of
the cascade split `(p, q)`, and the cost bound transfers verbatim.  It no longer
routes through `harper_compression_descent`, so the dependency direction is the
genuine PDF one (paired compression ⟹ scalar Macaulay leaves). -/
theorem franklFuredi_pairedCompression_exchange {N : ℕ} (A B : Finset (Cube N))
    (p q : ℕ) (hpq : CascadeSplit N (A.card + B.card) p q) :
    PairShadowCost N (simplicialInitSeg N p) (simplicialInitSeg N q) ≤
      PairShadowCost N A B := by
  obtain ⟨A', B', hcan, htot, hcost⟩ := pairedCompression_reaches_canonical A B
  obtain ⟨p', q', hpq', hA'eq, hB'eq⟩ := hcan
  rw [htot] at hpq'
  obtain ⟨hpp, hqq⟩ := cascadeSplit_unique hpq hpq'
  rw [hA'eq, hB'eq, ← hpp, ← hqq] at hcost
  exact hcost

end BooleanIsoperimetry
