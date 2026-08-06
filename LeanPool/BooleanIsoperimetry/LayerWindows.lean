/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.KruskalKatona

/-! # Layer-window accounting for the cross-slice Kruskal–Katona bridge.

This module provides the *layer-window* (Macaulay) decomposition of the unit
neighborhood of a simplicial initial segment, organized by Hamming layer.  It is
the language in which the cross-slice exchange bridge
(`PairShadowCost_initSeg_eq_layerWindowCost`, `Compression.lean`) relates the
geometric two-slice cost to the single-layer Kruskal–Katona minimum
`upperShadowVal_numeric_min` (`KruskalKatona.lean`).

The key object is `neighborhoodLayerCost N a`: the size of the unit neighborhood
of `simplicialInitSeg N a`, written as an *explicit finite sum over Hamming
layers* of the per-layer counts `layerCount N r (·)`.  This sum is provably equal
to `H N a` (`neighborhoodLayerCost_eq_H`), so it is a faithful re-expression of
the boundary functional `H` that exposes the per-layer windows the
Kruskal–Katona core operates on — not an opaque scalar.  The pair functional
`initSegPairLayerWindowCost` then assembles the two slice costs exactly the way
`PairShadowCost` does on simplicial initial segments. -/

namespace BooleanIsoperimetry

open Finset

/-- The Hamming-layer-`r` part of a family: the sets of cardinality `r` in `A`. -/
noncomputable def layerPart (N r : ℕ) (A : Finset (Cube N)) : Finset (Cube N) :=
  A.filter (fun x => x.card = r)

/-- The number of layer-`r` sets in `A` (the layer-`r` window count). -/
noncomputable def layerCount (N r : ℕ) (A : Finset (Cube N)) : ℕ :=
  (layerPart N r A).card

/-- Layers above the top Hamming level of the `N`-cube are empty. -/
lemma layerCount_eq_zero_of_N_lt {N r : ℕ} (hNr : N < r) (A : Finset (Cube N)) :
    layerCount N r A = 0 := by
  unfold layerCount layerPart
  rw [Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_filter] at hx
    have hle : x.card ≤ N := by
      have := Finset.card_le_univ x
      simpa [Fintype.card_fin] using this
    omega
  · intro h
    simp at h

/-- **Layer-window form of the boundary functional `H`.**

The unit neighborhood of the simplicial initial segment of size `a`, counted as a
finite sum over Hamming layers `r = 0, …, N+1` of its per-layer window counts.
Every layer summand `layerCount N r (neighborhood 1 (simplicialInitSeg N a))` is
the number of boundary vertices in Hamming layer `r`; for an initial segment the
fully covered low layers contribute `Nat.choose N r` and the single partially
covered top layer contributes the genuine *upper-shadow window*.  This is exactly
the Macaulay layer accounting, and it equals `H N a` (`neighborhoodLayerCost_eq_H`). -/
noncomputable def neighborhoodLayerCost (N a : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (N + 2), layerCount N r (neighborhood 1 (simplicialInitSeg N a))

/-- The layer-window sum reconstructs the boundary functional `H`: summing the
per-layer window counts of the neighborhood over all Hamming layers recovers its
cardinality `H N a`.  (Every vertex of the `N`-cube has cardinality `≤ N < N+2`,
so the layers `0, …, N+1` partition the neighborhood.) -/
lemma neighborhoodLayerCost_eq_H (N a : ℕ) :
    neighborhoodLayerCost N a = H N a := by
  unfold neighborhoodLayerCost layerCount layerPart H
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := fun x : Cube N => x.card)
    (t := Finset.range (N + 2))
    (fun x _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have hle : x.card ≤ N := by
        have := Finset.card_le_univ x
        simpa [Fintype.card_fin] using this
      omega)

/-- The per-layer window counts of the neighborhood are the layer counts of the
*neighborhood-as-initial-segment* `simplicialInitSeg N (H N a)`.  This makes the
windows manifestly the Macaulay/binomial windows that the Kruskal–Katona core
`upperShadowVal_numeric_min` minimizes layer by layer. -/
lemma layerCount_neighborhood_initSeg (N r a : ℕ) :
    layerCount N r (neighborhood 1 (simplicialInitSeg N a)) =
      layerCount N r (simplicialInitSeg N (H N a)) := by
  rw [neighborhood_initSeg_eq]

/-- **Layer-window pair cost.**  The two-slice Frankl–Füredi cost of the
simplicial initial segments of sizes `a` and `b`, written in layer-window terms:
each slice's boundary is the layer-window neighborhood cost
`neighborhoodLayerCost`, and the cross terms are the slice volumes, exactly as in
`PairShadowCost`.  By `neighborhoodLayerCost_eq_H` this equals the scalar
`max (H N a) b + max (H N b) a` on initial segments, but it is *defined* through
the explicit per-layer windows so the cross-slice Kruskal–Katona minimization can
be carried out layer by layer. -/
noncomputable def initSegPairLayerWindowCost (N a b : ℕ) : ℕ :=
  max (neighborhoodLayerCost N a) b + max (neighborhoodLayerCost N b) a

/-- The number of layer-`r` sets in the initial segment of size `a`. -/
noncomputable def layerWindowRemainder (N r a : ℕ) : ℕ :=
  layerCount N r (simplicialInitSeg N a)

/-- The number of layer-`r` sets in the neighborhood of the initial segment of size `a`.
This exactly matches the Kruskal--Katona upper shadow (plus the elements of the set itself). -/
noncomputable def layerWindowShadowCost (N r a : ℕ) : ℕ :=
  layerCount N r (neighborhood 1 (simplicialInitSeg N a))

/-- The cross-slice layer window cost for a single Hamming layer `r`. -/
noncomputable def PairLayerWindowCost (N r a b : ℕ) : ℕ :=
  max (layerWindowShadowCost N r a) (layerWindowRemainder N r b) +
  max (layerWindowShadowCost N r b) (layerWindowRemainder N r a)

/-- The remainder window is zero above the top Hamming layer. -/
lemma layerWindowRemainder_eq_zero_of_N_lt {N r a : ℕ} (hNr : N < r) :
    layerWindowRemainder N r a = 0 := by
  unfold layerWindowRemainder
  exact layerCount_eq_zero_of_N_lt hNr (simplicialInitSeg N a)

/-- The shadow-cost window is zero above the top Hamming layer. -/
lemma layerWindowShadowCost_eq_zero_of_N_lt {N r a : ℕ} (hNr : N < r) :
    layerWindowShadowCost N r a = 0 := by
  unfold layerWindowShadowCost
  exact layerCount_eq_zero_of_N_lt hNr (neighborhood 1 (simplicialInitSeg N a))

/-- The pair layer-window cost is zero above the top Hamming layer. -/
lemma PairLayerWindowCost_eq_zero_of_N_lt {N r a b : ℕ} (hNr : N < r) :
    PairLayerWindowCost N r a b = 0 := by
  unfold PairLayerWindowCost
  rw [layerWindowShadowCost_eq_zero_of_N_lt hNr,
      layerWindowRemainder_eq_zero_of_N_lt hNr,
      layerWindowShadowCost_eq_zero_of_N_lt hNr,
      layerWindowRemainder_eq_zero_of_N_lt hNr]
  simp

lemma max_layerWindow_eq_union_card (N r X Y : ℕ) :
    max (layerCount N r (simplicialInitSeg N X)) (layerCount N r (simplicialInitSeg N Y)) =
    layerCount N r (simplicialInitSeg N (max X Y)) := by
  rcases le_total X Y with hXY | hYX
  · rw [max_eq_right hXY]
    have hsub : simplicialInitSeg N X ⊆ simplicialInitSeg N Y :=
      initSeg_nested hXY
    have hsub_layer :
        layerPart N r (simplicialInitSeg N X) ⊆ layerPart N r (simplicialInitSeg N Y) :=
      Finset.filter_subset_filter _ hsub
    unfold layerCount
    rw [max_eq_right (Finset.card_le_card hsub_layer)]
  · rw [max_eq_left hYX]
    have hsub : simplicialInitSeg N Y ⊆ simplicialInitSeg N X :=
      initSeg_nested hYX
    have hsub_layer :
        layerPart N r (simplicialInitSeg N Y) ⊆ layerPart N r (simplicialInitSeg N X) :=
      Finset.filter_subset_filter _ hsub
    unfold layerCount
    rw [max_eq_left (Finset.card_le_card hsub_layer)]

/-- The per-layer window counts of any family `A` sum to its cardinality over the
Hamming layers `0, …, N+1` (every vertex of the `N`-cube has cardinality `≤ N`).
This is the reusable fiberwise-partition identity already used inside
`neighborhoodLayerCost_eq_H`. -/
lemma sum_layerCount_eq_card (N : ℕ) (A : Finset (Cube N)) :
    ∑ r ∈ Finset.range (N + 2), layerCount N r A = A.card := by
  unfold layerCount layerPart
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := fun x : Cube N => x.card)
    (t := Finset.range (N + 2))
    (fun x _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have hle : x.card ≤ N := by
        have := Finset.card_le_univ x
        simpa [Fintype.card_fin] using this
      omega)

/-- **Per-layer max collapses to the global boundary value.**  Summing the
per-layer `max` of the shadow-cost window of `a` against the remainder window of
`b` over all Hamming layers recovers `max (H N a) b`, provided `b ≤ 2^N`.

The key structural fact is that *both* per-layer windows are layer counts of
nested simplicial initial segments: the shadow window of `a` is the layer count
of `simplicialInitSeg N (H N a)` (`layerCount_neighborhood_initSeg`), and the
remainder window of `b` is the layer count of `simplicialInitSeg N b`.  Initial
segments are nested, so on each layer the two counts are comparable and their
`max` is the layer count of `simplicialInitSeg N (max (H N a) b)`
(`max_layerWindow_eq_union_card`).  Summing over layers gives the cardinality
`min (max (H N a) b) (2^N) = max (H N a) b`, the last equality using `b ≤ 2^N`
and `H N a ≤ 2^N`.  This is exactly the statement that the global `max` commutes
with the per-layer decomposition for nested initial-segment windows. -/
lemma sum_max_shadowRemainder (N a b : ℕ) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.range (N + 2),
        max (layerWindowShadowCost N r a) (layerWindowRemainder N r b)
      = max (H N a) b := by
  have hstep : ∀ r ∈ Finset.range (N + 2),
      max (layerWindowShadowCost N r a) (layerWindowRemainder N r b)
        = layerCount N r (simplicialInitSeg N (max (H N a) b)) := by
    intro r _
    unfold layerWindowShadowCost layerWindowRemainder
    rw [layerCount_neighborhood_initSeg, max_layerWindow_eq_union_card]
  rw [Finset.sum_congr rfl hstep, sum_layerCount_eq_card, card_simplicialInitSeg]
  exact min_eq_left (max_le (H_le_cube N a) hb)

/-! ## Kruskal–Katona identification of the layer windows

These lemmas connect the layer-window objects above to the single-layer
Kruskal–Katona core (`upperShadowVal_numeric_min` / `upperLayerShadow_min` in
`KruskalKatona.lean`).  They make the per-layer shadow windows manifestly the
KK upper-shadow windows, so the cross-slice leaf `cascade_window_sum_min`
(`Compression.lean`) routes through the genuine Kruskal–Katona minimum rather
than through opaque scalar `H` arithmetic. -/

/-- The shadow-cost window of `a` in layer `r` is the *remainder* window of the
neighborhood size `H N a` in the same layer: the unit neighborhood of an initial
segment is again an initial segment (`neighborhood_initSeg_eq`), so its per-layer
counts are literally the per-layer counts of `simplicialInitSeg N (H N a)`. -/
lemma layerWindowShadowCost_eq_remainder_H (N r a : ℕ) :
    layerWindowShadowCost N r a = layerWindowRemainder N r (H N a) := by
  unfold layerWindowShadowCost layerWindowRemainder
  rw [layerCount_neighborhood_initSeg]

/-- The layer-`r` part of a simplicial initial segment is `r`-uniform. -/
lemma layerPart_initSeg_uniform (N r a : ℕ) :
    ∀ x ∈ layerPart N r (simplicialInitSeg N a), x.card = r := by
  intro x hx
  simp only [layerPart, Finset.mem_filter] at hx
  exact hx.2

/-- The layer-`r` window of an initial segment never exceeds the number of
`r`-subsets `Nat.choose N r`. -/
lemma layerWindowRemainder_le_choose (N r a : ℕ) :
    layerWindowRemainder N r a ≤ Nat.choose N r := by
  unfold layerWindowRemainder layerCount
  exact card_le_choose_of_uniform (layerPart_initSeg_uniform N r a)

/-- **Thin Kruskal–Katona wrapper in layer-window language.**  For any `r`-uniform
family `A` with `r ≥ 1`, the numeric upper-shadow value at its own cardinality is
a lower bound for the size of its actual upper shadow in layer `r+1`.  This is
exactly `upperShadowVal_numeric_min` specialized to `t := A.card`, packaged so
the cross-slice layer-window leaf can invoke single-layer KK directly: the
simplicial layer initial segment of the same size achieves this lower bound, so
no `r`-uniform family has a smaller layer-`(r+1)` upper shadow. -/
lemma layerWindowShadowCost_KK_min {N r : ℕ} (hr : 1 ≤ r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    upperShadowVal N r A.card ≤ (upperLayerShadow N r A).card :=
  upperShadowVal_numeric_min hr (card_le_choose_of_uniform hA) hA rfl

/-- **Layer-window decomposition of the pair cost.**  The
scalar two-slice cost `initSegPairLayerWindowCost N a b` is the sum over Hamming
layers of the per-layer pair window costs `PairLayerWindowCost N r a b`.  This is
the bookkeeping bridge exposing the Macaulay/Kruskal–Katona layer windows that
the cross-slice leaf `cascade_window_sum_min` (`Compression.lean`) operates on
it requires `a, b ≤ 2^N` (otherwise the literal cross terms `a`/`b` exceed the
saturated initial-segment cardinality `2^N` and the identity fails). -/
lemma initSegPairLayerWindowCost_eq_KK_window_sum (N a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    initSegPairLayerWindowCost N a b =
      ∑ r ∈ Finset.range (N + 2), PairLayerWindowCost N r a b := by
  unfold initSegPairLayerWindowCost PairLayerWindowCost
  rw [Finset.sum_add_distrib, sum_max_shadowRemainder N a b hb,
      sum_max_shadowRemainder N b a ha, neighborhoodLayerCost_eq_H,
      neighborhoodLayerCost_eq_H]

/-! ## Suffix (upper-tail) closed form of the Macaulay layer windows

The cascade suffix leaf compares *upper-tail* sums `∑_{r ≥ k}` of the per-layer
remainder windows.  The following two lemmas give a completely explicit closed
form for such a tail: it is the number of vertices of cardinality `≥ k` in the
simplicial initial segment, and for a segment of size `m ≤ 2^N` this is exactly
the truncated difference `m - binomPrefix N k`.  Both are Macaulay
dictionary facts (the simplicial order fills the lower Hamming layers first, so
the layer-`< k` part of `simplicialInitSeg N m` is `simplicialInitSeg N (binomPrefix N k)`
capped at `m`, via `rank_lt_binomPrefix_iff`). -/

/-
A suffix of Hamming layers counts exactly the elements of cardinality `≥ k`
(every vertex of the `N`-cube has cardinality `≤ N < N + 2`).
-/
lemma sum_Ico_layerCount_eq_filter_card_ge (N k : ℕ) (A : Finset (Cube N)) :
    ∑ r ∈ Finset.Ico k (N + 2), layerCount N r A
      = (A.filter (fun x => k ≤ x.card)).card := by
  rw [show { x ∈ A | k ≤ #x } =
      Finset.biUnion (Finset.Ico k (N + 2) ) (fun r => Finset.filter (fun x => x.card = r) A)
    from ?_, Finset.card_biUnion]
  · rfl
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop
  · ext x; simp +decide only [mem_filter, mem_biUnion, mem_Ico, exists_eq_right_right']
    exact ⟨ fun h =>
      ⟨ ⟨ h.2, by linarith [show #x ≤ N by simpa using Finset.card_le_univ x] ⟩,
        h.1 ⟩,
      fun h => ⟨ h.2, h.1.1 ⟩ ⟩

/-
**Suffix closed form of the Macaulay remainder window.**  For an initial
segment of size `m ≤ 2^N`, the upper-tail sum (Hamming layers `≥ k`) of its
per-layer counts is the truncated difference `m - binomPrefix N k`.  This is the
reusable KK/Macaulay lever the cascade suffix leaf runs on.
-/
lemma suffix_layerWindowRemainder_eq (N m k : ℕ) (hm : m ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m
      = m - binomPrefix N k := by
  -- By definition of `layerWindowRemainder`, the sum is the cardinality of the set of
  -- elements in the initial segment with rank at least `binomPrefix N k`.
  have h_card : ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m =
      (simplicialInitSeg N m \ simplicialInitSeg N (min m (binomPrefix N k))).card := by
    have hsum :
        ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m =
          ((simplicialInitSeg N m).filter (fun x => k ≤ x.card)).card := by
      simpa [layerWindowRemainder] using
        sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N m)
    have hfilter :
        (simplicialInitSeg N m).filter (fun x => k ≤ x.card) =
          simplicialInitSeg N m \ simplicialInitSeg N (min m (binomPrefix N k)) := by
      ext x
      simp only [simplicialInitSeg, mem_filter, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨hrank, hcard⟩
        refine ⟨hrank, ?_⟩
        intro hmin
        have hrank_binom : rank x < binomPrefix N k := lt_of_lt_of_le hmin (min_le_right _ _)
        have hcard_lt : x.card < k :=
          (rank_lt_binomPrefix_iff (n := N) (c := k) x).mp hrank_binom
        omega
      · rintro ⟨hrank, hnot⟩
        refine ⟨hrank, ?_⟩
        exact Nat.le_of_not_lt fun hcard_lt =>
          hnot (lt_min hrank ((rank_lt_binomPrefix_iff (n := N) (c := k) x).mpr hcard_lt))
    rw [hsum, hfilter]
  rw [h_card, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr, card_simplicialInitSeg, card_simplicialInitSeg]
  · grind
  · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1,
      lt_of_lt_of_le (Finset.mem_filter.mp hx |>.2) (min_le_left _ _) ⟩

/-- **Hardy–Littlewood–Pólya pair majorization for truncated (`ℕ`) tails.**

For two `ℕ`-pairs, if the pair `(a', b')` weakly majorizes `(a, b)` — i.e. the
sums satisfy `a + b ≤ a' + b'` *and* the maxima satisfy `max a b ≤ max a' b'` —
then every truncated-tail pair sum is dominated:
`(a - c) + (b - c) ≤ (a' - c) + (b' - c)` for all thresholds `c` (`ℕ` truncated
subtraction).  This is the two-point Hardy–Littlewood–Pólya / Karamata fact for
the increasing convex family `x ↦ (x - c)⁺`, specialised to a pair; it is the
*final pair-combination step* of any Macaulay upper-tail argument once the two
neighborhood-slice values have been compared.

Caveat (recorded so it is not misused).  The two hypotheses are **strictly
stronger** than what the cascade tail leaf `cascade_KK_tail_min` actually needs:
that leaf only requires the truncated inequality at the *Macaulay grid points*
`c = binomPrefix N k`, and the max-slice hypothesis `max a b ≤ max a' b'` is
**not** available there — it is verified false on genuine cascade configurations
(smallest witness `N = 3, a = b = 2`, neighborhood slices `(7,4)` vs `(6,6)`; see
`verify_cascade_KK_tail_weakMaj_insufficient_small.py`).  Hence this lemma is a
*sound but incomplete* tool for that leaf: it closes the tail only in the
weak-majorized regime, and the genuine remaining content lives in the grid
structure of `H`, to be handled by the dimension recursion `H_succ_cascade` and
the single-layer minimum `layerWindowShadowCost_KK_min`. -/
lemma pair_tsub_le_of_sum_le_of_max_le {a b a' b' c : ℕ}
    (hsum : a + b ≤ a' + b') (hmax : max a b ≤ max a' b') :
    (a - c) + (b - c) ≤ (a' - c) + (b' - c) := by
  omega

/-! ## Dimension recursion for the Hamming upper-tail count.

The following lemma is the reusable slice-recursion brick requested for the
dimension induction of the cascade upper-tail leaf.  It says the number of
vertices of Hamming weight `≥ k` in a family `A ⊆ Cube (N+1)` splits, along the
top coordinate, into the weight-`≥ k` count of the lower slice `slice0 A` and the
weight-`≥ k-1` count of the upper slice `slice1 A` (the upper slice already
carries the top coordinate, so its members have one extra active coordinate).
This is the tail-count analogue of `slice_card_add`. -/

lemma tailCount_succ_slice {N : ℕ} (k : ℕ) (A : Finset (Cube (N + 1))) :
    (A.filter (fun z => k ≤ z.card)).card
      = ((slice0 A).filter (fun z => k ≤ z.card)).card
        + ((slice1 A).filter (fun z => k - 1 ≤ z.card)).card := by
  -- Decompose A into the two slices as described.
  have h_decomp : A =
      Finset.image (fun x => x.image Fin.castSucc) (slice0 A) ∪
        Finset.image (fun x => insert (Fin.last N) (x.image Fin.castSucc)) (slice1 A) := by
    ext x
    constructor
    · by_cases hx : Fin.last N ∈ x
      · intro hx_A
        obtain ⟨y, hy⟩ : ∃ y : Cube N, x = insert (Fin.last N) (y.image Fin.castSucc) := by
          use Finset.filter (fun y => Fin.castSucc y ∈ x) Finset.univ
          ext y; simp
          cases y using Fin.lastCases <;> aesop
        unfold slice1; aesop
      · -- Since `Fin.last N ∉ x`, write `x = y.image Fin.castSucc` for some `y : Cube N`.
        obtain ⟨y, hy⟩ : ∃ y : Finset (Fin N), x = y.image Fin.castSucc := by
          use Finset.univ.filter (fun i => Fin.castSucc i ∈ x)
          ext i
          induction i using Fin.lastCases <;> aesop
        unfold slice0 slice1; aesop
    · unfold slice0 slice1; aesop
  conv_lhs => rw [h_decomp, Finset.filter_union]
  rw [Finset.card_union_of_disjoint, Finset.card_filter, Finset.card_filter]
  · rw [Finset.sum_image, Finset.sum_image]
    · simp +decide [Finset.card_image_of_injective _ (Fin.castSucc_injective N),
        Finset.card_insert_of_notMem]
    · intro x hx y hy
      simp +decide only [Finset.ext_iff, mem_union, mem_image, mem_insert, SetLike.mem_coe] at *
      intro h a; specialize h (Fin.castSucc a) ; aesop
    · exact fun x hx y hy hxy => Finset.image_injective (Fin.castSucc_injective _) hxy
  · simp +contextual only [disjoint_left, mem_filter, mem_image, and_true, not_exists, not_and,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    intro a ha hk x hx H; replace H := Finset.ext_iff.mp H (Fin.last N) ; simp +decide at H

end BooleanIsoperimetry
