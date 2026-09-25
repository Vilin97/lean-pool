/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.FarMarkAPI
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossStrandSupport
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.GenericRankWitness

/-!
# The four-alternative same-strand lemma

This is the invariant form of paper Lemma 3.5 (`lem-SameStrand`).  The paper
writes vertex equalities as equalities of strand coordinates.  That is false
at either multivalent endpoint, because an endpoint has a coordinate on every
strand.  We state the first three alternatives as physical vertex equalities
and the fourth as the existence of one strand containing all three physical
vertices.

The argument is needed only in the paper's standing banana range `g ≥ 2`.
That hypothesis is mathematically essential: in genus one every degree-one
divisor has rank zero, so the displayed four-alternative claim fails for
three suitable points on a cycle.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A physical vertex lies on the normalized strand `alpha`.  Unlike a raw
coordinate equality, this treats the two common endpoints invariantly. -/
def VertexOnBananaStrand {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (x : B.graph.V) : Prop :=
  ∃ p : B.PathPosition alpha, x = strandVertex B alpha p

/-- Three physical vertices lie on one common banana strand. -/
def VerticesOnCommonBananaStrand {g : ℕ} (B : Banana g)
    (x y z : B.graph.V) : Prop :=
  ∃ alpha : Fin (g + 1),
    VertexOnBananaStrand B alpha x ∧
      VertexOnBananaStrand B alpha y ∧
      VertexOnBananaStrand B alpha z

/-- A noninterior normalized position is one of the two physical endpoints. -/
theorem strandVertex_eq_endpoint_of_not_interior
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (i : B.PathPosition alpha) (hi : ¬ B.IsInteriorPosition alpha i) :
    strandVertex B alpha i = leftEndpoint B ∨
      strandVertex B alpha i = rightEndpoint B := by
  change ¬ (0 < i.val ∧ i.val < B.length alpha) at hi
  have hiBound : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
  have hiEnd : i.val = 0 ∨ i.val = B.length alpha := by omega
  rcases hiEnd with hiZero | hiLength
  · left
    have hiEq : i = ⟨0, by omega⟩ := Fin.ext hiZero
    rw [hiEq, strandVertex_zero]
  · right
    have hiEq : i = ⟨B.length alpha, by omega⟩ := Fin.ext hiLength
    rw [hiEq, strandVertex_length]

/-- Either physical endpoint lies on every normalized banana strand. -/
theorem endpoint_vertexOnBananaStrand
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1)) (x : B.graph.V)
    (hx : x = leftEndpoint B ∨ x = rightEndpoint B) :
    VertexOnBananaStrand B alpha x := by
  rcases hx with rfl | rfl
  · exact ⟨⟨0, by omega⟩, (strandVertex_zero B alpha).symm⟩
  · exact ⟨⟨B.length alpha, by omega⟩,
      (strandVertex_length B alpha).symm⟩

/-- A non-reflected pair, expressed invariantly by inequality of physical
vertices, has rank zero. -/
theorem rank_normalized_same_strand_pair_zero_of_not_reflection_vertex
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i k : B.PathPosition alpha)
    (hNot : strandVertex B alpha k ≠
      strandVertex B alpha (strandMirror B alpha i)) :
    rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B alpha k)) = 0 := by
  have hSum : i.val + k.val ≠ B.length alpha := by
    intro h
    apply hNot
    congr 1
    apply Fin.ext
    simp only [strandMirror]
    omega
  by_cases hTail : B.core.tail alpha = 0
  · simp only [strandVertex, hTail, ↓reduceIte]
    exact rank_same_strand_pair_zero_of_not_reflection_generic
      hg B alpha i k hSum
  · simp only [strandVertex, hTail, ↓reduceIte]
    apply rank_same_strand_pair_zero_of_not_reflection_generic hg
    change (B.length alpha - i.val) + (B.length alpha - k.val) ≠
      B.length alpha
    have hi : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
    have hk : k.val ≤ B.length alpha := Nat.le_of_lt_succ k.isLt
    omega

/-- Generic-genus form of the core-plus-interior Dhar calculation.  The
theta-only theorem in `SameStrand.lean` predates the generic reduced-divisor
lemma which its proof actually uses. -/
theorem rank_coreVertex_add_distinct_interior_path_marks_ne_zero_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (e : Fin 2)
    (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition beta j)
    (hab : alpha ≠ beta) :
    rank B.graph
      (oneChip (B.coreVertex e) + oneChip (B.pathVertex alpha i) -
        oneChip (B.pathVertex beta j)) ≠ 0 := by
  have hjEndpoint : B.pathVertex beta j ≠ B.coreVertex e := by
    intro h
    rw [B.pathVertex_eq_interiorVertex beta j hj] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  have hji : B.pathVertex beta j ≠ B.pathVertex alpha i := by
    intro h
    have hba := (interior_and_strand_eq_of_pathVertex_eq_interior B beta alpha
      j i hi h).2
    exact hab hba.symm
  have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
    hg B e alpha beta i j hi hj hab hjEndpoint hji
  have hDebt :
      ((oneChip (B.coreVertex e) + oneChip (B.pathVertex alpha i) -
        oneChip (B.pathVertex beta j) : CFDiv B.graph)
          (B.pathVertex beta j)) < 0 := by
    simp [oneChip, hjEndpoint, hji]
  have hRank := rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex beta j)
    (oneChip (B.coreVertex e) + oneChip (B.pathVertex alpha i) -
      oneChip (B.pathVertex beta j)) hRed hDebt
  omega

/-- A raw-coordinate reflected pair has rank one in every banana of genus at
least two.  The older theorem in `SameStrand.lean` proves only the theta case;
the generic endpoint-pencil rank formula supplies exactly the missing step. -/
theorem rank_path_pair_eq_one_of_sum_eq_length_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i k : B.PathPosition alpha)
    (hsum : i.val + k.val = B.length alpha) :
    rank B.graph
      (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)) = 1 := by
  have hkMirror : B.pathVertex alpha k =
      B.pathVertex alpha (SegmentReflection.symmetricPosition B alpha i) := by
    rw [B.pathVertex_eq_iff_val_eq]
    change k.val = B.length alpha - i.val
    have hiBound := i.isLt
    omega
  have hReflection : linearEquiv B.graph
      (oneChip (B.coreVertex (B.core.tail alpha)) +
        oneChip (B.coreVertex (B.core.head alpha)))
      (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)) := by
    unfold linearEquiv
    apply (principal_iff_eq_prin B.graph _).mpr
    refine ⟨SegmentReflection.script B alpha i, ?_⟩
    rw [SegmentReflection.prin_script_eq_reflectionDivisor, ← hkMirror]
    abel
  have hRawEndpoints :
      oneChip (B.coreVertex (B.core.tail alpha)) +
          oneChip (B.coreVertex (B.core.head alpha)) =
        endpointPencilDivisor B := by
    by_cases hTail : B.core.tail alpha = 0
    · have hHead := head_eq_other_of_tail B alpha hTail
      simp [hTail, hHead, endpointPencilDivisor, leftEndpoint, rightEndpoint]
    · have hTail' : B.core.tail alpha = 1 := by
        apply Fin.ext
        have hTailVal : (B.core.tail alpha).val ≠ 0 := by
          intro hval
          apply hTail
          apply Fin.ext
          exact hval
        have hlt := (B.core.tail alpha).isLt
        omega
      have hHead : B.core.head alpha = 0 := by
        by_contra hne
        have hHead' : B.core.head alpha = 1 := by
          apply Fin.ext
          have hHeadVal : (B.core.head alpha).val ≠ 0 := by
            intro hval
            apply hne
            apply Fin.ext
            exact hval
          have hlt := (B.core.head alpha).isLt
          omega
        apply B.core_loopless alpha
        simp [hTail', hHead']
      simp [hTail', hHead, endpointPencilDivisor, leftEndpoint, rightEndpoint,
        add_comm]
  have hEndpointRank : rank B.graph (endpointPencilDivisor B) = 1 := by
    have h := rank_endpointPencil_nsmul_eq B 1 (by omega)
    simpa using h
  have hRankEq := rank_eq_of_linear_equiv B.graph hReflection
  rw [hRawEndpoints, hEndpointRank] at hRankEq
  omega

/-- Generic-genus form of the same-positive-strand / distinct-negative-strand
Dhar calculation. -/
theorem rank_same_path_pair_sub_distinct_interior_ne_zero_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (alpha beta : Fin (g + 1))
    (i k : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hk : B.IsInteriorPosition alpha k)
    (hj : B.IsInteriorPosition beta j)
    (hab : alpha ≠ beta)
    (hPairRank : rank B.graph
      (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)) = 0) :
    rank B.graph
      (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k) -
        oneChip (B.pathVertex beta j)) ≠ 0 := by
  rcases lt_trichotomy (i.val + k.val) (B.length alpha) with hsum | hsum | hsum
  · let p : B.PathPosition alpha := ⟨i.val + k.val, by omega⟩
    have hp : B.IsInteriorPosition alpha p := by
      change 0 < i.val + k.val ∧ i.val + k.val < B.length alpha
      exact ⟨Nat.add_pos_left hi.1 _, hsum⟩
    have hjEndpoint : B.pathVertex beta j ≠
        B.coreVertex (B.core.tail alpha) := by
      intro h
      rw [B.pathVertex_eq_interiorVertex beta j hj] at h
      simp [SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex] at h
    have hjp : B.pathVertex beta j ≠ B.pathVertex alpha p := by
      intro h
      have hba := (interior_and_strand_eq_of_pathVertex_eq_interior B beta alpha
        j p hp h).2
      exact hab hba.symm
    have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
      hg B (B.core.tail alpha) alpha beta p j hp hj hab hjEndpoint hjp
    have hDebt :
        ((oneChip (B.coreVertex (B.core.tail alpha)) +
          oneChip (B.pathVertex alpha p) - oneChip (B.pathVertex beta j) :
            CFDiv B.graph) (B.pathVertex beta j)) < 0 := by
      simp [oneChip, hjEndpoint, hjp]
    have hEndpointRank := rank_eq_neg_one_of_qReduced_debt B.graph
      (B.pathVertex beta j)
      (oneChip (B.coreVertex (B.core.tail alpha)) +
        oneChip (B.pathVertex alpha p) - oneChip (B.pathVertex beta j))
      hRed hDebt
    have hSlide := path_pair_linearEquiv_tail_sum B alpha i k hi.1 hk.1 hsum
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide (B.pathVertex beta j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    intro hZero
    dsimp [p] at hEndpointRank hRankEq
    rw [hZero, hEndpointRank] at hRankEq
    omega
  · have hReflected :=
      rank_path_pair_eq_one_of_sum_eq_length_generic hg B alpha i k hsum
    omega
  · let p : B.PathPosition alpha :=
      ⟨i.val + k.val - B.length alpha, by omega⟩
    have hp : B.IsInteriorPosition alpha p := by
      change 0 < i.val + k.val - B.length alpha ∧
        i.val + k.val - B.length alpha < B.length alpha
      constructor
      · omega
      · have hiBound := hi.2
        have hkBound := hk.2
        omega
    have hjEndpoint : B.pathVertex beta j ≠
        B.coreVertex (B.core.head alpha) := by
      intro h
      rw [B.pathVertex_eq_interiorVertex beta j hj] at h
      simp [SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex] at h
    have hjp : B.pathVertex beta j ≠ B.pathVertex alpha p := by
      intro h
      have hba := (interior_and_strand_eq_of_pathVertex_eq_interior B beta alpha
        j p hp h).2
      exact hab hba.symm
    have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
      hg B (B.core.head alpha) alpha beta p j hp hj hab hjEndpoint hjp
    have hDebt :
        ((oneChip (B.coreVertex (B.core.head alpha)) +
          oneChip (B.pathVertex alpha p) - oneChip (B.pathVertex beta j) :
            CFDiv B.graph) (B.pathVertex beta j)) < 0 := by
      simp [oneChip, hjEndpoint, hjp]
    have hEndpointRank := rank_eq_neg_one_of_qReduced_debt B.graph
      (B.pathVertex beta j)
      (oneChip (B.coreVertex (B.core.head alpha)) +
        oneChip (B.pathVertex alpha p) - oneChip (B.pathVertex beta j))
      hRed hDebt
    have hSlide := path_pair_linearEquiv_head_excess B alpha i k hi.2 hk.2 hsum
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide (B.pathVertex beta j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    intro hZero
    have hEndpointRank' : rank B.graph
        (oneChip (B.pathVertex alpha p) +
          oneChip (B.coreVertex (B.core.head alpha)) -
            oneChip (B.pathVertex beta j)) = -1 := by
      simpa only [add_comm] using hEndpointRank
    dsimp [p] at hEndpointRank' hRankEq
    rw [hZero, hEndpointRank'] at hRankEq
    omega

/-- Normalized-coordinate wrapper for the core-plus-interior Dhar
calculation in `SameStrand.lean`. -/
theorem rank_coreVertex_add_distinct_normalized_interior_ne_zero
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (e : Fin 2)
    (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition beta j) (hab : alpha ≠ beta) :
    rank B.graph
      (oneChip (B.coreVertex e) + oneChip (strandVertex B alpha i) -
        oneChip (strandVertex B beta j)) ≠ 0 := by
  let p := normalizedPathPosition B alpha i
  let q := normalizedPathPosition B beta j
  have hp : B.IsInteriorPosition alpha p :=
    normalizedPathPosition_isInterior B alpha i hi
  have hq : B.IsInteriorPosition beta q :=
    normalizedPathPosition_isInterior B beta j hj
  have hRaw := rank_coreVertex_add_distinct_interior_path_marks_ne_zero_generic
    hg B e alpha beta p q hp hq hab
  simpa [p, q, strandVertex_eq_pathVertex_normalized] using hRaw

/-- Two normalized interior chips on distinct strands cannot retain rank zero
after deleting a core vertex. -/
theorem rank_distinct_normalized_interior_pair_sub_core_ne_zero
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition beta j) (hab : alpha ≠ beta)
    (e : Fin 2) :
    rank B.graph
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j) -
        oneChip (B.coreVertex e)) ≠ 0 := by
  have hSupport := rankSupport_two_interior_distinct_strands
    hg B alpha beta i j hi hj hab
  intro hRank
  have hMem : B.coreVertex e ∈ rankSupport B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B beta j)) := by
    exact hRank.ge
  rw [hSupport] at hMem
  have heAlpha : B.coreVertex e ≠ strandVertex B alpha i := by
    rw [strandVertex_eq_pathVertex_normalized,
      B.pathVertex_eq_interiorVertex alpha _
        (normalizedPathPosition_isInterior B alpha i hi)]
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex]
  have heBeta : B.coreVertex e ≠ strandVertex B beta j := by
    rw [strandVertex_eq_pathVertex_normalized,
      B.pathVertex_eq_interiorVertex beta _
        (normalizedPathPosition_isInterior B beta j hj)]
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hMem
  exact (hMem.elim heAlpha heBeta).elim

/-- Normalized-coordinate wrapper for the same-positive-strand / distinct
negative-strand part of the Dhar calculation. -/
theorem rank_same_normalized_pair_sub_distinct_interior_ne_zero
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (alpha beta : Fin (g + 1))
    (i k : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hk : B.IsInteriorPosition alpha k)
    (hj : B.IsInteriorPosition beta j) (hab : alpha ≠ beta)
    (hPair : rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B alpha k)) = 0) :
    rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B alpha k) -
        oneChip (strandVertex B beta j)) ≠ 0 := by
  let p := normalizedPathPosition B alpha i
  let q := normalizedPathPosition B alpha k
  let r := normalizedPathPosition B beta j
  have hp : B.IsInteriorPosition alpha p :=
    normalizedPathPosition_isInterior B alpha i hi
  have hq : B.IsInteriorPosition alpha q :=
    normalizedPathPosition_isInterior B alpha k hk
  have hr : B.IsInteriorPosition beta r :=
    normalizedPathPosition_isInterior B beta j hj
  have hPairRaw : rank B.graph
      (oneChip (B.pathVertex alpha p) + oneChip (B.pathVertex alpha q)) = 0 := by
    simpa [p, q, strandVertex_eq_pathVertex_normalized] using hPair
  have hRaw := rank_same_path_pair_sub_distinct_interior_ne_zero_generic
    hg B alpha beta p q r hp hq hr hab hPairRaw
  simpa [p, q, r, strandVertex_eq_pathVertex_normalized] using hRaw

/-- **Corrected Lemma 3.5 (`lem-SameStrand`).**

If `rank(x + y - z) = 0` on a banana of genus at least two, then `z` equals
one of the two positive vertices, the two positive vertices are strand
reflections, or the three *physical vertices* lie on a common strand.

The paper appends coordinate equalities to the first, second, and fourth
alternatives.  Those parentheticals are invalid at the common endpoints;
the vertex/common-strand formulation here is the faithful invariant claim. -/
theorem banana_rank_zero_three_vertices_same_strand_alternatives
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (alpha beta gamma : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (k : B.PathPosition gamma)
    (hRank : rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B beta j) -
        oneChip (strandVertex B gamma k)) = 0) :
    strandVertex B alpha i = strandVertex B gamma k ∨
      strandVertex B beta j = strandVertex B gamma k ∨
      strandVertex B beta j =
        strandVertex B alpha (strandMirror B alpha i) ∨
      VerticesOnCommonBananaStrand B
        (strandVertex B alpha i) (strandVertex B beta j)
        (strandVertex B gamma k) := by
  by_cases hxz : strandVertex B alpha i = strandVertex B gamma k
  · exact Or.inl hxz
  by_cases hyz : strandVertex B beta j = strandVertex B gamma k
  · exact Or.inr (Or.inl hyz)
  by_cases hReflect : strandVertex B beta j =
      strandVertex B alpha (strandMirror B alpha i)
  · exact Or.inr (Or.inr (Or.inl hReflect))
  refine Or.inr (Or.inr (Or.inr ?_))
  by_cases hi : B.IsInteriorPosition alpha i
  · by_cases hj : B.IsInteriorPosition beta j
    · by_cases hk : B.IsInteriorPosition gamma k
      · by_cases hab : alpha = beta
        · subst beta
          by_cases hag : alpha = gamma
          · subst gamma
            exact ⟨alpha, ⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩⟩
          · have hPair : rank B.graph
                (oneChip (strandVertex B alpha i) +
                  oneChip (strandVertex B alpha j)) = 0 :=
              rank_normalized_same_strand_pair_zero_of_not_reflection_vertex
                hg B alpha i j hReflect
            have hNotRank :=
              rank_same_normalized_pair_sub_distinct_interior_ne_zero
                hg B alpha gamma i j k hi hj hk hag hPair
            exact (hNotRank hRank).elim
        · have hNeg := rank_strand_pair_sub_of_distinct_interior
              hg B alpha beta gamma i j k hi hj hk hab
                (Ne.symm hxz) (Ne.symm hyz)
          omega
      · by_cases hab : alpha = beta
        · subst beta
          refine ⟨alpha, ⟨i, rfl⟩, ⟨j, rfl⟩, ?_⟩
          exact endpoint_vertexOnBananaStrand B alpha _
            (strandVertex_eq_endpoint_of_not_interior B gamma k hk)
        · rcases strandVertex_eq_endpoint_of_not_interior B gamma k hk with
            hkLeft | hkRight
          · have hNotRank :=
                rank_distinct_normalized_interior_pair_sub_core_ne_zero
                  hg B alpha beta i j hi hj hab (0 : Fin 2)
            have hRank' := hRank
            rw [hkLeft, leftEndpoint] at hRank'
            exact (hNotRank hRank').elim
          · have hNotRank :=
                rank_distinct_normalized_interior_pair_sub_core_ne_zero
                  hg B alpha beta i j hi hj hab (1 : Fin 2)
            have hRank' := hRank
            rw [hkRight, rightEndpoint] at hRank'
            exact (hNotRank hRank').elim
    · by_cases hk : B.IsInteriorPosition gamma k
      · by_cases hag : alpha = gamma
        · subst gamma
          refine ⟨alpha, ⟨i, rfl⟩, ?_, ⟨k, rfl⟩⟩
          exact endpoint_vertexOnBananaStrand B alpha _
            (strandVertex_eq_endpoint_of_not_interior B beta j hj)
        · rcases strandVertex_eq_endpoint_of_not_interior B beta j hj with
            hjLeft | hjRight
          · have hNotRank :=
                rank_coreVertex_add_distinct_normalized_interior_ne_zero
                  hg B (0 : Fin 2) alpha gamma i k hi hk hag
            have hRank' := hRank
            rw [hjLeft, leftEndpoint] at hRank'
            exact (hNotRank (by simpa only [add_comm] using hRank')).elim
          · have hNotRank :=
                rank_coreVertex_add_distinct_normalized_interior_ne_zero
                  hg B (1 : Fin 2) alpha gamma i k hi hk hag
            have hRank' := hRank
            rw [hjRight, rightEndpoint] at hRank'
            exact (hNotRank (by simpa only [add_comm] using hRank')).elim
      · refine ⟨alpha, ⟨i, rfl⟩, ?_, ?_⟩
        · exact endpoint_vertexOnBananaStrand B alpha _
            (strandVertex_eq_endpoint_of_not_interior B beta j hj)
        · exact endpoint_vertexOnBananaStrand B alpha _
            (strandVertex_eq_endpoint_of_not_interior B gamma k hk)
  · by_cases hj : B.IsInteriorPosition beta j
    · by_cases hk : B.IsInteriorPosition gamma k
      · by_cases hbg : beta = gamma
        · subst gamma
          refine ⟨beta, ?_, ⟨j, rfl⟩, ⟨k, rfl⟩⟩
          exact endpoint_vertexOnBananaStrand B beta _
            (strandVertex_eq_endpoint_of_not_interior B alpha i hi)
        · rcases strandVertex_eq_endpoint_of_not_interior B alpha i hi with
            hiLeft | hiRight
          · have hNotRank :=
                rank_coreVertex_add_distinct_normalized_interior_ne_zero
                  hg B (0 : Fin 2) beta gamma j k hj hk hbg
            have hRank' := hRank
            rw [hiLeft, leftEndpoint] at hRank'
            exact (hNotRank hRank').elim
          · have hNotRank :=
                rank_coreVertex_add_distinct_normalized_interior_ne_zero
                  hg B (1 : Fin 2) beta gamma j k hj hk hbg
            have hRank' := hRank
            rw [hiRight, rightEndpoint] at hRank'
            exact (hNotRank hRank').elim
      · refine ⟨beta, ?_, ⟨j, rfl⟩, ?_⟩
        · exact endpoint_vertexOnBananaStrand B beta _
            (strandVertex_eq_endpoint_of_not_interior B alpha i hi)
        · exact endpoint_vertexOnBananaStrand B beta _
            (strandVertex_eq_endpoint_of_not_interior B gamma k hk)
    · refine ⟨gamma, ?_, ?_, ?_⟩
      · exact endpoint_vertexOnBananaStrand B gamma _
          (strandVertex_eq_endpoint_of_not_interior B alpha i hi)
      · exact endpoint_vertexOnBananaStrand B gamma _
          (strandVertex_eq_endpoint_of_not_interior B beta j hj)
      · exact ⟨k, rfl⟩

end Bananas
