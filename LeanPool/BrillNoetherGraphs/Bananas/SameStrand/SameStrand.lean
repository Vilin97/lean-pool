/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.ReducedCutCriterion
import LeanPool.BrillNoetherGraphs.Bananas.Basics.TwoEdgeCuts
import LeanPool.BrillNoetherGraphs.Bananas.Basics.DegreeOneRepresentatives
import LeanPool.BrillNoetherGraphs.Bananas.Basics.SegmentScript

/-!
# Coordinate hygiene for the same-strand argument

The paper's `SameStrand` lemma is a statement about *vertices*, not about
the non-unique path-slot descriptions of the two common endpoints.  This
file starts the formal version by recording the injectivity fact needed to
turn vertex equalities into slot equalities when the positions concerned are
genuinely interior.
-/

namespace Bananas


private theorem finTwo {e : Fin 2} : e = 0 ∨ e = 1 := by
  fin_cases e <;> simp

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The generic form of the subinterval-reflection identity.  The reusable
construction in `GenusFourCore097` is polymorphic in the subdivision spec;
its original packaged equality was specialized only because that file's
application has six core vertices and nine slots. -/
theorem prin_subinterval_reflection
    {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {star : Fin p}
    {lo hi target : ℕ}
    (hlo : lo < target) (hhi : target < hi)
    (hlen : hi ≤ spec.length star) :
    prin spec.graph (segScript spec star lo hi target) =
      -oneChip (G := spec.graph) (spec.pathVertex star ⟨lo, by omega⟩) -
        oneChip (spec.pathVertex star ⟨hi, by omega⟩) +
        oneChip (spec.pathVertex star ⟨target, by omega⟩) +
        oneChip (spec.pathVertex star ⟨lo + hi - target, by omega⟩) := by
  have hpos := spec.length_pos star
  refine divisor_ext ?_ ?_
  · intro v
    rw [prin_seg_core hlo hhi hlen]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      one_chip_pos_core spec star ⟨lo, by omega⟩ v,
      one_chip_pos_core spec star ⟨hi, by omega⟩ v,
      one_chip_pos_core spec star ⟨target, by omega⟩ v,
      one_chip_pos_core spec star ⟨lo + hi - target, by omega⟩ v]
    rw [if_neg (show ¬ (lo = spec.length star) by omega),
      if_neg (show ¬ (hi = 0) by omega),
      if_neg (show ¬ (target = 0) by omega),
      if_neg (show ¬ (target = spec.length star) by omega),
      if_neg (show ¬ (lo + hi - target = 0) by omega),
      if_neg (show ¬ (lo + hi - target = spec.length star) by omega)]
    split_ifs <;> omega
  · intro edge off
    have hoi := off.isLt
    rw [prin_seg_int hlo hhi hlen]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      one_chip_pos_int spec star ⟨lo, by omega⟩ edge off,
      one_chip_pos_int spec star ⟨hi, by omega⟩ edge off,
      one_chip_pos_int spec star ⟨target, by omega⟩ edge off,
      one_chip_pos_int spec star ⟨lo + hi - target, by omega⟩ edge off]
    by_cases he : edge = star
    · subst he
      rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl]
      split_ifs <;> omega
    · rw [if_neg he, if_neg (fun hh => he hh.symm),
        if_neg (fun hh => he hh.symm), if_neg (fun hh => he hh.symm),
        if_neg (fun hh => he hh.symm)]
      ring

/-- Two interior chips whose raw path coordinates sum to less than the slot
length slide to the tail endpoint and the point at their coordinate sum. -/
theorem path_pair_linearEquiv_tail_sum
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i k : B.PathPosition α)
    (hi : 0 < i.val) (hk : 0 < k.val)
    (hsum : i.val + k.val < B.length α) :
    linearEquiv B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k))
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.pathVertex α ⟨i.val + k.val, by omega⟩)) := by
  unfold linearEquiv
  apply (principal_iff_eq_prin B.graph _).mpr
  let s := -segScript B α 0 (i.val + k.val) i.val
  refine ⟨s, ?_⟩
  have hPrin := prin_subinterval_reflection (spec := B) (star := α)
    (lo := 0) (hi := i.val + k.val) (target := i.val)
    (by omega) (by omega) (by omega)
  have hMirror :
      B.pathVertex α
          ⟨0 + (i.val + k.val) - i.val, by omega⟩ =
        B.pathVertex α k := by
    rw [B.pathVertex_eq_iff_val_eq]
    change 0 + (i.val + k.val) - i.val = k.val
    omega
  dsimp [s]
  rw [map_neg, hPrin, B.pathVertex_zero, hMirror]
  abel

/-- Two interior chips whose raw path coordinates sum past the slot length
slide to the head endpoint and the point at their excess coordinate. -/
theorem path_pair_linearEquiv_head_excess
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i k : B.PathPosition α)
    (hi : i.val < B.length α) (hk : k.val < B.length α)
    (hsum : B.length α < i.val + k.val) :
    linearEquiv B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k))
      (oneChip (B.pathVertex α ⟨i.val + k.val - B.length α, by omega⟩) +
        oneChip (B.coreVertex (B.core.head α))) := by
  unfold linearEquiv
  apply (principal_iff_eq_prin B.graph _).mpr
  let lo := i.val + k.val - B.length α
  let s := -segScript B α lo (B.length α) i.val
  refine ⟨s, ?_⟩
  have hPrin := prin_subinterval_reflection (spec := B) (star := α)
    (lo := lo) (hi := B.length α) (target := i.val)
    (by dsimp [lo]; omega) (by omega) (by omega)
  have hMirror :
      B.pathVertex α
          ⟨lo + B.length α - i.val, by
            dsimp [lo]
            omega⟩ = B.pathVertex α k := by
    rw [B.pathVertex_eq_iff_val_eq]
    dsimp [lo]
    omega
  dsimp [s]
  rw [map_neg, hPrin, B.pathVertex_length, hMirror]
  dsimp [lo]
  abel

/-- On a theta, two raw path coordinates summing to the strand length form
the reflected (hence canonical) pair and have rank one. -/
theorem rank_path_pair_eq_one_of_sum_eq_length
    (B : Banana 2) (α : Fin 3) (i k : B.PathPosition α)
    (hsum : i.val + k.val = B.length α) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 1 := by
  have hkMirror : B.pathVertex α k =
      B.pathVertex α (SegmentReflection.symmetricPosition B α i) := by
    rw [B.pathVertex_eq_iff_val_eq]
    change k.val = B.length α - i.val
    have hiBound := i.isLt
    omega
  have hReflection : linearEquiv B.graph
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.coreVertex (B.core.head α)))
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) := by
    unfold linearEquiv
    apply (principal_iff_eq_prin B.graph _).mpr
    refine ⟨SegmentReflection.script B α i, ?_⟩
    rw [SegmentReflection.prin_script_eq_reflectionDivisor, ← hkMirror]
    abel
  have hRawEndpoints :
      oneChip (B.coreVertex (B.core.tail α)) +
          oneChip (B.coreVertex (B.core.head α)) =
        oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
    by_cases hTail : B.core.tail α = 0
    · have hHead := head_eq_other_of_tail B α hTail
      simp [hTail, hHead, leftEndpoint, rightEndpoint]
    · have hTail' : B.core.tail α = 1 := by
        apply Fin.ext
        have hTailVal : (B.core.tail α).val ≠ 0 := by
          intro hval
          apply hTail
          apply Fin.ext
          exact hval
        have hlt := (B.core.tail α).isLt
        omega
      have hHead : B.core.head α = 0 := by
        by_contra hne
        have hHead' : B.core.head α = 1 := by
          apply Fin.ext
          have hHeadVal : (B.core.head α).val ≠ 0 := by
            intro hval
            apply hne
            apply Fin.ext
            exact hval
          have hlt := (B.core.head α).isLt
          omega
        apply B.core_loopless α
        simp [hTail', hHead']
      simp [hTail', hHead, leftEndpoint, rightEndpoint, add_comm]
  have hCanonical :
      canonicalDivisor B.graph =
        oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
    simpa using canonical_divisor_eq_endpoints B
  have hCanonicalRank : rank B.graph (canonicalDivisor B.graph) = 1 := by
    have hRR := riemann_roch_for_graphs (graphConnected B)
      (canonicalDivisor B.graph)
    rw [sub_self, zero_divisor_rank, degree_of_canonical_divisor,
      B.genus_graph] at hRR
    omega
  have hRankEq := rank_eq_of_linear_equiv B.graph hReflection
  rw [hRawEndpoints, ← hCanonical] at hRankEq
  omega

/-- Interior vertices on distinct banana strands are distinct.  In
particular, the slot label of an interior vertex is intrinsic, whereas the
two endpoint descriptions deliberately are not. -/
theorem strand_eq_of_interior_vertex_eq {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (h : strandVertex B α i = strandVertex B β j) : α = β := by
  rw [strandVertex_eq_pathVertex_normalized,
    strandVertex_eq_pathVertex_normalized] at h
  have hi' : B.IsInteriorPosition α (normalizedPathPosition B α i) :=
    normalizedPathPosition_isInterior B α i hi
  have hj' : B.IsInteriorPosition β (normalizedPathPosition B β j) :=
    normalizedPathPosition_isInterior B β j hj
  rw [B.pathVertex_eq_interiorVertex α _ hi',
    B.pathVertex_eq_interiorVertex β _ hj'] at h
  exact congrArg Sigma.fst (Sum.inr.inj h)

/-- If a path vertex agrees with an interior vertex on another strand, then
the first path position is interior as well and the two strand labels agree.
This is useful for identifying the inside endpoint of a crossing step. -/
theorem interior_and_strand_eq_of_pathVertex_eq_interior {g : ℕ}
    (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hj : B.IsInteriorPosition β j)
    (h : B.pathVertex α i = B.pathVertex β j) :
    B.IsInteriorPosition α i ∧ α = β := by
  have hjZero : j.val ≠ 0 := hj.1.ne'
  have hjLast : j.val ≠ B.length β := ne_of_lt hj.2
  unfold SubdivisionGraph.Spec.pathVertex at h
  rw [dif_neg hjZero, dif_neg hjLast] at h
  by_cases hiZero : i.val = 0
  · rw [dif_pos hiZero] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  rw [dif_neg hiZero] at h
  by_cases hiLast : i.val = B.length α
  · rw [dif_pos hiLast] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  rw [dif_neg hiLast] at h
  have hi : B.IsInteriorPosition α i := by
    change 0 < i.val ∧ i.val < B.length α
    have hiBound := i.isLt
    omega
  exact ⟨hi, congrArg Sigma.fst (Sum.inr.inj h)⟩

/-- The endpoint coordinate aliases that make the paper's parenthetical
``i.e.`` clauses invalid without an interior hypothesis. -/
theorem strandVertex_zero_eq_zero {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) :
    strandVertex B α ⟨0, by omega⟩ = strandVertex B β ⟨0, by omega⟩ := by
  rw [strandVertex_zero, strandVertex_zero]

/-- Concrete witness to the endpoint-alias issue in the paper's coordinate
parentheticals: already on a theta, the zero positions of slots `0` and `1`
are equal vertices although their coordinate pairs differ. -/
theorem theta_left_endpoint_has_distinct_slot_descriptions (B : Banana 2) :
    ∃ (α β : Fin 3) (i : B.PathPosition α) (j : B.PathPosition β),
      α ≠ β ∧ strandVertex B α i = strandVertex B β j := by
  refine ⟨0, 1, ⟨0, by omega⟩, ⟨0, by omega⟩, by decide, ?_⟩
  exact strandVertex_zero_eq_zero B 0 1

/-- A pointwise form of the last step in the reduced-divisor strategy: a
`q`-reduced divisor with a debt at `q` is not winnable and hence has rank
`-1`.  It is kept separate from the banana interval calculation. -/
theorem rank_eq_neg_one_of_qReduced_debt
    (G : CFGraph) (q : G.V) (D : CFDiv G)
    (hRed : qReduced G q D) (hDebt : D q < 0) :
    rank G D = -1 := by
  have hNotWin : ¬ winnable G D := by
    intro hWin
    have hEff : effective D :=
      effective_of_winnable_and_q_reduced G q D hWin hRed
    exact (not_lt_of_ge (hEff q)) hDebt
  have hNotNonneg : ¬ 0 ≤ rank G D := by
    intro hNonneg
    exact hNotWin ((rank_nonneg_iff_winnable G D).mp
      ((rank_geq_iff G D 0).mpr hNonneg))
  have hLower := rank_geq_neg_one G D
  omega

/-- The pointwise version of the reduced-divisor calculation required in the
paper's `SameStrand` proof.  For a two-chip divisor with debt at `q`, the
ordinary two-edge-cut condition handles every cut of size at least three.
Thus it remains only to burn the exceptional multiplicity-two cuts.  This is
strictly weaker (and correct) than requiring every such cut containing both
chips to have size at least three. -/
theorem q_reduced_two_chip_sub_of_twoEdgeCutCondition_of_twoCut_burn
    (G : CFGraph) (q x y : G.V) (hqx : q ≠ x) (hqy : q ≠ y)
    (hTwoEdge : TwoEdgeCutCondition G)
    (hBurn : ∀ S : Finset G.V,
      S ⊆ Finset.univ.filter (· ≠ q) → S.Nonempty →
      cutMultiplicity G S = 2 →
      ∃ z ∈ S,
        oneChip x z + oneChip y z - oneChip q z <
          ∑ w ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z w : ℤ)) :
    qReduced G q (oneChip x + oneChip y - oneChip q) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    by_cases hzx : z = x <;> by_cases hzy : z = y
    · subst z; subst y; simp [hqx]
    · subst z; simp [hqx, hzy]
    · subst z; simp [hqy, hzx]
    · simp [oneChip, hz, hzx, hzy]
  · intro S hqS hNonempty hLegal
    have hS : S ⊆ Finset.univ.filter (· ≠ q) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hzq
      exact hqS (hzq ▸ hz)
    let boundary : ℤ := ∑ z ∈ S,
      ∑ w ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z w : ℤ)
    have hTwo : 2 ≤ boundary := by
      have hProper : S ≠ Finset.univ := by
        intro hAll
        have hq : q ∈ S := by rw [hAll]; simp
        exact hqS hq
      have hCut := hTwoEdge S hNonempty hProper
      unfold cutMultiplicity at hCut
      simp_rw [outdeg_S_eq_sum_filter] at hCut
      simpa [boundary] using hCut
    by_cases hEq : boundary = 2
    · obtain ⟨z, hzS, hzBurn⟩ := hBurn S hS hNonempty (by
        unfold cutMultiplicity
        simp_rw [outdeg_S_eq_sum_filter]
        simpa [boundary] using hEq)
      apply (not_lt_of_ge (hLegal z hzS))
      rw [outdeg_S_eq_sum_filter]
      simpa using hzBurn
    ·
      have hPointwise : ∀ z ∈ S,
          ∑ w ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z w : ℤ) ≤
            oneChip x z + oneChip y z - oneChip q z := by
        intro z hz
        rw [← outdeg_S_eq_sum_filter]
        exact hLegal z hz
      have hSum : boundary ≤ ∑ z ∈ S,
          (oneChip x z + oneChip y z - oneChip q z) := by
        exact Finset.sum_le_sum fun z hz => hPointwise z hz
      have hqS : q ∉ S := by
        intro hqS
        have := hS hqS
        simp at this
      have hMass : (∑ z ∈ S,
          (oneChip x z + oneChip y z - oneChip q z)) ≤ 2 := by
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      have hThree : 3 ≤ boundary := by omega
      omega

/-- If a cut fails the pointwise burning test for `x+y-q`, then every source
of a boundary edge is one of the two chip locations.  This is the local
form in which a multiplicity-two cut can be fed to `crossingSteps` geometry.
-/
theorem boundary_source_eq_left_or_right_of_two_chip_no_burn
    (G : CFGraph) (q x y : G.V) (S : Finset G.V)
    (hS : S ⊆ Finset.univ.filter (· ≠ q))
    (hNoBurn : ∀ z ∈ S,
      ¬ (oneChip x z + oneChip y z - oneChip q z <
        ∑ w ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z w : ℤ)))
    {z w : G.V} (hz : z ∈ S) (hw : w ∉ S)
    (hEdge : 0 < numEdges G z w) : z = x ∨ z = y := by
  have hqz : z ≠ q := by
    intro hzq
    have := hS hz
    simp [hzq] at this
  by_contra hNot
  push Not at hNot
  have hTerm : 0 < (numEdges G z w : ℤ) := by exact_mod_cast hEdge
  have hwFilter : w ∈ Finset.univ.filter fun t => t ∉ S := by
    simp [hw]
  have hTermLe : (numEdges G z w : ℤ) ≤
      ∑ t ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z t : ℤ) := by
    refine Finset.single_le_sum (f := fun t => (numEdges G z t : ℤ))
      (fun _ _ => Int.natCast_nonneg _) hwFilter
  have hBoundaryPos : 0 <
      ∑ t ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z t : ℤ) := by
    omega
  have hNo := hNoBurn z hz
  simp [oneChip, hNot.1, hNot.2, hqz] at hNo
  omega

/-- Turn a positive boundary multiplicity into the crossing unit step used by
the subdivision cut lemmas. -/
theorem exists_crossingStep_of_boundary_edge {n p : ℕ}
    (B : SubdivisionGraph.Spec n p) (S : Finset B.graph.V)
    {z w : B.graph.V} (hz : z ∈ S) (hw : w ∉ S)
    (hEdge : 0 < numEdges B.graph z w) :
    ∃ step : B.Step, step ∈ B.crossingSteps S ∧
      (B.stepLeft step.1 step.2 = z ∨ B.stepRight step.1 step.2 = z) := by
  obtain ⟨step, hstep | hstep⟩ := (B.num_edges_pos_iff z w).mp hEdge
  · change (B.stepLeft step.1 step.2, B.stepRight step.1 step.2) = (z, w) at hstep
    have hLeft := congrArg Prod.fst hstep
    have hRight := congrArg Prod.snd hstep
    change B.stepLeft step.1 step.2 = z at hLeft
    change B.stepRight step.1 step.2 = w at hRight
    refine ⟨step, ?_, Or.inl hLeft⟩
    · rw [B.mem_crossingSteps]
      left
      rw [hLeft, hRight]
      exact ⟨hz, hw⟩
  · change (B.stepLeft step.1 step.2, B.stepRight step.1 step.2) = (w, z) at hstep
    have hLeft := congrArg Prod.fst hstep
    have hRight := congrArg Prod.snd hstep
    change B.stepLeft step.1 step.2 = w at hLeft
    change B.stepRight step.1 step.2 = z at hRight
    refine ⟨step, ?_, Or.inr hRight⟩
    · rw [B.mem_crossingSteps]
      right
      rw [hLeft, hRight]
      exact ⟨hz, hw⟩

/-- An excluded interior point whose two strand endpoints are on the cut side
forces two different crossing steps on that strand. -/
theorem exists_two_crossingSteps_around_excluded_interior
    {g : ℕ} (B : Banana g) (S : Finset B.graph.V)
    (γ : Fin (g + 1)) (q : B.PathPosition γ)
    (hq : B.IsInteriorPosition γ q)
    (hTail : B.pathVertex γ ⟨0, by omega⟩ ∈ S)
    (hHead : B.pathVertex γ ⟨B.length γ, by omega⟩ ∈ S)
    (hqOut : B.pathVertex γ q ∉ S) :
    ∃ a b : Fin (B.length γ), a ≠ b ∧
      (⟨γ, a⟩ : B.Step) ∈ B.crossingSteps S ∧
      (⟨γ, b⟩ : B.Step) ∈ B.crossingSteps S := by
  obtain ⟨a, haLo, haHi, haCross⟩ := B.exists_crossingStep_between S γ
    ⟨0, by omega⟩ q hq.1 (Or.inl ⟨hTail, hqOut⟩)
  obtain ⟨b, hbLo, hbHi, hbCross⟩ := B.exists_crossingStep_between S γ
    q ⟨B.length γ, by omega⟩ hq.2 (Or.inr ⟨hqOut, hHead⟩)
  refine ⟨a, b, ?_, haCross, hbCross⟩
  intro hab
  have hval : a.val = b.val := congrArg Fin.val hab
  omega

/-- The two directed boundary sources on opposite sides of an excluded path
position cannot both be the same vertex of that path.  This is the remaining
one-strand arithmetic contradiction in the two-cut burning argument. -/
theorem directed_boundary_sources_ne_on_same_strand
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i q : B.PathPosition α) (a b : Fin (B.length α))
    (haq : a.val < q.val) (hqb : q.val ≤ b.val)
    (ha : B.stepLeft α a = B.pathVertex α i)
    (hb : B.stepRight α b = B.pathVertex α i) : False := by
  have haVertex : B.pathVertex α (B.stepLeftPosition α a) =
      B.pathVertex α i := by
    rw [B.pathVertex_stepLeftPosition]
    exact ha
  have hbVertex : B.pathVertex α (B.stepRightPosition α b) =
      B.pathVertex α i := by
    rw [B.pathVertex_stepRightPosition]
    exact hb
  have haPos := congrArg Fin.val (B.pathVertex_injective α haVertex)
  have hbPos := congrArg Fin.val (B.pathVertex_injective α hbVertex)
  change a.val = i.val at haPos
  change b.val + 1 = i.val at hbPos
  omega

/-- Exact Dhar calculation for three interior path coordinates: if the two
positive chips lie on distinct strands, then subtracting a different
interior vertex produces a reduced divisor at that vertex. -/
theorem q_reduced_distinct_interior_path_strands
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hq : B.IsInteriorPosition γ q)
    (hαβ : α ≠ β)
    (hqx : B.pathVertex γ q ≠ B.pathVertex α i)
    (hqy : B.pathVertex γ q ≠ B.pathVertex β j) :
    qReduced B.graph (B.pathVertex γ q)
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
        oneChip (B.pathVertex γ q)) := by
  apply q_reduced_two_chip_sub_of_twoEdgeCutCondition_of_twoCut_burn
    B.graph (B.pathVertex γ q) (B.pathVertex α i) (B.pathVertex β j)
    hqx hqy (graph_twoEdgeCutCondition (by omega) B)
  intro S hS hNonempty hCut
  by_contra hNoBurn
  push Not at hNoBurn
  have hqS : B.pathVertex γ q ∉ S := by
    intro hmem
    have := hS hmem
    simp at this
  have hPointwise : ∀ z ∈ S,
      (∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges B.graph z w : ℤ)) ≤
      oneChip (B.pathVertex α i) z + oneChip (B.pathVertex β j) z -
        oneChip (B.pathVertex γ q) z := by
    intro z hz
    exact hNoBurn z hz
  have hNoBurn' : ∀ z ∈ S,
      ¬ (oneChip (B.pathVertex α i) z + oneChip (B.pathVertex β j) z -
        oneChip (B.pathVertex γ q) z <
          ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
            (numEdges B.graph z w : ℤ)) := by
    intro z hz
    exact not_lt.mpr (hNoBurn z hz)
  have hBoundary :
      (∑ z ∈ S, ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges B.graph z w : ℤ)) = 2 := by
    unfold cutMultiplicity at hCut
    simp_rw [outdeg_S_eq_sum_filter] at hCut
    exact hCut
  have hBoth : B.pathVertex α i ∈ S ∧ B.pathVertex β j ∈ S := by
    constructor
    · by_contra hx
      have hSum := Finset.sum_le_sum
        (fun z hz => hPointwise z hz)
      have hMass :
          (∑ z ∈ S,
            (oneChip (B.pathVertex α i) z + oneChip (B.pathVertex β j) z -
              oneChip (B.pathVertex γ q) z)) ≤ 1 := by
        by_cases hy : B.pathVertex β j ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
    · by_contra hy
      have hSum := Finset.sum_le_sum
        (fun z hz => hPointwise z hz)
      have hMass :
          (∑ z ∈ S,
            (oneChip (B.pathVertex α i) z + oneChip (B.pathVertex β j) z -
              oneChip (B.pathVertex γ q) z)) ≤ 1 := by
        by_cases hx : B.pathVertex α i ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
  have hCoreSame := core_vertices_same_side_of_cutMultiplicity_two hg B S hCut
  have hZero : B.coreVertex (0 : Fin 2) ∈ S := by
    by_contra hZeroOut
    have hOneOut : B.coreVertex (1 : Fin 2) ∉ S := by
      intro hOne
      exact hZeroOut (hCoreSame.mpr hOne)
    have hFour := four_le_crossingSteps_of_two_interior_strands B S α β hαβ
      i j hi hj hZeroOut hOneOut hBoth.1 hBoth.2
    have hCount : (B.crossingSteps S).card = 2 := by
      exact_mod_cast (B.cutMultiplicity_eq_card_crossingSteps S).symm.trans hCut
    omega
  have hOne : B.coreVertex (1 : Fin 2) ∈ S := hCoreSame.mp hZero
  have finTwo : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    fin_cases t <;> simp
  have hTail : B.pathVertex γ ⟨0, by omega⟩ ∈ S := by
    rw [B.pathVertex_zero]
    rcases finTwo (B.core.tail γ) with ht | ht
    · simpa [ht] using hZero
    · simpa [ht] using hOne
  have hHead : B.pathVertex γ ⟨B.length γ, by omega⟩ ∈ S := by
    rw [B.pathVertex_length]
    rcases finTwo (B.core.head γ) with hh | hh
    · simpa [hh] using hZero
    · simpa [hh] using hOne
  obtain ⟨a, _, haq, haIn, haOut⟩ :=
    B.exists_crossing_step_between S γ ⟨0, by omega⟩ q hq.1 hTail hqS
  have hqComp : B.pathVertex γ q ∈ Sᶜ := Finset.mem_compl.mpr hqS
  have hHeadComp : B.pathVertex γ ⟨B.length γ, by omega⟩ ∉ Sᶜ := by
    simpa using hHead
  obtain ⟨b, hqb, _, hbLeftComp, hbRightNotComp⟩ :=
    B.exists_crossing_step_between Sᶜ γ q
      ⟨B.length γ, by omega⟩ hq.2 hqComp hHeadComp
  have hbOut : B.stepLeft γ b ∉ S := by
    simpa using hbLeftComp
  have hbIn : B.stepRight γ b ∈ S := by
    by_contra hnot
    exact hbRightNotComp (Finset.mem_compl.mpr hnot)
  have haEdge : 0 < numEdges B.graph (B.stepLeft γ a) (B.stepRight γ a) := by
    simpa using B.consecutive_num_edges_pos γ a
  have hbEdge : 0 < numEdges B.graph (B.stepRight γ b) (B.stepLeft γ b) := by
    rw [num_edges_symmetric]
    simpa using B.consecutive_num_edges_pos γ b
  have haSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex γ q) (B.pathVertex α i) (B.pathVertex β j)
    S hS hNoBurn' haIn haOut haEdge
  have hbSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex γ q) (B.pathVertex α i) (B.pathVertex β j)
    S hS hNoBurn' hbIn hbOut hbEdge
  rcases haSource with haX | haY <;> rcases hbSource with hbX | hbY
  · have hγα := (interior_and_strand_eq_of_pathVertex_eq_interior B γ α
      (B.stepLeftPosition γ a) i hi (by simpa using haX)).2
    subst γ
    exact directed_boundary_sources_ne_on_same_strand B α i q a b haq hqb haX hbX
  · have hγα := (interior_and_strand_eq_of_pathVertex_eq_interior B γ α
      (B.stepLeftPosition γ a) i hi (by simpa using haX)).2
    have hγβ := (interior_and_strand_eq_of_pathVertex_eq_interior B γ β
      (B.stepRightPosition γ b) j hj (by simpa using hbY)).2
    exact hαβ (hγα.symm.trans hγβ)
  · have hγβ := (interior_and_strand_eq_of_pathVertex_eq_interior B γ β
      (B.stepLeftPosition γ a) j hj (by simpa using haY)).2
    have hγα := (interior_and_strand_eq_of_pathVertex_eq_interior B γ α
      (B.stepRightPosition γ b) i hi (by simpa using hbX)).2
    exact hαβ (hγα.symm.trans hγβ)
  · have hγβ := (interior_and_strand_eq_of_pathVertex_eq_interior B γ β
      (B.stepLeftPosition γ a) j hj (by simpa using haY)).2
    subst γ
    exact directed_boundary_sources_ne_on_same_strand B β j q a b haq hqb haY hbY

/-- Core-endpoint case of the same Dhar calculation.  With either core
endpoint and an interior chip on one strand positive, subtracting an interior
point of a different strand is reduced at the latter point. -/
theorem q_reduced_coreVertex_add_distinct_interior_path_strands
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (e : Fin 2)
    (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hjEndpoint : B.pathVertex β j ≠ B.coreVertex e)
    (hji : B.pathVertex β j ≠ B.pathVertex α i) :
    qReduced B.graph (B.pathVertex β j)
      (oneChip (B.coreVertex e) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) := by
  apply q_reduced_two_chip_sub_of_twoEdgeCutCondition_of_twoCut_burn
    B.graph (B.pathVertex β j) (B.coreVertex e) (B.pathVertex α i)
    hjEndpoint hji (graph_twoEdgeCutCondition (by omega) B)
  intro S hS hNonempty hCut
  by_contra hNoBurn
  push Not at hNoBurn
  have hqS : B.pathVertex β j ∉ S := by
    intro hmem
    have := hS hmem
    simp at this
  have hNoBurn' : ∀ z ∈ S,
      ¬ (oneChip (B.coreVertex e) z + oneChip (B.pathVertex α i) z -
        oneChip (B.pathVertex β j) z <
          ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
            (numEdges B.graph z w : ℤ)) := by
    intro z hz
    exact not_lt.mpr (hNoBurn z hz)
  have hBoundary :
      (∑ z ∈ S, ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges B.graph z w : ℤ)) = 2 := by
    unfold cutMultiplicity at hCut
    simp_rw [outdeg_S_eq_sum_filter] at hCut
    exact hCut
  have hBoth : B.coreVertex e ∈ S ∧ B.pathVertex α i ∈ S := by
    constructor
    · by_contra hx
      have hSum := Finset.sum_le_sum
        (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.coreVertex e) z +
            oneChip (B.pathVertex α i) z -
              oneChip (B.pathVertex β j) z)) ≤ 1 := by
        by_cases hy : B.pathVertex α i ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
    · by_contra hy
      have hSum := Finset.sum_le_sum
        (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.coreVertex e) z +
            oneChip (B.pathVertex α i) z -
              oneChip (B.pathVertex β j) z)) ≤ 1 := by
        by_cases hx : B.coreVertex e ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
  have hCoreSame := core_vertices_same_side_of_cutMultiplicity_two hg B S hCut
  have hZero : B.coreVertex (0 : Fin 2) ∈ S := by
    fin_cases e
    · simpa using hBoth.1
    · apply hCoreSame.mpr
      simpa using hBoth.1
  have hOne : B.coreVertex (1 : Fin 2) ∈ S := hCoreSame.mp hZero
  have finTwo : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    fin_cases t <;> simp
  have hTail : B.pathVertex β ⟨0, by omega⟩ ∈ S := by
    rw [B.pathVertex_zero]
    rcases finTwo (B.core.tail β) with ht | ht
    · simpa [ht] using hZero
    · simpa [ht] using hOne
  have hHead : B.pathVertex β ⟨B.length β, by omega⟩ ∈ S := by
    rw [B.pathVertex_length]
    rcases finTwo (B.core.head β) with hh | hh
    · simpa [hh] using hZero
    · simpa [hh] using hOne
  obtain ⟨a, _, haj, haIn, haOut⟩ :=
    B.exists_crossing_step_between S β ⟨0, by omega⟩ j hj.1 hTail hqS
  have hjComp : B.pathVertex β j ∈ Sᶜ := Finset.mem_compl.mpr hqS
  have hHeadComp : B.pathVertex β ⟨B.length β, by omega⟩ ∉ Sᶜ := by
    simpa using hHead
  obtain ⟨b, hjb, _, hbLeftComp, hbRightNotComp⟩ :=
    B.exists_crossing_step_between Sᶜ β j
      ⟨B.length β, by omega⟩ hj.2 hjComp hHeadComp
  have hbOut : B.stepLeft β b ∉ S := by
    simpa using hbLeftComp
  have hbIn : B.stepRight β b ∈ S := by
    by_contra hnot
    exact hbRightNotComp (Finset.mem_compl.mpr hnot)
  have haEdge : 0 < numEdges B.graph (B.stepLeft β a) (B.stepRight β a) := by
    simpa using B.consecutive_num_edges_pos β a
  have hbEdge : 0 < numEdges B.graph (B.stepRight β b) (B.stepLeft β b) := by
    rw [num_edges_symmetric]
    simpa using B.consecutive_num_edges_pos β b
  have haSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex β j) (B.coreVertex e) (B.pathVertex α i)
    S hS hNoBurn' haIn haOut haEdge
  have hbSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex β j) (B.coreVertex e) (B.pathVertex α i)
    S hS hNoBurn' hbIn hbOut hbEdge
  have haLeft : B.stepLeft β a = B.coreVertex e := by
    rcases haSource with haLeft | haU
    · exact haLeft
    · have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
          (B.stepLeftPosition β a) i hi (by simpa using haU)).2
      exact (hαβ hβα.symm).elim
  have hbLeft : B.stepRight β b = B.coreVertex e := by
    rcases hbSource with hbLeft | hbU
    · exact hbLeft
    · have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
          (B.stepRightPosition β b) i hi (by simpa using hbU)).2
      exact (hαβ hβα.symm).elim
  have hPath : B.pathVertex β (B.stepLeftPosition β a) =
      B.pathVertex β (B.stepRightPosition β b) := by
    rw [B.pathVertex_stepLeftPosition, B.pathVertex_stepRightPosition,
      haLeft, hbLeft]
  have hPos := congrArg Fin.val (B.pathVertex_injective β hPath)
  change a.val = b.val + 1 at hPos
  omega

/-- If the debt lies strictly to the right of the non-endpoint chip on one
banana strand, the divisor consisting of the tail chip, the interior chip,
and that debt is reduced at the debt.  No interior hypothesis is needed for
`p`: the case `p = 0` simply puts both positive chips at the tail endpoint. -/
theorem q_reduced_path_zero_add_same_strand_of_lt
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α : Fin (g + 1))
    (p q : B.PathPosition α) (hpq : p.val < q.val) :
    qReduced B.graph (B.pathVertex α q)
      (oneChip (B.pathVertex α ⟨0, by omega⟩) +
        oneChip (B.pathVertex α p) - oneChip (B.pathVertex α q)) := by
  rw [B.pathVertex_zero]
  have hqZero : B.pathVertex α q ≠ B.coreVertex (B.core.tail α) := by
    intro h
    have h' : B.pathVertex α q = B.pathVertex α ⟨0, by omega⟩ := by
      simpa only [B.pathVertex_zero] using h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h')
    change q.val = 0 at hPos
    omega

  have hqp : B.pathVertex α q ≠ B.pathVertex α p := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    omega
  apply q_reduced_two_chip_sub_of_twoEdgeCutCondition_of_twoCut_burn
    B.graph (B.pathVertex α q) (B.coreVertex (B.core.tail α))
      (B.pathVertex α p) hqZero hqp
      (graph_twoEdgeCutCondition (by omega) B)
  intro S hS hNonempty hCut
  by_contra hNoBurn
  push Not at hNoBurn
  have hqS : B.pathVertex α q ∉ S := by
    intro hmem
    have := hS hmem
    simp at this
  have hNoBurn' : ∀ z ∈ S,
      ¬ (oneChip (B.coreVertex (B.core.tail α)) z +
          oneChip (B.pathVertex α p) z - oneChip (B.pathVertex α q) z <
        ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
          (numEdges B.graph z w : ℤ)) := by
    intro z hz
    exact not_lt.mpr (hNoBurn z hz)
  have hBoundary :
      (∑ z ∈ S, ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges B.graph z w : ℤ)) = 2 := by
    unfold cutMultiplicity at hCut
    simp_rw [outdeg_S_eq_sum_filter] at hCut
    exact hCut
  have hBoth :
      B.coreVertex (B.core.tail α) ∈ S ∧ B.pathVertex α p ∈ S := by
    constructor
    · by_contra hx
      have hSum := Finset.sum_le_sum (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.coreVertex (B.core.tail α)) z +
            oneChip (B.pathVertex α p) z -
              oneChip (B.pathVertex α q) z)) ≤ 1 := by
        by_cases hy : B.pathVertex α p ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
    · by_contra hy
      have hSum := Finset.sum_le_sum (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.coreVertex (B.core.tail α)) z +
            oneChip (B.pathVertex α p) z -
              oneChip (B.pathVertex α q) z)) ≤ 1 := by
        by_cases hx : B.coreVertex (B.core.tail α) ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
  have hCoreSame := core_vertices_same_side_of_cutMultiplicity_two hg B S hCut
  have hTail : B.core.tail α = 0 ∨ B.core.tail α = 1 := by
    exact finTwo (e := B.core.tail α)
  have hZero : B.coreVertex (0 : Fin 2) ∈ S := by
    rcases hTail with hTail | hTail
    · simpa [hTail] using hBoth.1
    · apply hCoreSame.mpr
      simpa [hTail] using hBoth.1
  have hOne : B.coreVertex (1 : Fin 2) ∈ S := hCoreSame.mp hZero
  have hHead : B.core.head α = 0 ∨ B.core.head α = 1 := by
    exact finTwo (e := B.core.head α)
  have hHeadMem : B.pathVertex α ⟨B.length α, by omega⟩ ∈ S := by
    rw [B.pathVertex_length]
    rcases hHead with hHead | hHead
    · simpa [hHead] using hZero
    · simpa [hHead] using hOne
  have hqComp : B.pathVertex α q ∈ Sᶜ := Finset.mem_compl.mpr hqS
  have hHeadComp : B.pathVertex α ⟨B.length α, by omega⟩ ∉ Sᶜ := by
    simpa using hHeadMem
  have hqLt : q.val < B.length α := by
    by_contra hqNot
    have hqEq : q = ⟨B.length α, by omega⟩ := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ q.isLt) (Nat.le_of_not_gt hqNot)
    exact hqS (by rw [hqEq]; exact hHeadMem)
  obtain ⟨b, hqb, _, hbLeftComp, hbRightNotComp⟩ :=
    B.exists_crossing_step_between Sᶜ α q
      ⟨B.length α, by omega⟩ hqLt hqComp hHeadComp
  have hbOut : B.stepLeft α b ∉ S := by
    simpa using hbLeftComp
  have hbIn : B.stepRight α b ∈ S := by
    by_contra hnot
    exact hbRightNotComp (Finset.mem_compl.mpr hnot)
  have hbEdge : 0 < numEdges B.graph (B.stepRight α b) (B.stepLeft α b) := by
    rw [num_edges_symmetric]
    simpa using B.consecutive_num_edges_pos α b
  have hbSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex α q) (B.coreVertex (B.core.tail α))
      (B.pathVertex α p) S hS hNoBurn' hbIn hbOut hbEdge
  rcases hbSource with hbZero | hbP
  · have hPath : B.pathVertex α (B.stepRightPosition α b) =
        B.pathVertex α ⟨0, by omega⟩ := by
      rw [B.pathVertex_stepRightPosition, B.pathVertex_zero]
      exact hbZero
    have hPos := congrArg Fin.val (B.pathVertex_injective α hPath)
    change b.val + 1 = 0 at hPos
    omega
  · have hPath : B.pathVertex α (B.stepRightPosition α b) =
        B.pathVertex α p := by
      rw [B.pathVertex_stepRightPosition]
      exact hbP
    have hPos := congrArg Fin.val (B.pathVertex_injective α hPath)
    change b.val + 1 = p.val at hPos
    omega

/-- If the debt lies strictly to the left of the non-endpoint chip on one
banana strand, the divisor consisting of the interior chip, the head chip,
and that debt is reduced at the debt.  This is the head-endpoint counterpart
of `q_reduced_path_zero_add_same_strand_of_lt`. -/
theorem q_reduced_same_strand_add_path_length_of_lt
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α : Fin (g + 1))
    (p q : B.PathPosition α) (hqp : q.val < p.val) :
    qReduced B.graph (B.pathVertex α q)
      (oneChip (B.pathVertex α p) +
        oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
          oneChip (B.pathVertex α q)) := by
  rw [B.pathVertex_length]
  have hqpVertex : B.pathVertex α q ≠ B.pathVertex α p := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    omega

  have hqHead : B.pathVertex α q ≠ B.coreVertex (B.core.head α) := by
    intro h
    have h' : B.pathVertex α q =
        B.pathVertex α ⟨B.length α, by omega⟩ := by
      simpa only [B.pathVertex_length] using h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h')
    change q.val = B.length α at hPos
    omega
  apply q_reduced_two_chip_sub_of_twoEdgeCutCondition_of_twoCut_burn
    B.graph (B.pathVertex α q) (B.pathVertex α p)
      (B.coreVertex (B.core.head α)) hqpVertex hqHead
      (graph_twoEdgeCutCondition (by omega) B)
  intro S hS hNonempty hCut
  by_contra hNoBurn
  push Not at hNoBurn
  have hqS : B.pathVertex α q ∉ S := by
    intro hmem
    have := hS hmem
    simp at this
  have hNoBurn' : ∀ z ∈ S,
      ¬ (oneChip (B.pathVertex α p) z +
          oneChip (B.coreVertex (B.core.head α)) z -
            oneChip (B.pathVertex α q) z <
        ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
          (numEdges B.graph z w : ℤ)) := by
    intro z hz
    exact not_lt.mpr (hNoBurn z hz)
  have hBoundary :
      (∑ z ∈ S, ∑ w ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges B.graph z w : ℤ)) = 2 := by
    unfold cutMultiplicity at hCut
    simp_rw [outdeg_S_eq_sum_filter] at hCut
    exact hCut
  have hBoth :
      B.pathVertex α p ∈ S ∧ B.coreVertex (B.core.head α) ∈ S := by
    constructor
    · by_contra hx
      have hSum := Finset.sum_le_sum (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.pathVertex α p) z +
            oneChip (B.coreVertex (B.core.head α)) z -
              oneChip (B.pathVertex α q) z)) ≤ 1 := by
        by_cases hy : B.coreVertex (B.core.head α) ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
    · by_contra hy
      have hSum := Finset.sum_le_sum (fun z hz => hNoBurn z hz)
      have hMass :
          (∑ z ∈ S, (oneChip (B.pathVertex α p) z +
            oneChip (B.coreVertex (B.core.head α)) z -
              oneChip (B.pathVertex α q) z)) ≤ 1 := by
        by_cases hx : B.pathVertex α p ∈ S <;>
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, oneChip,
            hx, hy, hqS]
      omega
  have hCoreSame := core_vertices_same_side_of_cutMultiplicity_two hg B S hCut
  have hHead : B.core.head α = 0 ∨ B.core.head α = 1 := by
    exact finTwo (e := B.core.head α)
  have hZero : B.coreVertex (0 : Fin 2) ∈ S := by
    rcases hHead with hHead | hHead
    · simpa [hHead] using hBoth.2
    · apply hCoreSame.mpr
      simpa [hHead] using hBoth.2
  have hOne : B.coreVertex (1 : Fin 2) ∈ S := hCoreSame.mp hZero
  have hTail : B.core.tail α = 0 ∨ B.core.tail α = 1 := by
    exact finTwo (e := B.core.tail α)
  have hTailMem : B.pathVertex α ⟨0, by omega⟩ ∈ S := by
    rw [B.pathVertex_zero]
    rcases hTail with hTail | hTail
    · simpa [hTail] using hZero
    · simpa [hTail] using hOne
  have hqPos : 0 < q.val := by
    by_contra h
    have hqZero : q = ⟨0, by omega⟩ := by
      apply Fin.ext
      simpa using Nat.eq_zero_of_not_pos h
    exact hqS (by simpa [hqZero] using hTailMem)
  obtain ⟨a, _, haq, haIn, haOut⟩ :=
    B.exists_crossing_step_between S α ⟨0, by omega⟩ q hqPos hTailMem hqS
  have haEdge : 0 < numEdges B.graph (B.stepLeft α a) (B.stepRight α a) := by
    simpa using B.consecutive_num_edges_pos α a
  have haSource := boundary_source_eq_left_or_right_of_two_chip_no_burn
    B.graph (B.pathVertex α q) (B.pathVertex α p)
      (B.coreVertex (B.core.head α)) S hS hNoBurn' haIn haOut haEdge
  rcases haSource with haP | haHead
  · have hPath : B.pathVertex α (B.stepLeftPosition α a) =
        B.pathVertex α p := by
      rw [B.pathVertex_stepLeftPosition]
      exact haP
    have hPos := congrArg Fin.val (B.pathVertex_injective α hPath)
    change a.val = p.val at hPos
    omega
  · have hPath : B.pathVertex α (B.stepLeftPosition α a) =
        B.pathVertex α ⟨B.length α, by omega⟩ := by
      rw [B.pathVertex_stepLeftPosition, B.pathVertex_length]
      exact haHead
    have hPos := congrArg Fin.val (B.pathVertex_injective α hPath)
    change a.val = B.length α at hPos
    omega

/-- Rank form of the two endpoint reducedness lemmas. -/
theorem rank_path_zero_add_same_strand_sub_of_lt
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α : Fin (g + 1))
    (p q : B.PathPosition α) (hpq : p.val < q.val) :
    rank B.graph
      (oneChip (B.pathVertex α ⟨0, by omega⟩) +
        oneChip (B.pathVertex α p) - oneChip (B.pathVertex α q)) = -1 := by
  have hqZero : B.pathVertex α q ≠ B.pathVertex α ⟨0, by omega⟩ := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    change q.val = 0 at hPos
    omega
  have hqp : B.pathVertex α q ≠ B.pathVertex α p := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    omega
  have hqZero' : B.pathVertex α q ≠ B.pathVertex α 0 := by
    intro h
    apply hqZero
    simpa using h
  let D : CFDiv B.graph := oneChip (B.pathVertex α ⟨0, by omega⟩) +
      oneChip (B.pathVertex α p) - oneChip (B.pathVertex α q)
  have hred : qReduced B.graph (B.pathVertex α q) D := by
    simpa [D] using q_reduced_path_zero_add_same_strand_of_lt hg B α p q hpq
  have hneg : D (B.pathVertex α q) < 0 := by
    simp [D, oneChip, hqZero', hqp]
  exact rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex α q) D hred hneg

theorem rank_same_strand_add_path_length_sub_of_lt
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α : Fin (g + 1))
    (p q : B.PathPosition α) (hqp : q.val < p.val) :
    rank B.graph
      (oneChip (B.pathVertex α p) +
        oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
          oneChip (B.pathVertex α q)) = -1 := by
  have hqP : B.pathVertex α q ≠ B.pathVertex α p := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    omega
  have hqLength : B.pathVertex α q ≠
      B.pathVertex α ⟨B.length α, by omega⟩ := by
    intro h
    have hPos := congrArg Fin.val (B.pathVertex_injective α h)
    simp at hPos
    omega
  have hqHead : B.pathVertex α q ≠ B.coreVertex (B.core.head α) := by
    intro h
    apply hqLength
    simpa [B.pathVertex_length] using h
  let D : CFDiv B.graph := oneChip (B.pathVertex α p) +
      oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
        oneChip (B.pathVertex α q)
  have hred : qReduced B.graph (B.pathVertex α q) D := by
    simpa [D] using q_reduced_same_strand_add_path_length_of_lt hg B α p q hqp
  have hneg : D (B.pathVertex α q) < 0 := by
    simp [D, oneChip, hqP, hqHead]
  exact rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex α q) D hred hneg

theorem rank_same_path_pair_sub_of_sum_outside
    (B : Banana 2) (α : Fin 3)
    (i k q : B.PathPosition α)
    (hRight : i.val + k.val < B.length α ∧ i.val + k.val < q.val) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k) -
        oneChip (B.pathVertex α q)) = -1 := by
  by_cases hi0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := by apply Fin.ext; exact hi0
    rw [hi]
    simpa [add_comm] using
      rank_path_zero_add_same_strand_sub_of_lt (by omega : 2 ≤ 2)
        B α k q (by omega)
  by_cases hk0 : k.val = 0
  · have hk : k = ⟨0, by omega⟩ := by apply Fin.ext; exact hk0
    rw [hk]
    simpa only [add_comm] using
      rank_path_zero_add_same_strand_sub_of_lt (by omega : 2 ≤ 2)
        B α i q (by omega)
  have hi : B.IsInteriorPosition α i := by
    change 0 < i.val ∧ i.val < B.length α
    exact ⟨by omega, by omega⟩
  have hk : B.IsInteriorPosition α k := by
    change 0 < k.val ∧ k.val < B.length α
    exact ⟨by omega, by omega⟩
  have hSlide := path_pair_linearEquiv_tail_sum B α i k hi.1 hk.1 hRight.1
  have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
    hSlide (B.pathVertex α q)
  have hRankEq := rank_eq_of_linear_equiv B.graph hShift
  have hTail := rank_path_zero_add_same_strand_sub_of_lt
    (by omega : 2 ≤ 2) B α ⟨i.val + k.val, by omega⟩ q hRight.2
  have hTail' : rank B.graph
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.pathVertex α ⟨i.val + k.val, by omega⟩) -
        oneChip (B.pathVertex α q)) = -1 := by
    simpa only [B.pathVertex_zero] using hTail
  rw [hTail'] at hRankEq
  omega

theorem rank_same_path_pair_sub_of_sum_outside_interior
    (B : Banana 2) (α : Fin 3)
    (i k q : B.PathPosition α)
    (hi : B.IsInteriorPosition α i)
    (hk : B.IsInteriorPosition α k)
    (hRight : i.val + k.val < B.length α ∧ i.val + k.val < q.val) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k) -
        oneChip (B.pathVertex α q)) = -1 := by
  have hSlide := path_pair_linearEquiv_tail_sum B α i k hi.1 hk.1 hRight.1
  have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
    hSlide (B.pathVertex α q)
  have hRankEq := rank_eq_of_linear_equiv B.graph hShift
  have hTail := rank_path_zero_add_same_strand_sub_of_lt
    (by omega : 2 ≤ 2) B α ⟨i.val + k.val, by omega⟩ q hRight.2
  have hTail' : rank B.graph
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.pathVertex α ⟨i.val + k.val, by omega⟩) -
        oneChip (B.pathVertex α q)) = -1 := by
    simpa only [B.pathVertex_zero] using hTail
  rw [hTail'] at hRankEq
  omega

theorem rank_same_path_pair_sub_of_sum_outside_left
    (B : Banana 2) (α : Fin 3)
    (i k q : B.PathPosition α)
    (hLeft : B.length α < i.val + k.val ∧
      q.val < i.val + k.val - B.length α) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k) -
        oneChip (B.pathVertex α q)) = -1 := by
  by_cases hiL : i.val = B.length α
  · have hi : i = ⟨B.length α, by omega⟩ := by apply Fin.ext; exact hiL
    rw [hi]
    simpa [add_comm] using
      rank_same_strand_add_path_length_sub_of_lt (by omega : 2 ≤ 2)
        B α k q (by omega)
  by_cases hkL : k.val = B.length α
  · have hk : k = ⟨B.length α, by omega⟩ := by apply Fin.ext; exact hkL
    rw [hk]
    exact rank_same_strand_add_path_length_sub_of_lt (by omega : 2 ≤ 2)
      B α i q (by omega)
  have hi : B.IsInteriorPosition α i := by
    change 0 < i.val ∧ i.val < B.length α
    exact ⟨by omega, by omega⟩
  have hk : B.IsInteriorPosition α k := by
    change 0 < k.val ∧ k.val < B.length α
    exact ⟨by omega, by omega⟩
  have hSlide := path_pair_linearEquiv_head_excess B α i k hi.2 hk.2 hLeft.1
  have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
    hSlide (B.pathVertex α q)
  have hRankEq := rank_eq_of_linear_equiv B.graph hShift
  have hHead := rank_same_strand_add_path_length_sub_of_lt
    (by omega : 2 ≤ 2) B α
      ⟨i.val + k.val - B.length α, by omega⟩ q hLeft.2
  have hHead' : rank B.graph
      (oneChip (B.pathVertex α ⟨i.val + k.val - B.length α, by omega⟩) +
        oneChip (B.coreVertex (B.core.head α)) -
        oneChip (B.pathVertex α q)) = -1 := by
    simpa [B.pathVertex_length, add_comm] using hHead
  rw [hHead'] at hRankEq
  omega

/-- General-coordinate version of the same-strand interval implication. -/
theorem same_strand_pair_sub_zero_forces_interval_general
    (B : Banana 2) (α : Fin 3)
    (i j k : B.PathPosition α)
    (hij : i.val < j.val)
    (hPair : rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 0)
    (hSub : rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k) -
        oneChip (B.pathVertex α j)) = 0) :
    k.val ≠ B.length α - i.val ∧
      j.val - i.val ≤ k.val ∧ k.val ≤ j.val - i.val + B.length α := by
  have hNotReflect : i.val + k.val ≠ B.length α := by
    intro hsum
    have hOne := rank_path_pair_eq_one_of_sum_eq_length B α i k hsum
    omega
  have hLower : j.val - i.val ≤ k.val := by
    by_contra h
    have hNeg := rank_same_path_pair_sub_of_sum_outside B α i k j
      ⟨by omega, by omega⟩
    omega
  have hUpper : k.val ≤ j.val - i.val + B.length α := by
    by_contra h
    have hNeg := rank_same_path_pair_sub_of_sum_outside_left B α i k j
      ⟨by omega, by omega⟩
    omega
  refine ⟨?_, hLower, hUpper⟩
  intro hReflect
  apply hNotReflect
  omega

/-- Every core vertex is one of the two endpoint descriptions of a strand. -/
theorem coreVertex_eq_pathVertex_zero_or_length
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (e : Fin 2) :
    B.coreVertex e = B.pathVertex α ⟨0, by omega⟩ ∨
      B.coreVertex e = B.pathVertex α ⟨B.length α, by omega⟩ := by
  by_cases hTail : e = B.core.tail α
  · left
    rw [B.pathVertex_zero]
    exact congrArg B.coreVertex hTail
  · right
    rw [B.pathVertex_length]
    have hHead : e = B.core.head α := by
      apply Fin.ext
      have he := e.isLt
      have ht := (B.core.tail α).isLt
      have hh := (B.core.head α).isLt
      have hTailVal : e.val ≠ (B.core.tail α).val := by
        intro h
        exact hTail (Fin.ext h)
      have hLoopVal : (B.core.tail α).val ≠ (B.core.head α).val := by
        intro h
        exact B.core_loopless α (Fin.ext h)
      omega
    exact congrArg B.coreVertex hHead

/-- For interior marks, a rank-zero normal-form auxiliary vertex must lie on
the marked strand; off-strand interior auxiliaries are ruled out by the
distinct-strand reducedness theorem. -/
theorem same_strand_auxiliary_vertex_interval
    (B : Banana 2) (α : Fin 3)
    (i j : B.PathPosition α)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition α j)
    (hij : i.val < j.val)
    (w : B.graph.V)
    (hwv : w ≠ B.pathVertex α j)
    (hPair : rank B.graph
      (oneChip w + oneChip (B.pathVertex α i)) = 0)
    (hSub : rank B.graph
      (oneChip w + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex α j)) = 0) :
    ∃ k : B.PathPosition α, w = B.pathVertex α k ∧
      k.val ≠ B.length α - i.val ∧
      j.val - i.val ≤ k.val ∧ k.val ≤ j.val - i.val + B.length α := by
  rcases w with e | ⟨γ, off⟩
  · obtain hEnd | hEnd := coreVertex_eq_pathVertex_zero_or_length B α e
    · let k : B.PathPosition α := ⟨0, by omega⟩
      have hPair' : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i)) = 0 := by
        rw [← hEnd]
        exact hPair
      have hSub' : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex α j)) = 0 := by
        rw [← hEnd]
        exact hSub
      obtain ⟨hk, hInt⟩ := same_strand_pair_sub_zero_forces_interval_general
        B α i j k hij (by simpa [add_comm] using hPair')
          (by simpa [add_comm] using hSub')
      exact ⟨k, hEnd, hk, hInt.1, hInt.2⟩
    · let k : B.PathPosition α := ⟨B.length α, by omega⟩
      have hPair' : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i)) = 0 := by
        rw [← hEnd]
        exact hPair
      have hSub' : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex α j)) = 0 := by
        rw [← hEnd]
        exact hSub
      obtain ⟨hk, hInt⟩ := same_strand_pair_sub_zero_forces_interval_general
        B α i j k hij (by simpa [add_comm] using hPair')
          (by simpa [add_comm] using hSub')
      exact ⟨k, hEnd, hk, hInt.1, hInt.2⟩
  · let k : B.PathPosition γ := ⟨off.val + 1, by
      have hoff := off.isLt
      have hlen := B.length_pos γ
      omega⟩
    have hk : B.IsInteriorPosition γ k := by
      change 0 < off.val + 1 ∧ off.val + 1 < B.length γ
      have hoff := off.isLt
      have hlen := B.length_pos γ
      omega
    have hwPath : B.interiorVertex γ off = B.pathVertex γ k := by
      rw [B.pathVertex_eq_interiorVertex γ k hk]
      congr 1
    have hPairPath : rank B.graph
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i)) = 0 := by
      rw [← hwPath]
      exact hPair
    have hSubPath : rank B.graph
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
          oneChip (B.pathVertex α j)) = 0 := by
      rw [← hwPath]
      exact hSub
    by_cases hγα : γ = α
    · subst γ
      obtain ⟨hK, hInt⟩ := same_strand_pair_sub_zero_forces_interval_general
        B α i j k hij (by simpa [add_comm] using hPairPath)
          (by simpa [add_comm] using hSubPath)
      exact ⟨k, hwPath, hK, hInt.1, hInt.2⟩
    · have hji : B.pathVertex α i ≠ B.pathVertex α j := by
        intro h
        have hPos := congrArg Fin.val (B.pathVertex_injective α h)
        omega
      have hqW : B.pathVertex α j ≠ B.pathVertex γ k := by
        intro h
        apply hwv
        change B.interiorVertex γ off = B.pathVertex α j
        rw [hwPath]
        exact h.symm
      have hqU : B.pathVertex α j ≠ B.pathVertex α i := by
        intro h
        have hPos := congrArg Fin.val (B.pathVertex_injective α h)
        omega
      have hRed := q_reduced_distinct_interior_path_strands
        (by omega) B γ α α k i j hk hi hj hγα hqW hqU
      have hDebt :
          ((oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex α j) : CFDiv B.graph)
              (B.pathVertex α j)) < 0 := by
        simp [oneChip, hqW, hqU]
      have hRank := rank_eq_neg_one_of_qReduced_debt B.graph
        (B.pathVertex α j)
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
          oneChip (B.pathVertex α j)) hRed hDebt
      exfalso
      omega
/-- Left-endpoint specialization of the core-endpoint Dhar calculation. -/
theorem q_reduced_leftEndpoint_add_distinct_interior_path_strands
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hjLeft : B.pathVertex β j ≠ leftEndpoint B)
    (hji : B.pathVertex β j ≠ B.pathVertex α i) :
    qReduced B.graph (B.pathVertex β j)
      (oneChip (leftEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) := by
  simpa [leftEndpoint] using
    q_reduced_coreVertex_add_distinct_interior_path_strands hg B 0 α β i j
      hi hj hαβ (by simpa [leftEndpoint] using hjLeft) hji

/-- Right-endpoint specialization of the core-endpoint Dhar calculation. -/
theorem q_reduced_rightEndpoint_add_distinct_interior_path_strands
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hjRight : B.pathVertex β j ≠ rightEndpoint B)
    (hji : B.pathVertex β j ≠ B.pathVertex α i) :
    qReduced B.graph (B.pathVertex β j)
      (oneChip (rightEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) := by
  simpa [rightEndpoint] using
    q_reduced_coreVertex_add_distinct_interior_path_strands hg B 1 α β i j
      hi hj hαβ (by simpa [rightEndpoint] using hjRight) hji

/-- In particular, the left endpoint cannot be the auxiliary vertex in a
rank-zero `w + u - v` configuration with distinct interior marked strands. -/
theorem rank_leftEndpoint_add_distinct_interior_path_marks_ne_zero
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rank B.graph
      (oneChip (leftEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) ≠ 0 := by
  have hjLeft : B.pathVertex β j ≠ leftEndpoint B := by
    intro h
    unfold leftEndpoint at h
    rw [B.pathVertex_eq_interiorVertex β j hj] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  have hji : B.pathVertex β j ≠ B.pathVertex α i := by
    intro h
    have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
      j i hi h).2
    exact hαβ hβα.symm
  have hRed := q_reduced_leftEndpoint_add_distinct_interior_path_strands
    (by omega) B α β i j hi hj hαβ hjLeft hji
  have hDebt :
      ((oneChip (leftEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j) : CFDiv B.graph) (B.pathVertex β j)) < 0 := by
    simp [oneChip, hjLeft, hji]
  have hRank := rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex β j)
    (oneChip (leftEndpoint B) + oneChip (B.pathVertex α i) -
      oneChip (B.pathVertex β j)) hRed hDebt
  omega

/-- The right endpoint likewise cannot be the auxiliary vertex in a
rank-zero `w + u - v` configuration with distinct interior marked strands. -/
theorem rank_rightEndpoint_add_distinct_interior_path_marks_ne_zero
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rank B.graph
      (oneChip (rightEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) ≠ 0 := by
  have hjRight : B.pathVertex β j ≠ rightEndpoint B := by
    intro h
    unfold rightEndpoint at h
    rw [B.pathVertex_eq_interiorVertex β j hj] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  have hji : B.pathVertex β j ≠ B.pathVertex α i := by
    intro h
    have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
      j i hi h).2
    exact hαβ hβα.symm
  have hRed := q_reduced_rightEndpoint_add_distinct_interior_path_strands
    (by omega) B α β i j hi hj hαβ hjRight hji
  have hDebt :
      ((oneChip (rightEndpoint B) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j) : CFDiv B.graph) (B.pathVertex β j)) < 0 := by
    simp [oneChip, hjRight, hji]
  have hRank := rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex β j)
    (oneChip (rightEndpoint B) + oneChip (B.pathVertex α i) -
      oneChip (B.pathVertex β j)) hRed hDebt
  omega

/-- Coordinate-free core-endpoint version used when decomposing an arbitrary
auxiliary vertex into core and interior cases. -/
theorem rank_coreVertex_add_distinct_interior_path_marks_ne_zero
    (B : Banana 2) (e : Fin 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rank B.graph
      (oneChip (B.coreVertex e) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) ≠ 0 := by
  have hjEndpoint : B.pathVertex β j ≠ B.coreVertex e := by
    intro h
    rw [B.pathVertex_eq_interiorVertex β j hj] at h
    simp [SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex] at h
  have hji : B.pathVertex β j ≠ B.pathVertex α i := by
    intro h
    have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
      j i hi h).2
    exact hαβ hβα.symm
  have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
    (by omega) B e α β i j hi hj hαβ hjEndpoint hji
  have hDebt :
      ((oneChip (B.coreVertex e) + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j) : CFDiv B.graph)
          (B.pathVertex β j)) < 0 := by
    simp [oneChip, hjEndpoint, hji]
  have hRank := rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex β j)
    (oneChip (B.coreVertex e) + oneChip (B.pathVertex α i) -
      oneChip (B.pathVertex β j)) hRed hDebt
  omega

/-- The remaining on-strand case of `SameStrand`.  If the two positive
vertices are interior points of one theta strand and their pair has rank
zero, then subtracting an interior point of a different strand cannot leave
rank zero.  The rank-zero hypothesis is essential: it excludes the reflected
pair, whose coordinate sum is the strand length. -/
theorem rank_same_path_pair_sub_distinct_interior_ne_zero
    (B : Banana 2) (α β : Fin 3)
    (i k : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hk : B.IsInteriorPosition α k)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hPairRank : rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 0) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k) -
        oneChip (B.pathVertex β j)) ≠ 0 := by
  rcases lt_trichotomy (i.val + k.val) (B.length α) with hsum | hsum | hsum
  · let p : B.PathPosition α := ⟨i.val + k.val, by omega⟩
    have hp : B.IsInteriorPosition α p := by
      change 0 < i.val + k.val ∧ i.val + k.val < B.length α
      exact ⟨Nat.add_pos_left hi.1 _, hsum⟩
    have hjEndpoint : B.pathVertex β j ≠
        B.coreVertex (B.core.tail α) := by
      intro h
      rw [B.pathVertex_eq_interiorVertex β j hj] at h
      simp [SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex] at h
    have hjp : B.pathVertex β j ≠ B.pathVertex α p := by
      intro h
      have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
        j p hp h).2
      exact hαβ hβα.symm
    have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
      (by omega) B (B.core.tail α) α β p j hp hj hαβ hjEndpoint hjp
    have hDebt :
        ((oneChip (B.coreVertex (B.core.tail α)) +
          oneChip (B.pathVertex α p) - oneChip (B.pathVertex β j) :
            CFDiv B.graph) (B.pathVertex β j)) < 0 := by
      simp [oneChip, hjEndpoint, hjp]
    have hEndpointRank := rank_eq_neg_one_of_qReduced_debt B.graph
      (B.pathVertex β j)
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.pathVertex α p) - oneChip (B.pathVertex β j))
      hRed hDebt
    have hSlide := path_pair_linearEquiv_tail_sum B α i k hi.1 hk.1 hsum
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide (B.pathVertex β j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    intro hZero
    dsimp [p] at hEndpointRank hRankEq
    rw [hZero, hEndpointRank] at hRankEq
    omega
  · have hReflected := rank_path_pair_eq_one_of_sum_eq_length B α i k hsum
    omega
  · let p : B.PathPosition α :=
      ⟨i.val + k.val - B.length α, by omega⟩
    have hp : B.IsInteriorPosition α p := by
      change 0 < i.val + k.val - B.length α ∧
        i.val + k.val - B.length α < B.length α
      constructor
      · omega
      · have hiBound := hi.2
        have hkBound := hk.2
        omega
    have hjEndpoint : B.pathVertex β j ≠
        B.coreVertex (B.core.head α) := by
      intro h
      rw [B.pathVertex_eq_interiorVertex β j hj] at h
      simp [SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex] at h
    have hjp : B.pathVertex β j ≠ B.pathVertex α p := by
      intro h
      have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
        j p hp h).2
      exact hαβ hβα.symm
    have hRed := q_reduced_coreVertex_add_distinct_interior_path_strands
      (by omega) B (B.core.head α) α β p j hp hj hαβ hjEndpoint hjp
    have hDebt :
        ((oneChip (B.coreVertex (B.core.head α)) +
          oneChip (B.pathVertex α p) - oneChip (B.pathVertex β j) :
            CFDiv B.graph) (B.pathVertex β j)) < 0 := by
      simp [oneChip, hjEndpoint, hjp]
    have hEndpointRank := rank_eq_neg_one_of_qReduced_debt B.graph
      (B.pathVertex β j)
      (oneChip (B.coreVertex (B.core.head α)) +
        oneChip (B.pathVertex α p) - oneChip (B.pathVertex β j))
      hRed hDebt
    have hSlide := path_pair_linearEquiv_head_excess B α i k hi.2 hk.2 hsum
    have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
      hSlide (B.pathVertex β j)
    have hRankEq := rank_eq_of_linear_equiv B.graph hShift
    intro hZero
    have hEndpointRank' : rank B.graph
        (oneChip (B.pathVertex α p) +
          oneChip (B.coreVertex (B.core.head α)) -
            oneChip (B.pathVertex β j)) = -1 := by
      simpa only [add_comm] using hEndpointRank
    dsimp [p] at hEndpointRank' hRankEq
    rw [hZero, hEndpointRank'] at hRankEq
    omega


/-- Full auxiliary-vertex form needed by the negative-`rankDelta` bridge.
For distinct interior theta marks `u` and `v`, a rank-zero positive pair
`w+u` with `w ≠ v` cannot still have rank zero after subtracting `v`. -/
theorem rank_aux_add_mark_sub_distinct_mark_ne_zero
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) (w : B.graph.V)
    (hwv : w ≠ B.pathVertex β j)
    (hPairRank : rank B.graph
      (oneChip w + oneChip (B.pathVertex α i)) = 0) :
    rank B.graph
      (oneChip w + oneChip (B.pathVertex α i) -
        oneChip (B.pathVertex β j)) ≠ 0 := by
  rcases w with e | interior
  · simpa [SubdivisionGraph.Spec.coreVertex] using
      rank_coreVertex_add_distinct_interior_path_marks_ne_zero
        B e α β i j hi hj hαβ
  · rcases interior with ⟨γ, off⟩
    let k : B.PathPosition γ := ⟨off.val + 1, by
      have hoff := off.isLt
      have hlen := B.length_pos γ
      omega⟩
    have hk : B.IsInteriorPosition γ k := by
      change 0 < off.val + 1 ∧ off.val + 1 < B.length γ
      have hoff := off.isLt
      have hlen := B.length_pos γ
      omega

    have hwPath : B.interiorVertex γ off = B.pathVertex γ k := by
      rw [B.pathVertex_eq_interiorVertex γ k hk]
      congr 1
    have hPairRankPath : rank B.graph
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i)) = 0 := by
      rw [← hwPath]
      exact hPairRank
    by_cases hγα : γ = α
    · subst γ
      have hPairRank' : rank B.graph
          (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 0 := by
        simpa [add_comm] using hPairRankPath
      have hOnStrand := rank_same_path_pair_sub_distinct_interior_ne_zero
        B α β i k j hi hk hj hαβ hPairRank'
      intro hZero
      apply hOnStrand
      have hZeroPath : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j)) = 0 := by
        rw [← hwPath]
        exact hZero
      simpa [add_comm] using hZeroPath
    · have hqW : B.pathVertex β j ≠ B.pathVertex γ k := by
        intro h
        apply hwv
        change B.interiorVertex γ off = B.pathVertex β j
        rw [hwPath]
        exact h.symm
      have hqU : B.pathVertex β j ≠ B.pathVertex α i := by
        intro h
        have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
          j i hi h).2
        exact hαβ hβα.symm
      have hRed := q_reduced_distinct_interior_path_strands
        (by omega) B γ α β k i j hk hi hj hγα hqW hqU
      have hDebt :
          ((oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j) : CFDiv B.graph)
              (B.pathVertex β j)) < 0 := by
        simp [oneChip, hqW, hqU]
      have hRank := rank_eq_neg_one_of_qReduced_debt B.graph
        (B.pathVertex β j)
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
          oneChip (B.pathVertex β j)) hRed hDebt
      intro hZero
      have hZero' : rank B.graph
          (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j)) = 0 := by
        rw [← hwPath]
        exact hZero
      omega

private theorem linearEquiv_zero_of_rank_nonneg_degree_zero_sameStrand
    (G : CFGraph) (D : CFDiv G) (hRank : 0 ≤ rank G D) (hDeg : deg D = 0) :
    linearEquiv G D 0 := by
  obtain ⟨E, hEff, hDE⟩ := (rank_nonneg_iff_winnable G D).mp
    ((rank_geq_iff G D 0).mpr hRank)
  have hEDeg : deg E = 0 := by
    rw [← linear_equiv_preserves_deg G D E hDE, hDeg]
  have hE : E = 0 := eff_degree_zero E hEff hEDeg
  simpa [hE] using hDE

theorem rank_same_strand_pair_zero_of_not_reflection
    (B : Banana 2) (α : Fin 3)
    (i k : B.PathPosition α)
    (hNot : strandVertex B α k ≠ strandVertex B α (strandMirror B α i)) :
    rank B.graph
      (oneChip (strandVertex B α i) + oneChip (strandVertex B α k)) = 0 := by
  let D : CFDiv B.graph :=
    oneChip (strandVertex B α i) + oneChip (strandVertex B α k)
  have hEff : effective D := by
    intro v
    simp [D, oneChip]
    omega
  have hNonneg : 0 ≤ rank B.graph D := by
    apply (rank_geq_iff B.graph D 0).mp
    exact (rank_nonneg_iff_winnable B.graph D).mpr
      (winnable_of_effective B.graph D hEff)
  have hDeg : deg D = 2 := by
    dsimp [D]
    simp [deg.map_add, deg_one_chip]
  have hKDeg : deg (canonicalDivisor B.graph - D) = 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph, hDeg]
    norm_num
  have hRR := riemann_roch_for_graphs (graphConnected B) D
  have hKLe : rank B.graph (canonicalDivisor B.graph - D) ≤ 0 := by
    by_cases hKNonneg : 0 ≤ rank B.graph (canonicalDivisor B.graph - D)
    · have hBound := rank_le_degree B.graph
        (canonicalDivisor B.graph - D)
        (rank B.graph (canonicalDivisor B.graph - D)) hKNonneg
        ((rank_geq_iff B.graph _ _).mpr le_rfl)
      omega
    · omega
  have hRankLe : rank B.graph D ≤ 1 := by
    rw [B.genus_graph, hDeg] at hRR
    omega
  by_cases hZero : rank B.graph D = 0
  · simpa [D] using hZero
  · have hOne : rank B.graph D = 1 := by omega
    have hKRank : rank B.graph (canonicalDivisor B.graph - D) = 0 := by
      rw [B.genus_graph, hDeg, hOne] at hRR
      omega
    have hKEquiv := linearEquiv_zero_of_rank_nonneg_degree_zero_sameStrand B.graph
      (canonicalDivisor B.graph - D) (by omega) hKDeg
    have hDK : linearEquiv B.graph D (canonicalDivisor B.graph) := by
      unfold linearEquiv at hKEquiv ⊢
      simpa [sub_eq_add_neg] using
        AddSubgroup.neg_mem (principalDivisors B.graph) hKEquiv
    have hRef := endpoint_sum_linearEquiv_strand_reflection B α i
    have hCan : canonicalDivisor B.graph =
        oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
      simpa using canonical_divisor_eq_endpoints B
    rw [← hCan] at hRef
    have hResidual : linearEquiv B.graph
        (oneChip (strandVertex B α k))
        (canonicalDivisor B.graph - oneChip (strandVertex B α i)) := by
      unfold linearEquiv at hDK ⊢
      convert hDK using 1 ; dsimp [D] ; abel
    have hRefResidual : linearEquiv B.graph
        (canonicalDivisor B.graph - oneChip (strandVertex B α i))
        (oneChip (strandVertex B α (strandMirror B α i))) := by
      unfold linearEquiv at hRef ⊢
      convert hRef using 1 ; abel
    have hVertices : strandVertex B α k =
        strandVertex B α (strandMirror B α i) :=
      one_chip_representative_unique_on_banana (by omega) B
        (x := strandVertex B α k)
        (y := strandVertex B α (strandMirror B α i))
        hResidual.symm hRefResidual
    exact (hNot hVertices).elim

private theorem rank_one_chip_eq_zero_banana_two
    (B : Banana 2) (x : B.graph.V) :
    rank B.graph (oneChip x) = 0 := by
  let y : B.graph.V :=
    if x = leftEndpoint B then rightEndpoint B else leftEndpoint B
  have hxy : x ≠ y := by
    dsimp [y]
    split_ifs with hx
    · rw [hx]
      simp [leftEndpoint, rightEndpoint, SubdivisionGraph.Spec.coreVertex]
    · exact hx
  have hWinnable : winnable B.graph (oneChip x) :=
    winnable_of_effective B.graph _ (eff_one_chip x)
  have hNonneg : 0 ≤ rank B.graph (oneChip x) :=
    (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr hWinnable)
  have hLt : rank B.graph (oneChip x) < 1 := by
    by_contra hNot
    have hRank : rank B.graph (oneChip x) ≥ 1 := by omega
    have hxyWin := (rank_ge_one_iff_winnable_sub_one_chip B.graph
      (oneChip x)).mp hRank y
    obtain ⟨E, hEff, hEquiv⟩ := hxyWin
    have hEDeg : deg E = 0 := by
      rw [← linear_equiv_preserves_deg B.graph _ E hEquiv,
        deg.map_sub, deg_one_chip, deg_one_chip]
      norm_num
    have hZero : E = 0 := eff_degree_zero E hEff hEDeg
    apply marks_not_linearEquiv (by omega : 1 ≤ 2) B hxy
    simpa [hZero] using hEquiv
  omega

theorem rank_one_chip_zero_banana_two
    (B : Banana 2) (x : B.graph.V) :
    rank B.graph (oneChip x) = 0 :=
  rank_one_chip_eq_zero_banana_two B x

theorem rank_same_path_pair_sub_of_sum_inside_full
    (B : Banana 2) (alpha : Fin 3)
    (i k q : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hk : B.IsInteriorPosition alpha k)
    (hq : B.IsInteriorPosition alpha q)
    (hInside : i.val + k.val - B.length alpha ≤ q.val ∧
      q.val ≤ i.val + k.val) :
    rank B.graph
      (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k) -
        oneChip (B.pathVertex alpha q)) = 0 := by
  by_cases hNotReflect : i.val + k.val ≠ B.length alpha
  · by_cases hsum : i.val + k.val < B.length alpha
    · have hSlide := path_pair_linearEquiv_tail_sum B alpha i k hi.1 hk.1 hsum
      have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
        hSlide (B.pathVertex alpha q)
      by_cases hqSum : q.val = i.val + k.val
      · have hqEq : q = ⟨i.val + k.val, by omega⟩ := by
          apply Fin.ext
          exact hqSum
        have hRankEq := rank_eq_of_linear_equiv B.graph hShift
        rw [hqEq] at hRankEq
        have hCancel :
            oneChip (B.coreVertex (B.core.tail alpha)) +
                oneChip (B.pathVertex alpha ⟨i.val + k.val, by omega⟩) -
                  oneChip (B.pathVertex alpha ⟨i.val + k.val, by omega⟩) =
              oneChip (G := B.graph) (B.coreVertex (B.core.tail alpha)) := by
          abel
        rw [hCancel, rank_one_chip_eq_zero_banana_two] at hRankEq
        simpa only [hqEq] using hRankEq
      · have hqLt : q.val < i.val + k.val := by omega
        have hPrin := prin_subinterval_reflection (spec := B) (star := alpha)
          (lo := 0) (hi := i.val + k.val) (target := q.val)
          hq.1 hqLt (by omega)
        have hReflect : linearEquiv B.graph
            (oneChip (B.coreVertex (B.core.tail alpha)) +
                oneChip (B.pathVertex alpha ⟨i.val + k.val, by omega⟩) -
                  oneChip (B.pathVertex alpha q))
            (oneChip (B.pathVertex alpha
              ⟨0 + (i.val + k.val) - q.val, by omega⟩)) := by
          unfold linearEquiv
          apply (principal_iff_eq_prin B.graph _).mpr
          refine ⟨segScript B alpha 0 (i.val + k.val) q.val, ?_⟩
          rw [hPrin, B.pathVertex_zero]
          abel
        have hTotal := hShift.trans hReflect
        have hRankEq := rank_eq_of_linear_equiv B.graph hTotal
        rw [rank_one_chip_eq_zero_banana_two] at hRankEq
        omega
    · have hsum' : B.length alpha < i.val + k.val := by omega
      have hSlide := path_pair_linearEquiv_head_excess B alpha i k hi.2 hk.2 hsum'
      have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
        hSlide (B.pathVertex alpha q)
      by_cases hqLo : q.val = i.val + k.val - B.length alpha
      · have hqEq : q = ⟨i.val + k.val - B.length alpha, by omega⟩ := by
          apply Fin.ext
          exact hqLo
        have hRankEq := rank_eq_of_linear_equiv B.graph hShift
        rw [hqEq] at hRankEq
        have hCancel :
            oneChip (B.pathVertex alpha
                ⟨i.val + k.val - B.length alpha, by omega⟩) +
                oneChip (B.coreVertex (B.core.head alpha)) -
                  oneChip (B.pathVertex alpha
                    ⟨i.val + k.val - B.length alpha, by omega⟩) =
              oneChip (G := B.graph) (B.coreVertex (B.core.head alpha)) := by
          abel
        rw [hCancel, rank_one_chip_eq_zero_banana_two] at hRankEq
        simpa only [hqEq] using hRankEq
      · have hqGt : i.val + k.val - B.length alpha < q.val := by omega
        have hPrin := prin_subinterval_reflection (spec := B) (star := alpha)
          (lo := i.val + k.val - B.length alpha)
          (hi := B.length alpha) (target := q.val)
          hqGt hq.2 (by omega)
        have hReflect : linearEquiv B.graph
            (oneChip (B.pathVertex alpha
                ⟨i.val + k.val - B.length alpha, by omega⟩) +
                oneChip (B.coreVertex (B.core.head alpha)) -
                  oneChip (B.pathVertex alpha q))
            (oneChip (B.pathVertex alpha
              ⟨(i.val + k.val - B.length alpha) + B.length alpha - q.val,
                by omega⟩)) := by
          unfold linearEquiv
          apply (principal_iff_eq_prin B.graph _).mpr
          refine ⟨segScript B alpha (i.val + k.val - B.length alpha)
            (B.length alpha) q.val, ?_⟩
          rw [hPrin, B.pathVertex_length]
          abel
        have hTotal := hShift.trans hReflect
        have hRankEq := rank_eq_of_linear_equiv B.graph hTotal
        rw [rank_one_chip_eq_zero_banana_two] at hRankEq
        omega
  · have hReflect : i.val + k.val = B.length alpha := by omega
    let D : CFDiv B.graph :=
      oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)
    let E : CFDiv B.graph := D - oneChip (B.pathVertex alpha q)
    have hDRank : rank B.graph D = 1 := by
      dsimp [D]
      exact rank_path_pair_eq_one_of_sum_eq_length B alpha i k hReflect
    have hERankNonneg : 0 ≤ rank B.graph E := by
      have hStep := rank_sub_one_chip_ge_rank_sub_one D (B.pathVertex alpha q)
      dsimp [E]
      rw [hDRank] at hStep
      omega
    have hEWin : winnable B.graph E :=
      (rank_nonneg_iff_winnable B.graph E).mp
        ((rank_geq_iff B.graph E 0).mpr hERankNonneg)
    obtain ⟨F, hFEff, hEF⟩ := hEWin
    have hEDeg : deg E = 1 := by
      dsimp [E, D]
      rw [deg.map_sub, deg.map_add, deg_one_chip, deg_one_chip, deg_one_chip]
      norm_num
    have hFDeg : deg F = 1 := by
      rw [← linear_equiv_preserves_deg B.graph E F hEF, hEDeg]
    obtain ⟨x, rfl⟩ := effective_degree_one_eq_one_chip F hFEff hFDeg
    have hRankEq := rank_eq_of_linear_equiv B.graph hEF
    rw [rank_one_chip_eq_zero_banana_two] at hRankEq
    dsimp [E, D] at hRankEq
    exact hRankEq
/-
    have hwPath : B.interiorVertex γ off = B.pathVertex γ k := by
      rw [B.pathVertex_eq_interiorVertex γ k hk]
      congr 1
    have hPairRankPath : rank B.graph
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i)) = 0 := by
      rw [← hwPath]
      exact hPairRank
    by_cases hγα : γ = α
    · subst γ
      have hPairRank' : rank B.graph
          (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k)) = 0 := by
        simpa [add_comm] using hPairRankPath
      have hOnStrand := rank_same_path_pair_sub_distinct_interior_ne_zero
        B α β i k j hi hk hj hαβ hPairRank'
      intro hZero
      apply hOnStrand
      have hZeroPath : rank B.graph
          (oneChip (B.pathVertex α k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j)) = 0 := by
        rw [← hwPath]
        exact hZero
      simpa [add_comm] using hZeroPath
    · have hqW : B.pathVertex β j ≠ B.pathVertex γ k := by
        intro h
        apply hwv
        change B.interiorVertex γ off = B.pathVertex β j
        rw [hwPath]
        exact h.symm
      have hqU : B.pathVertex β j ≠ B.pathVertex α i := by
        intro h
        have hβα := (interior_and_strand_eq_of_pathVertex_eq_interior B β α
          j i hi h).2
        exact hαβ hβα.symm
      have hRed := q_reduced_distinct_interior_path_strands
        (by omega) B γ α β k i j hk hi hj hγα hqW hqU
      have hDebt :
          ((oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j) : CFDiv B.graph)
              (B.pathVertex β j)) < 0 := by
        simp [oneChip, hqW, hqU]
      have hRank := rank_eq_neg_one_of_qReduced_debt B.graph
        (B.pathVertex β j)
        (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
          oneChip (B.pathVertex β j)) hRed hDebt
      intro hZero
      have hZero' : rank B.graph
          (oneChip (B.pathVertex γ k) + oneChip (B.pathVertex α i) -
            oneChip (B.pathVertex β j)) = 0 := by
        rw [← hwPath]
        exact hZero
      omega
 -/

end Bananas
