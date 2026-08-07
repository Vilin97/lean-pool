/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData
import LeanPool.Erdos97ConvexOctagon.LRAT.Semantics

/-!
# Exhaustive coverage formula

This module gives mathematical meaning to every clause identifier used by the
checked LRAT certificates.  The formula describes normalized balanced
four-out incidence tables, pair sparsity, and the audited geometric
obstructions.
-/

namespace Erdos97Octagon

open LRAT

namespace RawIncidence

/-- A proposition-valued SAT assignment obtained from an incidence table. -/
def valuation (R : RawIncidence) : LRAT.Valuation := fun index =>
  ∃ centre target : Vertex,
    index = varIndex centre target ∧ target ∈ R centre

/-- Reading the SAT assignment at an incidence variable recovers membership. -/
theorem valuation_variable (R : RawIncidence) (centre target : Vertex) :
    valuation R (varIndex centre target) ↔ target ∈ R centre := by
  constructor
  · rintro ⟨centre', target', hindex, hmem⟩
    have hcentreVal : centre'.val = centre.val := by
      unfold varIndex at hindex
      omega
    have htargetVal : target'.val = target.val := by
      unfold varIndex at hindex
      omega
    have hcentre : centre' = centre := Fin.ext hcentreVal
    have htarget : target' = target := Fin.ext htargetVal
    simpa [hcentre, htarget] using hmem
  · intro hmem
    exact ⟨centre, target, rfl, hmem⟩

/-- Five-, two-, and three-subsets in the lexicographic order used by the generator. -/
def fiveSubsets : List (List Vertex) :=
  ((List.finRange 8).sublistsLen 5).reverse

/-- Vertex triples in the lexicographic order used by the generator. -/
def vertexTriples : List (List Vertex) :=
  ((List.finRange 8).sublistsLen 3).reverse

private def pairAt (index : ℕ) : Vertex × Vertex :=
  match vertexPairs.getD index [] with
  | [a, b] => (a, b)
  | _ => (0, 0)

/-- Semantic tags for clauses shared by every branch certificate. -/
inductive BaseClauseTag where
  | diagonal (vertex : Vertex)
  | normalized (target : Vertex)
  | rowAtMost (centre : Vertex) (subset : List Vertex)
  | rowAtLeast (centre : Vertex) (subset : List Vertex)
  | columnAtMost (target : Vertex) (centres : List Vertex)
  | columnAtLeast (target : Vertex) (centres : List Vertex)
  | pairSparse (a b : Vertex) (centres : List Vertex)
  | pattern (origin : ℕ)
  | hard (origin : ℕ)

/-- A shared clause or one of the sixteen row-fixing clauses for a branch. -/
inductive ClauseTag where
  | base (tag : BaseClauseTag)
  | branchOne (target : Vertex) (selected : Bool)
  | branchTwo (target : Vertex) (selected : Bool)

private def patternMask (origin : ℕ) : UInt64 :=
  match patternEntry origin with
  | some entry => entry.mask
  | none => 0

private def hardCode (origin : ℕ) : UInt64 :=
  match hardEntry origin with
  | some entry => entry.code
  | none => 0

private def unitClause (centre target : Vertex) (selected : Bool) : Clause :=
  [if selected then .positive (varIndex centre target) else .negative (varIndex centre target)]

/-- The literal list represented by a shared semantic clause tag. -/
def BaseClauseTag.toClause : BaseClauseTag → Clause
  | .diagonal vertex => [.negative (varIndex vertex vertex)]
  | .normalized target => unitClause 0 target (bitSetB 30 target.val)
  | .rowAtMost centre subset => subset.map fun target => .negative (varIndex centre target)
  | .rowAtLeast centre subset => subset.map fun target => .positive (varIndex centre target)
  | .columnAtMost target centres => centres.map fun centre => .negative (varIndex centre target)
  | .columnAtLeast target centres => centres.map fun centre => .positive (varIndex centre target)
  | .pairSparse a b centres => centres.flatMap fun centre =>
      [.negative (varIndex centre a), .negative (varIndex centre b)]
  | .pattern origin =>
      ((List.range 64).filter fun index => bitSetB (patternMask origin) index).map .negative
  | .hard origin => (List.range 64).map fun index =>
      if bitSetB (hardCode origin) index then .negative index else .positive index

/-- The literal list represented by any semantic clause tag. -/
def ClauseTag.toClause : ClauseTag → Clause
  | .base tag => tag.toClause
  | .branchOne target selected => unitClause 1 target selected
  | .branchTwo target selected => unitClause 2 target selected

/-- Structural and lookup conditions needed for a shared tag to be meaningful. -/
def BaseClauseTag.Valid : BaseClauseTag → Prop
  | .rowAtMost _ subset | .rowAtLeast _ subset |
      .columnAtMost _ subset | .columnAtLeast _ subset =>
      subset.Nodup ∧ subset.length = 5
  | .pairSparse a b centres => a ≠ b ∧ centres.Nodup ∧ centres.length = 3
  | .pattern origin =>
      match patternEntry origin with
      | some entry => entry.validB = true
      | none => False
  | .hard origin =>
      match hardEntry origin with
      | some entry => entry.validB = true
      | none => False
  | _ => True

/-- Structural and lookup conditions needed for any tag to be meaningful. -/
def ClauseTag.Valid : ClauseTag → Prop
  | .base tag => tag.Valid
  | _ => True

/-- The two branch-unit tags agree with the two rows fixed for this SAT branch. -/
def ClauseTag.BranchValid (Q : OctagonIncidence) : ClauseTag → Prop
  | .branchOne target selected => selected = true ↔ target ∈ Q.targets 1
  | .branchTwo target selected => selected = true ↔ target ∈ Q.targets 2
  | _ => True

/-- Boolean checker for the structural validity of a semantic clause tag. -/
def ClauseTag.validB : ClauseTag → Bool
  | .base (.rowAtMost _ subset) | .base (.rowAtLeast _ subset) |
      .base (.columnAtMost _ subset) | .base (.columnAtLeast _ subset) =>
      decide (subset.Nodup ∧ subset.length = 5)
  | .base (.pairSparse a b centres) =>
      decide (a ≠ b ∧ centres.Nodup ∧ centres.length = 3)
  | .base (.pattern origin) => match patternEntry origin with
    | some entry => entry.validB
    | none => false
  | .base (.hard origin) => match hardEntry origin with
    | some entry => entry.validB
    | none => false
  | _ => true

theorem ClauseTag.valid_of_validB {tag : ClauseTag} (h : tag.validB = true) : tag.Valid :=
  by
    cases tag with
    | base tag =>
        cases tag <;> simp only [ClauseTag.validB, ClauseTag.Valid,
          BaseClauseTag.Valid, decide_eq_true_eq] at h ⊢
        all_goals try exact h
        all_goals split <;> simp_all
    | branchOne | branchTwo => trivial

private def branchStart : ℕ := 20659
private def branchEnd : ℕ := branchStart + 16

/-- Decode a generator clause identifier. -/
def tagOfRef (rowOne rowTwo : UInt64) (reference : ℕ) : ClauseTag :=
  if reference < 8 then
    .base (.diagonal (Fin.ofNat 8 reference))
  else if reference < 16 then
    .base (.normalized (Fin.ofNat 8 (reference - 8)))
  else if reference < 912 then
    let offset := reference - 16
    let centre := Fin.ofNat 8 (offset / 112)
    let subset := fiveSubsets.getD ((offset % 112) / 2) []
    .base (if offset % 2 = 0 then .rowAtMost centre subset else .rowAtLeast centre subset)
  else if reference < 1808 then
    let offset := reference - 912
    let target := Fin.ofNat 8 (offset / 112)
    let centres := fiveSubsets.getD ((offset % 112) / 2) []
    .base (if offset % 2 = 0 then .columnAtMost target centres else .columnAtLeast target centres)
  else if reference < 3376 then
    let offset := reference - 1808
    let pair := pairAt (offset / 56)
    .base (.pairSparse pair.1 pair.2 (vertexTriples.getD (offset % 56) []))
  else if reference < 14419 then
    .base (.pattern (reference - 3376))
  else if reference < branchStart then
    .base (.hard (reference - 14419))
  else if reference < branchStart + 8 then
    let target := Fin.ofNat 8 (reference - branchStart)
    .branchOne target (bitSetB rowOne target.val)
  else
    let target := Fin.ofNat 8 (reference - branchStart - 8)
    .branchTwo target (bitSetB rowTwo target.val)

private theorem tagOfRef_branchValid
    (Q : OctagonIncidence) {rowOne rowTwo : UInt64}
    (hrowOne : Q.targets 1 = packedRow rowOne)
    (hrowTwo : Q.targets 2 = packedRow rowTwo) (reference : ℕ) :
    (tagOfRef rowOne rowTwo reference).BranchValid Q := by
  unfold tagOfRef
  split
  · trivial
  split
  · trivial
  split
  · trivial
  split
  · trivial
  split
  · trivial
  split
  · trivial
  split
  · trivial
  split
  · dsimp only [ClauseTag.BranchValid]
    rw [hrowOne, mem_packedRow]
  · dsimp only [ClauseTag.BranchValid]
    rw [hrowTwo, mem_packedRow]

/-- A shared-clause reference has no branch-specific semantic condition. -/
theorem tagOfRef_baseBranchValid
    (Q : OctagonIncidence) {reference : ℕ} (hreference : reference < branchStart) :
    (tagOfRef 0 0 reference).BranchValid Q := by
  unfold tagOfRef
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial

/-- Check that a clause reference is in range and has an audited semantic payload. -/
def coveredB (rowOne rowTwo : UInt64) (reference : ℕ) : Bool :=
  decide (reference < branchEnd) && (tagOfRef rowOne rowTwo reference).validB

/-- The formula encoded by a branch's ordered list of clause references. -/
def coverageFormula (rowOne rowTwo : UInt64) (references : List ℕ) : Formula :=
  references.map fun reference => (tagOfRef rowOne rowTwo reference).toClause

private theorem satisfies_of_not_all_neg
    (valuation : Valuation) (clause : Clause)
    (h : ¬ List.Forall valuation.falsifies clause) :
    valuation.satisfies clause := by
  induction clause with
  | nil => simp at h
  | cons literal clause ih =>
      intro hliteral
      apply ih
      intro hrest
      apply h
      simpa using And.intro hliteral hrest

private theorem no_five_inside_card_four
    {selected : Finset Vertex} (hcard : selected.card = 4)
    {vertices : List Vertex} (hnodup : vertices.Nodup) (hlength : vertices.length = 5)
    (hsubset : vertices.toFinset ⊆ selected) : False := by
  have hfive : vertices.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hnodup, hlength]
  have hle := Finset.card_le_card hsubset
  rw [hfive, hcard] at hle
  omega

private theorem no_card_four_avoids_five
    {selected : Finset Vertex} (hcard : selected.card = 4)
    {vertices : List Vertex} (hnodup : vertices.Nodup) (hlength : vertices.length = 5)
    (havoid : ∀ vertex ∈ vertices, vertex ∉ selected) : False := by
  have hfive : vertices.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hnodup, hlength]
  have hsubset : selected ⊆ Finset.univ \ vertices.toFinset := by
    intro vertex hselected
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_toFinset]
    exact fun hvertex => havoid vertex hvertex hselected
  have hcomplement : (Finset.univ \ vertices.toFinset).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hfive]
  have hle := Finset.card_le_card hsubset
  rw [hcard, hcomplement] at hle
  omega

private def predecessors (Q : OctagonIncidence) (target : Vertex) : Finset Vertex :=
  Finset.univ.filter fun centre => target ∈ Q.targets centre

private theorem card_predecessors (Q : OctagonIncidence) (target : Vertex) :
    (predecessors Q target).card = Q.indegree target := by
  unfold predecessors OctagonIncidence.indegree
  rw [Finset.sum_boole]
  norm_num

private def jointPredecessors
    (Q : OctagonIncidence) (a b : Vertex) : Finset Vertex :=
  Finset.univ.filter fun centre => a ∈ Q.targets centre ∧ b ∈ Q.targets centre

private theorem card_jointPredecessors (Q : OctagonIncidence) (a b : Vertex) :
    (jointPredecessors Q a b).card = Q.pairMultiplicity a b := by
  unfold jointPredecessors OctagonIncidence.pairMultiplicity
  rw [Finset.sum_boole]
  norm_num

private theorem unitClause_satisfied
    (R : RawIncidence) (centre target : Vertex) (selected : Bool)
    (hselected : selected = true ↔ target ∈ R centre) :
    (valuation R).satisfies (unitClause centre target selected) := by
  cases selected <;>
    simpa [unitClause, LRAT.Valuation.satisfies, LRAT.Valuation.falsifies,
      valuation_variable] using hselected

private theorem standardTargets_bit (target : Vertex) :
    bitSetB 30 target.val = true ↔ target ∈ standardTargets := by
  fin_cases target <;> decide

/-- Every audited semantic clause is satisfied by the corresponding geometric incidence table. -/
theorem BaseClauseTag.satisfies
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (tag : BaseClauseTag) (hvalid : tag.Valid) :
    (valuation Q.targets).satisfies tag.toClause := by
  cases tag with
  | diagonal vertex =>
      simp only [BaseClauseTag.toClause, LRAT.Valuation.satisfies,
        LRAT.Valuation.falsifies]
      intro hselected
      exact Q.centre_not_mem vertex ((valuation_variable _ _ _).mp hselected)
  | normalized target =>
      apply unitClause_satisfied
      rw [hN]
      exact standardTargets_bit target
  | rowAtMost centre subset =>
      simp only [BaseClauseTag.Valid] at hvalid
      apply satisfies_of_not_all_neg
      intro hall
      rw [List.forall_iff_forall_mem] at hall
      apply no_five_inside_card_four (Q.card_targets centre) hvalid.1 hvalid.2
      intro target htarget
      have htargetList : target ∈ subset := by simpa using htarget
      apply (valuation_variable Q.targets centre target).mp
      exact hall (.negative (varIndex centre target))
        (List.mem_map.mpr ⟨target, htargetList, rfl⟩)
  | rowAtLeast centre subset =>
      simp only [BaseClauseTag.Valid] at hvalid
      apply satisfies_of_not_all_neg
      intro hall
      rw [List.forall_iff_forall_mem] at hall
      apply no_card_four_avoids_five (Q.card_targets centre) hvalid.1 hvalid.2
      intro target htarget hselected
      exact (hall (.positive (varIndex centre target))
        (List.mem_map.mpr ⟨target, htarget, rfl⟩))
        ((valuation_variable Q.targets centre target).mpr hselected)
  | columnAtMost target centres =>
      simp only [BaseClauseTag.Valid] at hvalid
      apply satisfies_of_not_all_neg
      intro hall
      rw [List.forall_iff_forall_mem] at hall
      have hcard : (predecessors Q target).card = 4 := by
        rw [card_predecessors, hBalanced target]
      apply no_five_inside_card_four hcard hvalid.1 hvalid.2
      intro centre hcentre
      have hcentreList : centre ∈ centres := by simpa using hcentre
      rw [predecessors, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (valuation_variable Q.targets centre target).mp
        (hall (.negative (varIndex centre target))
          (List.mem_map.mpr ⟨centre, hcentreList, rfl⟩))⟩
  | columnAtLeast target centres =>
      simp only [BaseClauseTag.Valid] at hvalid
      apply satisfies_of_not_all_neg
      intro hall
      rw [List.forall_iff_forall_mem] at hall
      have hcard : (predecessors Q target).card = 4 := by
        rw [card_predecessors, hBalanced target]
      apply no_card_four_avoids_five hcard hvalid.1 hvalid.2
      intro centre hcentre hselected
      have htarget : target ∈ Q.targets centre :=
        (Finset.mem_filter.mp (show centre ∈ Finset.univ.filter
          (fun centre => target ∈ Q.targets centre) from hselected)).2
      exact (hall (.positive (varIndex centre target))
        (List.mem_map.mpr ⟨centre, hcentre, rfl⟩))
        ((valuation_variable Q.targets centre target).mpr htarget)
  | pairSparse a b centres =>
      simp only [BaseClauseTag.Valid] at hvalid
      apply satisfies_of_not_all_neg
      intro hall
      rw [List.forall_iff_forall_mem] at hall
      have hsubset : centres.toFinset ⊆ jointPredecessors Q a b := by
        intro centre hcentre
        have hcentreList : centre ∈ centres := by simpa using hcentre
        rw [jointPredecessors, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · apply (valuation_variable Q.targets centre a).mp
          apply hall (.negative (varIndex centre a))
          change LRAT.Literal.negative (varIndex centre a) ∈ centres.flatMap (fun centre =>
            [LRAT.Literal.negative (varIndex centre a),
              LRAT.Literal.negative (varIndex centre b)])
          rw [List.mem_flatMap]
          exact ⟨centre, hcentreList, by simp⟩
        · apply (valuation_variable Q.targets centre b).mp
          apply hall (.negative (varIndex centre b))
          change LRAT.Literal.negative (varIndex centre b) ∈ centres.flatMap (fun centre =>
            [LRAT.Literal.negative (varIndex centre a),
              LRAT.Literal.negative (varIndex centre b)])
          rw [List.mem_flatMap]
          exact ⟨centre, hcentreList, by simp⟩
      have hthree : centres.toFinset.card = 3 := by
        rw [List.toFinset_card_of_nodup hvalid.2.1, hvalid.2.2]
      have hle := Finset.card_le_card hsubset
      have hsparse : (jointPredecessors Q a b).card ≤ 2 := by
        rw [card_jointPredecessors]
        exact hSparse hvalid.1
      rw [hthree] at hle
      omega
  | pattern origin =>
      simp only [BaseClauseTag.Valid] at hvalid
      cases hfind : patternEntry origin with
      | none => simp [hfind] at hvalid
      | some entry =>
          have hentryValid : entry.certificate.toCertificate.Valid
              (packedIncidence entry.mask) :=
            PatternEntry.valid_of_validB (by simpa only [hfind] using hvalid)
          have hmask : patternMask origin = entry.mask := by simp [patternMask, hfind]
          apply satisfies_of_not_all_neg
          intro hall
          rw [List.forall_iff_forall_mem] at hall
          have hextends : Extends (packedIncidence entry.mask) Q.targets := by
            intro centre target hselected
            apply (valuation_variable Q.targets centre target).mp
            apply hall (.negative (varIndex centre target))
            simp only [BaseClauseTag.toClause, hmask, List.mem_map]
            refine ⟨varIndex centre target, ?_, rfl⟩
            rw [List.mem_filter]
            refine ⟨List.mem_range.mpr ?_, ?_⟩
            · unfold varIndex
              omega
            · simpa [packedSelectsB] using
                (mem_packedIncidence entry.mask centre target).mp hselected
          exact Certificate.not_convex_realises entry.certificate.toCertificate
            (entry.certificate.valid_mono hextends hentryValid) hC hR
  | hard origin =>
      simp only [BaseClauseTag.Valid] at hvalid
      cases hfind : hardEntry origin with
      | none => simp [hfind] at hvalid
      | some entry =>
          have hentryValid : entry.certificate.Valid (packedIncidence entry.code) :=
            HardEntry.valid_of_validB (by simpa only [hfind] using hvalid)
          have hcode : hardCode origin = entry.code := by simp [hardCode, hfind]
          apply satisfies_of_not_all_neg
          intro hall
          rw [List.forall_iff_forall_mem] at hall
          have htargets : Q.targets = packedIncidence entry.code := by
            funext centre
            ext target
            rw [mem_packedIncidence]
            unfold packedSelectsB
            cases hbit : bitSetB entry.code (varIndex centre target) with
            | false =>
                simp only [Bool.false_eq_true, iff_false]
                intro hselected
                have hfalsified := hall (.positive (varIndex centre target)) (by
                  simp only [BaseClauseTag.toClause, hcode, List.mem_map]
                  refine ⟨varIndex centre target, List.mem_range.mpr ?_, ?_⟩
                  · unfold varIndex
                    omega
                  · simp [hbit])
                exact hfalsified ((valuation_variable Q.targets centre target).mpr hselected)
            | true =>
                constructor
                · intro _
                  trivial
                · intro _
                  apply (valuation_variable Q.targets centre target).mp
                  apply hall (.negative (varIndex centre target))
                  simp only [BaseClauseTag.toClause, hcode, List.mem_map]
                  refine ⟨varIndex centre target, List.mem_range.mpr ?_, ?_⟩
                  · unfold varIndex
                    omega
                  · simp [hbit]
          have hcertificate : entry.certificate.Valid Q.targets := by
            rw [htargets]
            exact hentryValid
          exact Certificate.not_convex_realises entry.certificate hcertificate hC hR

/-- Every audited shared or branch clause is satisfied by the incidence table. -/
theorem ClauseTag.satisfies
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (tag : ClauseTag) (hvalid : tag.Valid) (hbranch : tag.BranchValid Q) :
    (valuation Q.targets).satisfies tag.toClause := by
  cases tag with
  | base baseTag =>
      exact baseTag.satisfies hC hR hN hSparse hBalanced hvalid
  | branchOne target selected =>
      exact unitClause_satisfied Q.targets 1 target selected hbranch
  | branchTwo target selected =>
      exact unitClause_satisfied Q.targets 2 target selected hbranch

/-- A covered reference list is satisfied by the corresponding incidence table. -/
theorem coverageFormula_satisfied
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    {rowOne rowTwo : UInt64}
    (hrowOne : Q.targets 1 = packedRow rowOne)
    (hrowTwo : Q.targets 2 = packedRow rowTwo)
    (references : List ℕ)
    (hcovered : references.all (coveredB rowOne rowTwo) = true) :
    (valuation Q.targets).SatisfiesFormula (coverageFormula rowOne rowTwo references) := by
  constructor
  intro clause hclause
  rw [coverageFormula, List.mem_map] at hclause
  obtain ⟨reference, hreference, rfl⟩ := hclause
  have hcoveredReference := (List.all_eq_true.mp hcovered) reference hreference
  simp only [coveredB, Bool.and_eq_true] at hcoveredReference
  exact (tagOfRef rowOne rowTwo reference).satisfies hC hR hN hSparse hBalanced
    ((tagOfRef rowOne rowTwo reference).valid_of_validB hcoveredReference.2)
    (tagOfRef_branchValid Q hrowOne hrowTwo reference)

end RawIncidence

end Erdos97Octagon
