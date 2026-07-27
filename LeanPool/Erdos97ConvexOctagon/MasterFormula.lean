/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.RowSymmetry

/-!
# Master coverage formula

The master formula combines every valid shared semantic clause with one clause
excluding each noncanonical first row.  It has 64 variables and 6,582 clauses.
-/

namespace Erdos97Octagon.RawIncidence

open LRAT

/-- References of every valid shared semantic clause, in generator order. -/
def masterReferences : List ℕ :=
  (List.range 20659).filter fun reference =>
    (tagOfRef 0 0 reference).validB

/-- The seven canonical first rows viewed as finite sets. -/
def canonicalRows : List (Finset Vertex) :=
  List.ofFn fun orbit : Fin 7 => packedRow (canonicalRowMask orbit)

/-- Every eight-bit row, in numeric mask order. -/
def allPackedRows : List (Finset Vertex) :=
  (List.range 256).map fun mask => packedRow (UInt64.ofNat mask)

/-- The 249 rows outside the seven canonical symmetry classes. -/
def excludedRows : List (Finset Vertex) :=
  allPackedRows.filter fun row => row ∉ canonicalRows

/-- A clause which is false precisely when row one equals `row`. -/
def rowExclusionClause (row : Finset Vertex) : Clause :=
  List.ofFn fun target : Vertex =>
    if target ∈ row then
      .negative (varIndex 1 target)
    else
      .positive (varIndex 1 target)

/-- All valid shared clauses. -/
def masterBaseFormula : Formula :=
  masterReferences.map fun reference => (tagOfRef 0 0 reference).toClause

/-- Clauses restricting row one to the seven canonical rows. -/
def canonicalRowFormula : Formula :=
  excludedRows.map rowExclusionClause

/-- The single formula checked by the committed LRAT certificate. -/
def masterFormula : Formula :=
  masterBaseFormula ++ canonicalRowFormula

/-- A valid in-range shared reference gives its clause directly from the master formula. -/
theorem masterBaseClause_proves
    (reference : ℕ) (hrange : decide (reference < 20659) = true)
    (hvalid : (tagOfRef 0 0 reference).validB = true)
    (clause : Clause) (hclause : clause = (tagOfRef 0 0 reference).toClause) :
    masterFormula.Proves clause := by
  subst clause
  intro valuation hsatisfies
  apply hsatisfies.property
  rw [masterFormula, List.mem_append, masterBaseFormula, List.mem_map]
  apply Or.inl
  refine ⟨reference, ?_, rfl⟩
  rw [masterReferences, List.mem_filter]
  exact ⟨List.mem_range.mpr (of_decide_eq_true hrange), hvalid⟩

/-- A noncanonical in-range row mask gives its exclusion clause from the master formula. -/
theorem canonicalRowClause_proves
    (mask : ℕ) (hrange : decide (mask < 256) = true)
    (hnoncanonical :
      decide (packedRow (UInt64.ofNat mask) ∉ canonicalRows) = true)
    (clause : Clause)
    (hclause : clause = rowExclusionClause (packedRow (UInt64.ofNat mask))) :
    masterFormula.Proves clause := by
  subst clause
  intro valuation hsatisfies
  apply hsatisfies.property
  rw [masterFormula, List.mem_append, canonicalRowFormula, List.mem_map]
  apply Or.inr
  refine ⟨packedRow (UInt64.ofNat mask), ?_, rfl⟩
  rw [excludedRows, List.mem_filter]
  refine ⟨?_, hnoncanonical⟩
  rw [allPackedRows, List.mem_map]
  exact ⟨mask, List.mem_range.mpr (of_decide_eq_true hrange), rfl⟩

private theorem rowExclusionClause_satisfied
    (Q : OctagonIncidence) (row : Finset Vertex)
    (hne : Q.targets 1 ≠ row) :
    (valuation Q.targets).satisfies (rowExclusionClause row) := by
  apply LRAT.Valuation.satisfiesOfNotAllFalsified
  intro hall
  apply hne
  ext target
  rw [List.forall_iff_forall_mem] at hall
  have hmember :
      (if target ∈ row then
          LRAT.Literal.negative (varIndex 1 target)
        else
          LRAT.Literal.positive (varIndex 1 target)) ∈ rowExclusionClause row := by
    rw [rowExclusionClause, List.mem_ofFn]
    exact ⟨target, rfl⟩
  by_cases htarget : target ∈ row
  · have hfalsified := hall _ hmember
    simpa [htarget, LRAT.Valuation.falsifies, valuation_variable] using hfalsified
  · have hfalsified := hall _ hmember
    simpa [htarget, LRAT.Valuation.falsifies, valuation_variable] using hfalsified

private theorem masterBaseFormula_satisfied
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced) :
    (valuation Q.targets).SatisfiesFormula masterBaseFormula := by
  constructor
  intro clause hclause
  rw [masterBaseFormula, List.mem_map] at hclause
  obtain ⟨reference, hreference, rfl⟩ := hclause
  have hparts := List.mem_filter.mp hreference
  exact (tagOfRef 0 0 reference).satisfies hC hR hN hSparse hBalanced
    ((tagOfRef 0 0 reference).valid_of_validB hparts.2)
    (tagOfRef_baseBranchValid Q (List.mem_range.mp hparts.1))

/-- The canonical-row clauses are satisfied for one selected canonical orbit. -/
theorem canonicalRowFormula_satisfied
    (Q : OctagonIncidence) (orbit : Fin 7)
    (hrow : Q.targets 1 = packedRow (canonicalRowMask orbit)) :
    (valuation Q.targets).SatisfiesFormula canonicalRowFormula := by
  constructor
  intro clause hclause
  rw [canonicalRowFormula, List.mem_map] at hclause
  obtain ⟨row, hrowExcluded, rfl⟩ := hclause
  apply rowExclusionClause_satisfied
  intro hequal
  have hcanonical : row ∈ canonicalRows := by
    rw [← hequal, hrow]
    unfold canonicalRows
    rw [List.mem_ofFn]
    exact ⟨orbit, rfl⟩
  have hnotCanonical : row ∉ canonicalRows :=
    of_decide_eq_true (List.mem_filter.mp hrowExcluded).2
  exact hnotCanonical hcanonical

/-- Every hypothetical normalized counterexample with canonical row one
satisfies the master formula. -/
theorem masterFormula_satisfied
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (orbit : Fin 7)
    (hrow : Q.targets 1 = packedRow (canonicalRowMask orbit)) :
    (valuation Q.targets).SatisfiesFormula masterFormula := by
  constructor
  intro clause hclause
  rw [masterFormula, List.mem_append] at hclause
  rcases hclause with hbase | hcanonical
  · exact (masterBaseFormula_satisfied hC hR hN hSparse hBalanced).property
      clause hbase
  · exact (canonicalRowFormula_satisfied Q orbit hrow).property clause hcanonical

end Erdos97Octagon.RawIncidence
