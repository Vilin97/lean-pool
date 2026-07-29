/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.MasterFormulaData

/-!
# Master coverage formula

The master formula combines the shared semantic clauses used by the certificate
with the needed noncanonical first-row exclusions. It has 64 variables and 3,263 clauses.
-/

namespace Erdos97Octagon.RawIncidence

open LRAT

/-- Shared semantic-clause references retained in the unsatisfiable core. -/
def masterReferences : List ℕ :=
  (List.range 20659).filter fun reference =>
    masterReferenceUsedB reference && (tagOfRef 0 0 reference).validB

/-- The seven canonical first rows viewed as finite sets. -/
def canonicalRows : List (Finset Vertex) :=
  List.ofFn fun orbit : Fin 7 => packedRow (canonicalRowMask orbit)

/-- Noncanonical first-row masks retained in the unsatisfiable core. -/
def masterExcludedRowMasks : List ℕ :=
  (List.range 256).filter fun mask =>
    masterExcludedMaskUsedB mask &&
      decide (packedRow (UInt64.ofNat mask) ∉ canonicalRows)

/-- First rows excluded by the committed unsatisfiable core. -/
def excludedRows : List (Finset Vertex) :=
  masterExcludedRowMasks.map fun mask => packedRow (UInt64.ofNat mask)

/-- A clause which is false precisely when row one equals `row`. -/
def rowExclusionClause (row : Finset Vertex) : Clause :=
  List.ofFn fun target : Vertex =>
    if target ∈ row then
      .negative (varIndex 1 target)
    else
      .positive (varIndex 1 target)

/-- Retained shared clauses. -/
def masterBaseFormula : Formula :=
  masterReferences.map fun reference => (tagOfRef 0 0 reference).toClause

/-- Retained noncanonical first-row exclusion clauses. -/
def canonicalRowFormula : Formula :=
  excludedRows.map rowExclusionClause

/-- The single formula checked by the committed LRAT certificate. -/
def masterFormula : Formula :=
  masterBaseFormula ++ canonicalRowFormula

/-- A valid in-range shared reference gives its clause directly from the master formula. -/
theorem masterBaseClause_proves
    (reference : ℕ) (hrange : decide (reference < 20659) = true)
    (hused : masterReferenceUsedB reference = true)
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
  exact ⟨List.mem_range.mpr (of_decide_eq_true hrange),
    by simpa only [Bool.and_eq_true] using And.intro hused hvalid⟩

/-- A noncanonical in-range row mask gives its exclusion clause from the master formula. -/
theorem canonicalRowClause_proves
    (mask : ℕ) (hrange : decide (mask < 256) = true)
    (hused : masterExcludedMaskUsedB mask = true)
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
  rw [excludedRows, List.mem_map]
  refine ⟨mask, ?_, rfl⟩
  rw [masterExcludedRowMasks, List.mem_filter]
  exact ⟨List.mem_range.mpr (of_decide_eq_true hrange),
    by simpa only [Bool.and_eq_true] using And.intro hused hnoncanonical⟩

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
  have hchecks : masterReferenceUsedB reference = true ∧
      (tagOfRef 0 0 reference).validB = true := by
    simpa only [Bool.and_eq_true] using hparts.2
  exact (tagOfRef 0 0 reference).satisfies hC hR hN hSparse hBalanced
    ((tagOfRef 0 0 reference).valid_of_validB hchecks.2)
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
  rw [excludedRows, List.mem_map] at hrowExcluded
  obtain ⟨mask, hmask, rfl⟩ := hrowExcluded
  apply rowExclusionClause_satisfied
  intro hequal
  have hcanonical : packedRow (UInt64.ofNat mask) ∈ canonicalRows := by
    rw [← hequal, hrow]
    unfold canonicalRows
    rw [List.mem_ofFn]
    exact ⟨orbit, rfl⟩
  have hmaskParts := List.mem_filter.mp hmask
  have hmaskChecks : masterExcludedMaskUsedB mask = true ∧
      decide (packedRow (UInt64.ofNat mask) ∉ canonicalRows) = true := by
    simpa only [Bool.and_eq_true] using hmaskParts.2
  have hnotCanonical : packedRow (UInt64.ofNat mask) ∉ canonicalRows :=
    of_decide_eq_true hmaskChecks.2
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
