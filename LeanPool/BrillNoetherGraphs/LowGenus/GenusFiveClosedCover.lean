/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCoverData
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpecCensus

/-!
# Exact affine covers for closed genus-five rows

This module joins two existing public trust boundaries.  A `CoordinateCell`
is an ordinary closed explicit-potential certificate whose coordinates are
the twelve slot lengths.  `AffineCover` selects one such cell, and the
closed-face census turns its local scripts into `BNExists` on the canonical
forest contraction.  The final adapter recovers the diagnostic AR pencil.

Generated row modules contain data only: certificates, cones, and one checked
cover tree.  All graph and divisor semantics are proved here once.
-/

namespace AtanasovRanganathan.GenusFiveClosedCover

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.ExplicitPotential.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations

variable {n p : ℕ}

/-- Extensionality for degenerate specifications; all omitted fields are
proofs of propositions. -/
theorem degSpec_ext
    {left right : Certificate.DegenerateSpec.DegSpec n p}
    (hCore : left.core = right.core)
    (hLength : left.length = right.length)
    (hRep : left.rep = right.rep) : left = right := by
  obtain ⟨leftCore, leftLength, _, leftRep, _, _, _, _⟩ := left
  obtain ⟨rightCore, rightLength, _, rightRep, _, _, _, _⟩ := right
  simp only at hCore hLength hRep
  subst rightCore
  subst rightLength
  subst rightRep
  rfl

/-- The affine coordinate reading the length of slot `edge`. -/
def coordinateForm (edge : Fin p) : ExplicitPotential.AffineForm p where
  fixedValue := 0
  coefficient := fun coordinate => if coordinate = edge then 1 else 0

@[simp] theorem coordinateForm_eval (edge : Fin p) (point : Fin p → ℤ) :
    (coordinateForm edge).eval point = point edge := by
  simp [coordinateForm, Certificate.AffineCover.AffineForm.eval]

/-- Passive data for one cone of a closed row cover. -/
structure CoordinateCell (core : ExplicitPotential.Core n p) where
  divisor : Fin n → ℤ
  witness : Fin n → AnchorWitness p n p
  cone : List (ExplicitPotential.AffineForm p)

/-- Interpret a cell as the standard explicit-potential certificate. -/
def CoordinateCell.certificate {core : ExplicitPotential.Core n p}
    (cell : CoordinateCell core) : Certificate p n p where
  core := core
  segment := coordinateForm
  divisor := cell.divisor
  witness := cell.witness
  cone := cell.cone

@[simp] theorem CoordinateCell.certificate_cone
    {core : ExplicitPotential.Core n p} (cell : CoordinateCell core) :
    cell.certificate.cone = cell.cone := rfl

/-- The length point used by a coordinate cell. -/
def lengthPoint (length : Fin p → ℕ) : Fin p → ℤ :=
  fun edge => length edge

@[simp] theorem coordinateCell_segmentNat
    {core : ExplicitPotential.Core n p} (cell : CoordinateCell core)
    (length : Fin p → ℕ) (edge : Fin p) :
    cell.certificate.segmentNat (lengthPoint length) edge = length edge := by
  simp [CoordinateCell.certificate, lengthPoint,
    ExplicitPotential.Certificate.segmentNat]

@[simp] theorem coordinateCell_zeroSlots
    {core : ExplicitPotential.Core n p} (cell : CoordinateCell core)
    (length : Fin p → ℕ) :
    cell.certificate.zeroSlots (lengthPoint length) = zeroSlots length := by
  ext edge
  simp [ExplicitPotential.Certificate.mem_zeroSlots,
    Configurations.mem_zeroSlots]

/-- One accepted coordinate cell proves the semantic row statement on the
canonical closed face. -/
theorem CoordinateCell.bnExists_faceSpec
    {core : ExplicitPotential.Core n p} (core_nonempty : 0 < n)
    (hCoreConnected : core.Connected) (cell : CoordinateCell core)
    (hValid : cell.certificate.ValidClosed 4)
    (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (notLoopy : ¬ IsLoopy core (zeroSlots length))
    (hCone : ExplicitPotential.FormsHold cell.cone (lengthPoint length)) :
    BNExists (faceSpec core core_nonempty length forest notLoopy).graph 1 4 := by
  have hForest' : IsForest cell.certificate.core
      (cell.certificate.zeroSlots (lengthPoint length)) := by
    change IsForest core (cell.certificate.zeroSlots (lengthPoint length))
    simpa using forest
  have hNotLoopy' : ¬ IsLoopy cell.certificate.core
      (cell.certificate.zeroSlots (lengthPoint length)) := by
    change ¬ IsLoopy core (cell.certificate.zeroSlots (lengthPoint length))
    simpa using notLoopy
  have hExistence :=
    cell.certificate.bnExists_on_degenerate_subdivision_of_validClosed_of_forestCensus
      (lengthPoint length) core_nonempty 4 hValid (by simpa using hCone)
      hForest' hNotLoopy' hCoreConnected
  let certificateSpec := cell.certificate.degenerateSpec
    (lengthPoint length) core_nonempty
    (cell.certificate.censusRep (lengthPoint length))
    (cell.certificate.censusRep_idem (lengthPoint length))
    (cell.certificate.censusRep_zero (lengthPoint length))
    (cell.certificate.censusRep_loopless (lengthPoint length) hNotLoopy')
    (cell.certificate.censusRep_forest (lengthPoint length) hForest')
  have hSpec : certificateSpec =
      faceSpec core core_nonempty length forest notLoopy := by
    apply degSpec_ext
    · rfl
    · funext edge
      exact coordinateCell_segmentNat cell length edge
    · change compFold core
          (cell.certificate.zeroSlots (lengthPoint length)) =
        compFold core (zeroSlots length)
      exact congrArg (compFold core)
        (coordinateCell_zeroSlots cell length)
  change BNExists certificateSpec.graph 1 4 at hExistence
  rw [hSpec] at hExistence
  exact hExistence

/-- A list of passive cells advertises exactly their certificate cones. -/
def cones {core : ExplicitPotential.Core n p}
    (cells : List (CoordinateCell core)) :
    List (List (ExplicitPotential.AffineForm p)) :=
  cells.map CoordinateCell.cone

/-! ## A compact split tree for certificate cells -/

/-- Proof-producing decision tree used by the fixed-row emitter.  A leaf names
one cell and carries, for every inequality in its cone, a Farkas contradiction
from the active chamber together with the violation of that inequality. -/
inductive CellTree (p : ℕ) where
  | cell (index : ℕ) (receipts : List Certificate.AffineCover.FarkasData)
  | absurd (receipt : Certificate.AffineCover.FarkasData)
  | split (form : ExplicitPotential.AffineForm p)
      (nonnegative negative : CellTree p)

namespace CellTree

def coneAt {core : ExplicitPotential.Core n p}
    (cells : List (CoordinateCell core)) (index : ℕ) :
    List (ExplicitPotential.AffineForm p) :=
  (cells.getD index
    { divisor := fun _ => 0
      witness := fun _ =>
        { alpha := fun _ => 0
          beta := fun _ => 0
          potential := fun _ => 0 }
      cone := [] }).cone

def Valid {core : ExplicitPotential.Core n p}
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) : CellTree p → Prop
  | .cell index receipts =>
      index < cells.length ∧
      receipts.length = (coneAt cells index).length ∧
      ∀ i : Fin (coneAt cells index).length,
        (receipts.getD i.val { terms := [] }).Valid
          (active ++ [Certificate.AffineCover.AffineForm.violation
            ((coneAt cells index).get i)])
  | .absurd receipt => receipt.Valid active
  | .split form nonnegative negative =>
      nonnegative.Valid cells (active ++ [form]) ∧
      negative.Valid cells
        (active ++ [Certificate.AffineCover.AffineForm.violation form])

def check {core : ExplicitPotential.Core n p}
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) : CellTree p → Bool
  | .cell index receipts =>
      decide (index < cells.length) &&
      decide (receipts.length = (coneAt cells index).length) &&
      ExplicitPotential.allFin (fun i : Fin (coneAt cells index).length =>
        (receipts.getD i.val { terms := [] }).check
          (active ++ [Certificate.AffineCover.AffineForm.violation
            ((coneAt cells index).get i)]))
  | .absurd receipt => receipt.check active
  | .split form nonnegative negative =>
      nonnegative.check cells (active ++ [form]) &&
      negative.check cells
        (active ++ [Certificate.AffineCover.AffineForm.violation form])

@[simp] theorem check_eq_true_iff
    {core : ExplicitPotential.Core n p}
    (tree : CellTree p) (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) :
    tree.check cells active = true ↔ tree.Valid cells active := by
  induction tree generalizing active with
  | cell index receipts =>
      simp [check, Valid, and_assoc]
  | absurd receipt => simp [check, Valid]
  | split form nonnegative negative ihNonnegative ihNegative =>
      simp [check, Valid, ihNonnegative, ihNegative]

theorem coveredCell_of_valid
    {core : ExplicitPotential.Core n p}
    (tree : CellTree p) (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p))
    (hValid : tree.Valid cells active)
    (point : Fin p → ℤ) (hActive : ExplicitPotential.FormsHold active point) :
    ∃ cell ∈ cells, ExplicitPotential.FormsHold cell.cone point := by
  induction tree generalizing active with
  | cell index receipts =>
      obtain ⟨hIndex, hLength, hReceipts⟩ := hValid
      let cell := cells[index]
      refine ⟨cell, List.getElem_mem hIndex, ?_⟩
      intro form hForm
      obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hForm
      have hConeAt : coneAt cells index = cell.cone := by
        unfold coneAt
        rw [List.getD_eq_getElem _ _ hIndex]
      have hiReceipts : i < receipts.length := by
        rw [hLength, hConeAt]
        exact hi
      let receipt := receipts[i]
      have hReceipt : receipt.Valid
          (active ++ [Certificate.AffineCover.AffineForm.violation form]) := by
        have := hReceipts ⟨i, by simpa [hConeAt] using hi⟩
        rw [List.getD_eq_getElem _ _ hiReceipts] at this
        simpa [receipt, hConeAt, hEq] using this
      by_contra hFails
      apply receipt.not_formsHold_of_valid _ hReceipt
      intro row hRow
      simp only [List.mem_append, List.mem_singleton] at hRow
      rcases hRow with hRow | rfl
      · exact hActive row hRow
      · rw [Certificate.AffineCover.AffineForm.holds_violation_iff_not]
        exact hFails
  | absurd receipt =>
      exact (receipt.not_formsHold_of_valid active hValid hActive).elim
  | split form nonnegative negative ihNonnegative ihNegative =>
      by_cases hForm : 0 ≤ form.eval point
      · exact ihNonnegative (active ++ [form]) hValid.1 (by
          intro row hRow
          simp only [List.mem_append, List.mem_singleton] at hRow
          rcases hRow with hRow | rfl
          · exact hActive row hRow
          · exact hForm)
      · exact ihNegative
          (active ++ [Certificate.AffineCover.AffineForm.violation form])
          hValid.2 (by
            intro row hRow
            simp only [List.mem_append, List.mem_singleton] at hRow
            rcases hRow with hRow | rfl
            · exact hActive row hRow
            · rw [Certificate.AffineCover.AffineForm.holds_violation_iff_not]
              exact hForm)

end CellTree

/-! The generated row proofs can have many repeated split forms and Farkas
receipts.  `CompactCellTree` stores indices into shared tables, keeping the
checked source proportional to the genuinely distinct arithmetic data. -/

inductive CompactCellTree where
  | cell (index : ℕ) (receipts : List ℕ)
  | absurd (receipt : ℕ)
  | split (form : ℕ) (nonnegative negative : CompactCellTree)

namespace CompactCellTree

def decode {p : ℕ}
    (forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData) :
    CompactCellTree → CellTree p
  | .cell index indices =>
      .cell index (indices.map fun i => receipts.getD i { terms := [] })
  | .absurd index => .absurd (receipts.getD index { terms := [] })
  | .split index nonnegative negative =>
      .split (forms.getD index 0)
        (nonnegative.decode forms receipts) (negative.decode forms receipts)

def check {core : ExplicitPotential.Core n p}
    (tree : CompactCellTree) (forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData)
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) : Bool :=
  (tree.decode forms receipts).check cells active

@[simp] theorem check_split {core : ExplicitPotential.Core n p}
    (index : ℕ) (nonnegative negative : CompactCellTree)
    (forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData)
    (cells : List (CoordinateCell core))
    (active : List (ExplicitPotential.AffineForm p)) :
    (CompactCellTree.split index nonnegative negative).check
        forms receipts cells active =
      (nonnegative.check forms receipts cells
          (active ++ [forms.getD index 0]) &&
        negative.check forms receipts cells
          (active ++ [Certificate.AffineCover.AffineForm.violation
            (forms.getD index 0)])) := rfl

end CompactCellTree

/-- Checked split-tree form of `closedConstruction_of_cover`. -/
theorem closedConstruction_of_cellTree
    {core : ExplicitPotential.Core n p} (core_nonempty : 0 < n)
    (hCoreConnected : core.Connected)
    (cells : List (CoordinateCell core))
    (base : List (ExplicitPotential.AffineForm p))
    (tree : CellTree p)
    (hBase : ∀ length : Fin p → ℕ,
      ExplicitPotential.FormsHold base (lengthPoint length))
    (hCells : ∀ cell ∈ cells, cell.certificate.ValidClosed 4)
    (hCheck : tree.check cells base = true) :
    ClosedSubdivisionDharConstruction core core_nonempty := by
  intro length forest notLoopy
  obtain ⟨cell, hCell, hCone⟩ := tree.coveredCell_of_valid cells base
    ((tree.check_eq_true_iff cells base).mp hCheck)
    (lengthPoint length) (hBase length)
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (cell.bnExists_faceSpec core_nonempty hCoreConnected (hCells cell hCell)
      length forest notLoopy hCone)

/-- Table-compressed checked split-tree form of
`closedConstruction_of_cellTree`. -/
theorem closedConstruction_of_compactCellTree
    {core : ExplicitPotential.Core n p} (core_nonempty : 0 < n)
    (hCoreConnected : core.Connected)
    (cells : List (CoordinateCell core))
    (base forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData)
    (tree : CompactCellTree)
    (hBase : ∀ length : Fin p → ℕ,
      ExplicitPotential.FormsHold base (lengthPoint length))
    (hCells : ∀ cell ∈ cells, cell.certificate.ValidClosed 4)
    (hCheck : tree.check forms receipts cells base = true) :
    ClosedSubdivisionDharConstruction core core_nonempty :=
  closedConstruction_of_cellTree core_nonempty hCoreConnected cells base
    (tree.decode forms receipts) hBase hCells hCheck

/-- **Chamber form of `closedConstruction_of_compactCellTree`.**

The checked data only has to cover the sub-cone cut out by `base`, and the
conclusion is the pencil at a single length vector lying in that sub-cone.
This is exactly the shape of the `chamber` argument of
`ClosedOrbit.closedConstruction_of_chamber`, so a row whose exact cover is too
large to replay on the whole orthant may be proved on a fundamental domain for
the core's symmetry group and transported to the rest.

Nothing is weakened: `base` is still the active row list at the root of the
tree, so every Farkas receipt is replayed against exactly the hypotheses the
caller supplies pointwise through `hHold`. -/
theorem chamberPencil_of_compactCellTree
    {core : ExplicitPotential.Core n p} (core_nonempty : 0 < n)
    (hCoreConnected : core.Connected)
    (cells : List (CoordinateCell core))
    (base forms : List (ExplicitPotential.AffineForm p))
    (receipts : List Certificate.AffineCover.FarkasData)
    (tree : CompactCellTree)
    (hCells : ∀ cell ∈ cells, cell.certificate.ValidClosed 4)
    (hCheck : tree.check forms receipts cells base = true)
    (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (notLoopy : ¬ IsLoopy core (zeroSlots length))
    (hHold : ExplicitPotential.FormsHold base (lengthPoint length)) :
    Nonempty (DegreeFourDharPencil
      (faceSpec core core_nonempty length forest notLoopy).graph) := by
  obtain ⟨cell, hCell, hCone⟩ :=
    (tree.decode forms receipts).coveredCell_of_valid cells base
      (((tree.decode forms receipts).check_eq_true_iff cells base).mp hCheck)
      (lengthPoint length) hHold
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (cell.bnExists_faceSpec core_nonempty hCoreConnected (hCells cell hCell)
      length forest notLoopy hCone)

/-- A checked affine cover whose every cell is valid gives the full closed AR
construction. -/
theorem closedConstruction_of_cover
    {core : ExplicitPotential.Core n p} (core_nonempty : 0 < n)
    (hCoreConnected : core.Connected)
    (cells : List (CoordinateCell core))
    (base : List (ExplicitPotential.AffineForm p))
    (hBase : ∀ length : Fin p → ℕ,
      ExplicitPotential.FormsHold base (lengthPoint length))
    (hCells : ∀ cell ∈ cells, cell.certificate.ValidClosed 4)
    (hCover : Certificate.AffineCover.Covers base (cones cells)) :
    ClosedSubdivisionDharConstruction core core_nonempty := by
  intro length forest notLoopy
  obtain ⟨cone, hConeMem, hCone⟩ := hCover (lengthPoint length) (hBase length)
  obtain ⟨cell, hCellMem, rfl⟩ := List.mem_map.mp hConeMem
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (cell.bnExists_faceSpec core_nonempty hCoreConnected (hCells cell hCellMem)
      length forest notLoopy hCone)

end AtanasovRanganathan.GenusFiveClosedCover
