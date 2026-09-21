/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel

/-!
# Finite polyhedral cell data

This module records a finite collection of compact cells by continuous barycentric
parameterizations.  The data are intentionally proof-carrying: later topology uses the
specified face and relative-interior relations rather than an unverified geometric picture.
-/

namespace NRR

open scoped BigOperators

/-- Barycentric coordinates of the standard `d`-simplex. -/
def StandardSimplex (d : ℕ) :=
  {w : Fin (d + 1) → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

namespace StandardSimplex

instance (d : ℕ) : TopologicalSpace (StandardSimplex d) :=
  TopologicalSpace.induced Subtype.val inferInstance

instance (d : ℕ) : CoeFun (StandardSimplex d) (fun _ => Fin (d + 1) → ℝ) :=
  ⟨fun w => w.1⟩

@[simp] theorem nonneg {d : ℕ} (w : StandardSimplex d) (i : Fin (d + 1)) :
    0 ≤ w i :=
  w.2.1 i

@[simp] theorem sum_eq_one {d : ℕ} (w : StandardSimplex d) :
    ∑ i, w i = 1 :=
  w.2.2

/-- The relative interior of the standard simplex. -/
def IsInterior {d : ℕ} (w : StandardSimplex d) : Prop :=
  ∀ i, 0 < w i

end StandardSimplex

/--
A finite cell structure on a topological space.  Each cell is parameterized by a standard
simplex of the declared dimension.  The relation `IsFace a b` means that the cell `a` is a
face of `b`.
-/
structure FiniteCellStructure (X : Type*) [TopologicalSpace X] where
  Cell : Type*
  [cellFintype : Fintype Cell]
  [cellDecidableEq : DecidableEq Cell]
  dim : Cell → ℕ
  param : ∀ c : Cell, StandardSimplex (dim c) → X
  continuous_param : ∀ c, Continuous (param c)
  isCompact_range : ∀ c, IsCompact (Set.range (param c))
  cover : ∀ x : X, ∃ c w, param c w = x
  IsFace : Cell → Cell → Prop
  face_refl : ∀ c, IsFace c c
  face_trans : ∀ {a b c}, IsFace a b → IsFace b c → IsFace a c
  face_dim_le : ∀ {a b}, IsFace a b → dim a ≤ dim b
  face_range_subset : ∀ {a b}, IsFace a b → Set.range (param a) ⊆ Set.range (param b)
  relInterior_disjoint :
    ∀ {a b}, a ≠ b →
      Disjoint
        {x | ∃ w, StandardSimplex.IsInterior w ∧ param a w = x}
        {x | ∃ w, StandardSimplex.IsInterior w ∧ param b w = x}
  relInterior_cover :
    ∀ x : X, ∃ c w, StandardSimplex.IsInterior w ∧ param c w = x

namespace FiniteCellStructure

variable {X : Type*} [TopologicalSpace X]

/-- Carrier of a cell. -/
def carrier (P : FiniteCellStructure X) (c : P.Cell) : Set X :=
  Set.range (P.param c)

/-- Relative interior specified by strictly positive barycentric coordinates. -/
def relInterior (P : FiniteCellStructure X) (c : P.Cell) : Set X :=
  {x | ∃ w, StandardSimplex.IsInterior w ∧ P.param c w = x}

@[simp] theorem mem_carrier_iff (P : FiniteCellStructure X) (c : P.Cell) (x : X) :
    x ∈ P.carrier c ↔ ∃ w, P.param c w = x :=
  Iff.rfl

@[simp] theorem mem_relInterior_iff (P : FiniteCellStructure X) (c : P.Cell) (x : X) :
    x ∈ P.relInterior c ↔
      ∃ w, StandardSimplex.IsInterior w ∧ P.param c w = x :=
  Iff.rfl

 theorem relInterior_subset_carrier (P : FiniteCellStructure X) (c : P.Cell) :
    P.relInterior c ⊆ P.carrier c := by
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, rfl⟩

 theorem isCompact_carrier (P : FiniteCellStructure X) (c : P.Cell) :
    IsCompact (P.carrier c) :=
  P.isCompact_range c

 theorem carrier_cover (P : FiniteCellStructure X) :
    ⋃ c : P.Cell, P.carrier c = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨c, w, rfl⟩ := P.cover x
    exact Set.mem_iUnion.2 ⟨c, ⟨w, rfl⟩⟩

/-- Cells of a fixed dimension. -/
def CellsOfDim (P : FiniteCellStructure X) (d : ℕ) :=
  {c : P.Cell // P.dim c = d}

noncomputable instance (P : FiniteCellStructure X) (d : ℕ) : Fintype (P.CellsOfDim d) := by
  classical
  letI : Fintype P.Cell := P.cellFintype
  exact Fintype.ofFinset (Finset.univ.filter fun c => P.dim c = d) (by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl)

end FiniteCellStructure

end NRR
