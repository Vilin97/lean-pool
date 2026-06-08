/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000Relaxation

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Distributed2Coloring.LowerBound.Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var

noncomputable instance : Fintype G := by infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev LabelTriple := N1000000Witness.LabelTriple

instance : NeZero n := ⟨by
  -- `n = 10^6`.
  decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def symOfNat (k : Nat) : SymN :=
  Fin.ofNat n k

lemma symOfNat_injective_of_lt {a b : Nat} (ha : a < n) (hb : b < n) :
    symOfNat a = symOfNat b → a = b := by
  intro hab
  have hval : a % n = b % n := by
    simpa [symOfNat] using congrArg Fin.val hab
  have ha' : a % n = a := Nat.mod_eq_of_lt ha
  have hb' : b % n = b := Nat.mod_eq_of_lt hb
  simpa [ha', hb'] using hval

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGet (t : LabelTriple) (i : Fin 3) : SymN :=
  match i.1 with
  | 0 => symOfNat t.1
  | 1 => symOfNat t.2.1
  | _ => symOfNat t.2.2

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def tupleOfLabels (t : LabelTriple) : Tuple 3 n :=
  fun i => labelGet t i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGetNat (t : LabelTriple) (i : Fin 3) : Nat :=
  match i.1 with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

lemma labelGet_eq_symOfNat_labelGetNat (t : LabelTriple) (i : Fin 3) :
    labelGet t i = symOfNat (labelGetNat t i) := by
  fin_cases i <;> rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsDistinct (t : LabelTriple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance (t : LabelTriple) : Decidable (LabelsDistinct t) := by
  unfold LabelsDistinct
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsInRange (t : LabelTriple) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

instance (t : LabelTriple) : Decidable (LabelsInRange t) := by
  unfold LabelsInRange
  infer_instance

lemma labelGetNat_lt (t : LabelTriple) (hr : LabelsInRange (t := t)) (i : Fin 3) :
    labelGetNat t i < n := by
  fin_cases i
  · simpa [labelGetNat] using hr.1
  · simpa [labelGetNat] using hr.2.1
  · simpa [labelGetNat] using hr.2.2

lemma labelGetNat_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t) :
    Function.Injective (labelGetNat t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h.1 (by simpa [labelGetNat] using hij)).elim
  · exact (h.2.1 (by simpa [labelGetNat] using hij)).elim
  · have hij' : t.2.1 = t.1 := by
      simpa [labelGetNat] using hij
    exact (h.1 hij'.symm).elim
  · rfl
  · exact (h.2.2 (by simpa [labelGetNat] using hij)).elim
  · have hij' : t.2.2 = t.1 := by
      simpa [labelGetNat] using hij
    exact (h.2.1 hij'.symm).elim
  · have hij' : t.2.2 = t.2.1 := by
      simpa [labelGetNat] using hij
    exact (h.2.2 hij'.symm).elim
  · rfl

lemma tupleOfLabels_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t)
    (hr : LabelsInRange (t := t)) :
    Function.Injective (tupleOfLabels t) := by
  intro i j hij
  have hi : labelGetNat t i < n := labelGetNat_lt (t := t) hr i
  have hj : labelGetNat t j < n := labelGetNat_lt (t := t) hr j
  have hijSym : symOfNat (labelGetNat t i) = symOfNat (labelGetNat t j) := by
    simpa [tupleOfLabels, labelGet_eq_symOfNat_labelGetNat] using hij
  have hijNat : labelGetNat t i = labelGetNat t j :=
    symOfNat_injective_of_lt (a := labelGetNat t i) (b := labelGetNat t j) hi hj hijSym
  exact labelGetNat_injective_of_labelsDistinct (t := t) h hijNat

theorem varRepU_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepU[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

theorem varRepV_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepV[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepUAt (i : Var) : LabelTriple :=
  varRepU[i.1]!

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepVAt (i : Var) : LabelTriple :=
  varRepV[i.1]!

theorem varRepUAt_labelsDistinct (i : Var) : LabelsDistinct (varRepUAt i) := by
  fin_cases i <;> decide

theorem varRepVAt_labelsDistinct (i : Var) : LabelsDistinct (varRepVAt i) := by
  fin_cases i <;> decide

theorem varRepUAt_labelsInRange (i : Var) : LabelsInRange (varRepUAt i) := by
  fin_cases i <;> decide

theorem varRepVAt_labelsInRange (i : Var) : LabelsInRange (varRepVAt i) := by
  fin_cases i <;> decide

theorem varRepUAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepUAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

theorem varRepVAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepVAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexU (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepUAt i), varRepUAt_injective i⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexV (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepVAt i), varRepVAt_injective i⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def xFromColoring (f : Coloring n) : Var → Q :=
  fun i => corrAvg (n := n) f (varRepVertexU i) (varRepVertexV i)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeVarVar : Var :=
  ⟨edgeVar, by decide⟩

-- A concrete representative edge `((3,0,1) -> (0,1,2))`, encoded as a 4-tuple `(3,0,1,2)`.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRepTuple : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => symOfNat 3
    | 1 => symOfNat 0
    | 2 => symOfNat 1
    | _ => symOfNat 2

lemma edgeRepTuple_injective : Function.Injective edgeRepTuple := by
  intro i j hij
  have hmod0 : (0 : Nat) % n = 0 := Nat.mod_eq_of_lt (by decide : (0 : Nat) < n)
  have hmod1 : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by decide : (1 : Nat) < n)
  have hmod2 : (2 : Nat) % n = 2 := Nat.mod_eq_of_lt (by decide : (2 : Nat) < n)
  have hmod3 : (3 : Nat) % n = 3 := Nat.mod_eq_of_lt (by decide : (3 : Nat) < n)
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    have hval := congrArg Fin.val hij
    have : False := by
      -- Reduce to an absurd equality between distinct numerals.
      simp [edgeRepTuple, symOfNat, hmod0, hmod1, hmod2, hmod3] at hval
    cases this

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRep : Edge n :=
  ⟨edgeRepTuple, edgeRepTuple_injective⟩

theorem edgeRep_src : Edge.src edgeRep = varRepVertexV edgeVarVar := by
  have hV : varRepVAt edgeVarVar = (3, 0, 1) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.src, Edge.srcIndex, edgeRep, edgeRepTuple, varRepVertexV, varRepVAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hV]

theorem edgeRep_dst : Edge.dst edgeRep = varRepVertexU edgeVarVar := by
  have hU : varRepUAt edgeVarVar = (0, 1, 2) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.dst, Edge.dstIndex, edgeRep, edgeRepTuple, varRepVertexU, varRepUAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hU]

/-!
This file currently defines the reduced orbit variables `xFromColoring` and the concrete edge
representative `edgeRep`.  The remaining objective link

`xEdge (xFromColoring f) = edgeCorrelation f`

is deferred to a separate module (it uses orbit-stabilizer / pretransitivity for the action of
`Sym(n)` on `Edge n`).
-/

end N1000000Relaxation

end Distributed2Coloring.LowerBound
