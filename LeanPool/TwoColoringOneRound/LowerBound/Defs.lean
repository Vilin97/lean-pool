/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# LeanPool.TwoColoringOneRound.LowerBound.Defs
-/

namespace Distributed2Coloring.LowerBound

open scoped BigOperators

/-- Symbols. -/
abbrev Sym (n : Nat) := Fin n

/-- Ordered `k`-tuples of symbols. -/
abbrev Tuple (k n : Nat) := Fin k → Sym n

/-- Vertices are injective triples of symbols. -/
abbrev Vertex (n : Nat) := { v : Tuple 3 n // Function.Injective v }

/-- Edges are injective quadruples of symbols, encoding `(a,b,c) → (b,c,d)`. -/
abbrev Edge (n : Nat) := { e : Tuple 4 n // Function.Injective e }

namespace Vertex

/-- First coordinate `a` of a vertex `(a,b,c)`. -/
def a {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨0, by decide⟩
/-- Second coordinate `b` of a vertex `(a,b,c)`. -/
def b {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨1, by decide⟩
/-- Third coordinate `c` of a vertex `(a,b,c)`. -/
def c {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨2, by decide⟩

end Vertex

namespace Edge

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def srcIndex (i : Fin 3) : Fin 4 :=
  ⟨i.1, Nat.lt_trans i.2 (by decide)⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def dstIndex (i : Fin 3) : Fin 4 :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp] lemma srcIndex_zero : srcIndex (0 : Fin 3) = (0 : Fin 4) := by
  ext
  rfl

@[simp] lemma srcIndex_one : srcIndex (1 : Fin 3) = (1 : Fin 4) := by
  ext
  rfl

@[simp] lemma srcIndex_two : srcIndex (2 : Fin 3) = (2 : Fin 4) := by
  ext
  rfl

@[simp] lemma dstIndex_zero : dstIndex (0 : Fin 3) = (1 : Fin 4) := by
  ext
  rfl

@[simp] lemma dstIndex_one : dstIndex (1 : Fin 3) = (2 : Fin 4) := by
  ext
  rfl

@[simp] lemma dstIndex_two : dstIndex (2 : Fin 3) = (3 : Fin 4) := by
  ext
  rfl

/-- Source vertex of an edge `(a,b,c,d)`, i.e. `(a,b,c)`. -/
def src {n : Nat} (e : Edge n) : Vertex n :=
  ⟨fun i => e.1 (srcIndex i), by
    intro i j hij
    have h4 : srcIndex i = srcIndex j := e.2 hij
    apply Fin.ext
    simpa [srcIndex] using congrArg Fin.val h4⟩

/-- Target vertex of an edge `(a,b,c,d)`, i.e. `(b,c,d)`. -/
def dst {n : Nat} (e : Edge n) : Vertex n :=
  ⟨fun i => e.1 (dstIndex i), by
    intro i j hij
    have h4 : dstIndex i = dstIndex j := e.2 hij
    apply Fin.ext
    have hval : (i.1 + 1) = (j.1 + 1) := by
      simpa [dstIndex] using congrArg Fin.val h4
    exact Nat.succ.inj hval⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monochromatic {n : Nat} (f : Vertex n → Bool) (e : Edge n) : Prop :=
  f (src e) = f (dst e)

instance {n : Nat} (f : Vertex n → Bool) (e : Edge n) : Decidable (monochromatic f e) := by
  dsimp [monochromatic]
  infer_instance

end Edge

/-- A `2`-coloring of the vertices. -/
abbrev Coloring (n : Nat) := Vertex n → Bool

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCount (n : Nat) : Nat := Fintype.card (Edge n)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monoEdges {n : Nat} (f : Coloring n) : Finset (Edge n) :=
  (Finset.univ : Finset (Edge n)).filter (Edge.monochromatic f)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monoCount {n : Nat} (f : Coloring n) : Nat :=
  (monoEdges f).card

/-- Fraction of monochromatic directed edges under `f`. -/
def monoFraction {n : Nat} (f : Coloring n) : ℚ :=
  (monoCount f : ℚ) / (edgeCount n : ℚ)

/-- Convert a coloring to a sign labeling `±1`. -/
def signOfColoring {n : Nat} (f : Coloring n) : Vertex n → Int :=
  fun v => if f v then (-1) else (1)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCorrSum {n : Nat} (f : Coloring n) : Int :=
  (Finset.univ : Finset (Edge n)).sum fun e =>
    (signOfColoring f (Edge.src e)) * (signOfColoring f (Edge.dst e))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCorrelation {n : Nat} (f : Coloring n) : ℚ :=
  (edgeCorrSum f : ℚ) / (edgeCount n : ℚ)

lemma signOfColoring_sq {n : Nat} (f : Coloring n) (v : Vertex n) :
    (signOfColoring f v) * (signOfColoring f v) = 1 := by
  unfold signOfColoring
  by_cases h : f v <;> simp [h]

/-- On an edge, being monochromatic is equivalent to having product `+1` in `±1`. -/
lemma mono_iff_sign_mul_eq_one {n : Nat} (f : Coloring n) (e : Edge n) :
    Edge.monochromatic f e ↔
      (signOfColoring f (Edge.src e)) * (signOfColoring f (Edge.dst e)) = 1 := by
  unfold Edge.monochromatic signOfColoring
  by_cases hs : f (Edge.src e) <;> by_cases ht : f (Edge.dst e) <;> simp [hs, ht]

lemma monoIndicator_eq_one_add_sign_mul_div_two {n : Nat} (f : Coloring n) (e : Edge n) :
    (if Edge.monochromatic f e then (1 : ℚ) else 0)
      = ((1 : ℚ) + (signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int)) / 2 := by
  unfold Edge.monochromatic signOfColoring
  by_cases hs : f (Edge.src e) <;> by_cases ht : f (Edge.dst e) <;> simp [hs, ht]

lemma monoFraction_eq_one_add_edgeCorrelation_div_two {n : Nat} (f : Coloring n)
    (hE : edgeCount n ≠ 0) :
    monoFraction f = ((1 : ℚ) + edgeCorrelation f) / 2 := by
  classical
  have hE' : (edgeCount n : ℚ) ≠ 0 := by
    exact_mod_cast hE
  let z : Edge n → ℚ := fun e =>
    ((signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int) : ℚ)
  -- Express `monoCount` as a sum of indicators using `Finset.sum_boole`.
  have hcount :
      (monoCount f : ℚ)
        = (Finset.univ : Finset (Edge n)).sum (fun e =>
            if Edge.monochromatic f e then (1 : ℚ) else 0) := by
    simp [monoCount, monoEdges]
  -- Rewrite each indicator as `(1 + sign_mul)/2` and sum.
  calc
    monoFraction f
        = (monoCount f : ℚ) / (edgeCount n : ℚ) := by rfl
    _ = ((Finset.univ : Finset (Edge n)).sum (fun e =>
          if Edge.monochromatic f e then (1 : ℚ) else 0)) / (edgeCount n : ℚ) := by
          simp [hcount]
    _ = ((Finset.univ : Finset (Edge n)).sum (fun e =>
          ((1 : ℚ) + z e) / 2))
          / (edgeCount n : ℚ) := by
          refine congrArg (fun z => z / (edgeCount n : ℚ)) ?_
          refine Finset.sum_congr rfl ?_
          intro e _
          simpa [z] using (monoIndicator_eq_one_add_sign_mul_div_two (n := n) f e)
    _ = ((((Finset.univ : Finset (Edge n)).sum (fun _e => (1 : ℚ))
            + (Finset.univ : Finset (Edge n)).sum z) / 2))
          / (edgeCount n : ℚ) := by
          -- Linearity: pull out the factor `1/2`, then distribute the sum across addition.
          have hlin :
              (Finset.univ : Finset (Edge n)).sum (fun e => ((1 : ℚ) + z e) / 2)
                = ((Finset.univ : Finset (Edge n)).sum (fun e => (1 : ℚ) + z e)) / 2 := by
            -- `x/2 = x * (2⁻¹)`, and `sum` commutes with right multiplication by a constant.
            simp [div_eq_mul_inv, Finset.sum_mul]
          -- Now distribute the sum across addition.
          simp [hlin, Finset.sum_add_distrib]
    _ = (((edgeCount n : ℚ) + (edgeCorrSum f : ℚ)) / 2) / (edgeCount n : ℚ) := by
          simp [edgeCount, edgeCorrSum, z]
    _ = ((1 : ℚ) + (edgeCorrSum f : ℚ) / (edgeCount n : ℚ)) / 2 := by
          -- algebra in a field; requires `edgeCount n ≠ 0`
          field_simp [hE', add_comm, add_left_comm, add_assoc, mul_add, add_mul]
    _ = ((1 : ℚ) + edgeCorrelation f) / 2 := by
          simp [edgeCorrelation]

end Distributed2Coloring.LowerBound
