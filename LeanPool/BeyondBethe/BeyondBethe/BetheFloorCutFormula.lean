/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraph

/-!
# Coordinate formula for Bethe floor-cut normals

The machine implementation uses the four signed indicators obtained by
pulling one recovered matrix coordinate back to the flattened upper-left
block.  This file proves that direct formula equal to `betheFloorCutNormal`,
separately from any encoding or iteration argument.
-/

@[expose] public section

namespace BeyondBethe

/-- Base-coordinate coefficient of the lower-floor cut at recovered entry
`(i,j)`.  It is the negative of the four-corner affine pullback. -/
def explicitBetheFloorCutBaseEntry {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) : ℚ :=
  -(if a.castSucc = i ∧ b.castSucc = j then 1 else 0) +
    (if a.castSucc = i ∧ Fin.last m = j then 1 else 0) +
    (if Fin.last m = i ∧ b.castSucc = j then 1 else 0) -
    (if Fin.last m = i ∧ Fin.last m = j then 1 else 0)

/-- Full epigraph-vector formula, with zero in the last coordinate. -/
def explicitBetheFloorCutNormal {m : ℕ} (i j : Fin (m + 1)) :
    Fin (m * m + 1) → ℚ :=
  Fin.snoc (fun k ↦
    let ab := finProdFinEquiv.symm k
    explicitBetheFloorCutBaseEntry i j ab.1 ab.2) 0

theorem neg_affinePullback_entryCovector {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) :
    -affinePullbackGradient (matrixEntryCovector i j) a b =
      explicitBetheFloorCutBaseEntry i j a b := by
  simp only [affinePullbackGradient, matrixEntryCovector,
    explicitBetheFloorCutBaseEntry]
  by_cases hab : a.castSucc = i ∧ b.castSucc = j <;>
    by_cases haLast : a.castSucc = i ∧ Fin.last m = j <;>
    by_cases hLastB : Fin.last m = i ∧ b.castSucc = j <;>
    by_cases hLastLast : Fin.last m = i ∧ Fin.last m = j <;>
    simp [hab, haLast, hLastB, hLastLast] <;> ring

theorem explicitBetheFloorCutNormal_eq {m : ℕ}
    (i j : Fin (m + 1)) :
    explicitBetheFloorCutNormal i j = betheFloorCutNormal i j := by
  ext k
  refine Fin.lastCases ?_ (fun k ↦ ?_) k
  · simp [explicitBetheFloorCutNormal, betheFloorCutNormal]
  · rw [betheFloorCutNormal_castSucc]
    simp only [explicitBetheFloorCutNormal, Fin.snoc_castSucc,
      squareMatrixToVector]
    exact (neg_affinePullback_entryCovector i j
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).symm

@[simp] theorem explicitBetheFloorCutBaseEntry_upperLeft {m : ℕ}
    (i j a b : Fin m) :
    explicitBetheFloorCutBaseEntry i.castSucc j.castSucc a b =
      if a = i ∧ b = j then -1 else 0 := by
  have hi : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have hj : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  by_cases hai : a = i <;> by_cases hbj : b = j <;>
    simp [explicitBetheFloorCutBaseEntry, hai, hbj, hi, hj]

@[simp] theorem explicitBetheFloorCutBaseEntry_lastColumn {m : ℕ}
    (i a b : Fin m) :
    explicitBetheFloorCutBaseEntry i.castSucc (Fin.last m) a b =
      if a = i then 1 else 0 := by
  have hi : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have hb : b.castSucc ≠ Fin.last m := Fin.castSucc_ne_last b
  by_cases hai : a = i <;>
    simp [explicitBetheFloorCutBaseEntry, hai, hi, hb]

@[simp] theorem explicitBetheFloorCutBaseEntry_lastRow {m : ℕ}
    (j a b : Fin m) :
    explicitBetheFloorCutBaseEntry (Fin.last m) j.castSucc a b =
      if b = j then 1 else 0 := by
  have hj : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  have ha : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
  by_cases hbj : b = j <;>
    simp [explicitBetheFloorCutBaseEntry, hbj, hj, ha]

@[simp] theorem explicitBetheFloorCutBaseEntry_corner {m : ℕ}
    (a b : Fin m) :
    explicitBetheFloorCutBaseEntry (Fin.last m) (Fin.last m) a b = -1 := by
  have ha : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
  have hb : b.castSucc ≠ Fin.last m := Fin.castSucc_ne_last b
  simp [explicitBetheFloorCutBaseEntry, ha, hb]

end BeyondBethe
