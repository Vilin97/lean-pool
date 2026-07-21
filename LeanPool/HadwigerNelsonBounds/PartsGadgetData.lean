/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsCanonicalTriangle

/-! Generated exact combinatorics for the finite second-stage Parts gadget. -/

namespace HadwigerNelsonBounds

/-- Axial coordinates in one of the two triangular-lattice patches. -/
structure PartsGadgetVertex where
  /-- Whether the point lies in the rotated patch. -/ rotated : Bool
  /-- First axial coordinate. -/ q : Int
  /-- Second axial coordinate. -/ r : Int
deriving DecidableEq

/-- Exact descriptor of one of the 73 gadget vertices. -/
def partsGadgetVertex (vertex : Fin 73) : PartsGadgetVertex :=
  match vertex.val with
  | 0 => ⟨false, -3, 0⟩
  | 1 => ⟨false, -3, 1⟩
  | 2 => ⟨false, -3, 2⟩
  | 3 => ⟨false, -3, 3⟩
  | 4 => ⟨false, -2, -1⟩
  | 5 => ⟨false, -2, 0⟩
  | 6 => ⟨false, -2, 1⟩
  | 7 => ⟨false, -2, 2⟩
  | 8 => ⟨false, -2, 3⟩
  | 9 => ⟨false, -1, -2⟩
  | 10 => ⟨false, -1, -1⟩
  | 11 => ⟨false, -1, 0⟩
  | 12 => ⟨false, -1, 1⟩
  | 13 => ⟨false, -1, 2⟩
  | 14 => ⟨false, -1, 3⟩
  | 15 => ⟨false, 0, -3⟩
  | 16 => ⟨false, 0, -2⟩
  | 17 => ⟨false, 0, -1⟩
  | 18 => ⟨false, 0, 0⟩
  | 19 => ⟨false, 0, 1⟩
  | 20 => ⟨false, 0, 2⟩
  | 21 => ⟨false, 0, 3⟩
  | 22 => ⟨false, 1, -3⟩
  | 23 => ⟨false, 1, -2⟩
  | 24 => ⟨false, 1, -1⟩
  | 25 => ⟨false, 1, 0⟩
  | 26 => ⟨false, 1, 1⟩
  | 27 => ⟨false, 1, 2⟩
  | 28 => ⟨false, 2, -3⟩
  | 29 => ⟨false, 2, -2⟩
  | 30 => ⟨false, 2, -1⟩
  | 31 => ⟨false, 2, 0⟩
  | 32 => ⟨false, 2, 1⟩
  | 33 => ⟨false, 3, -3⟩
  | 34 => ⟨false, 3, -2⟩
  | 35 => ⟨false, 3, -1⟩
  | 36 => ⟨false, 3, 0⟩
  | 37 => ⟨true, -3, 0⟩
  | 38 => ⟨true, -3, 1⟩
  | 39 => ⟨true, -3, 2⟩
  | 40 => ⟨true, -3, 3⟩
  | 41 => ⟨true, -2, -1⟩
  | 42 => ⟨true, -2, 0⟩
  | 43 => ⟨true, -2, 1⟩
  | 44 => ⟨true, -2, 2⟩
  | 45 => ⟨true, -2, 3⟩
  | 46 => ⟨true, -1, -2⟩
  | 47 => ⟨true, -1, -1⟩
  | 48 => ⟨true, -1, 0⟩
  | 49 => ⟨true, -1, 1⟩
  | 50 => ⟨true, -1, 2⟩
  | 51 => ⟨true, -1, 3⟩
  | 52 => ⟨true, 0, -3⟩
  | 53 => ⟨true, 0, -2⟩
  | 54 => ⟨true, 0, -1⟩
  | 55 => ⟨true, 0, 1⟩
  | 56 => ⟨true, 0, 2⟩
  | 57 => ⟨true, 0, 3⟩
  | 58 => ⟨true, 1, -3⟩
  | 59 => ⟨true, 1, -2⟩
  | 60 => ⟨true, 1, -1⟩
  | 61 => ⟨true, 1, 0⟩
  | 62 => ⟨true, 1, 1⟩
  | 63 => ⟨true, 1, 2⟩
  | 64 => ⟨true, 2, -3⟩
  | 65 => ⟨true, 2, -2⟩
  | 66 => ⟨true, 2, -1⟩
  | 67 => ⟨true, 2, 0⟩
  | 68 => ⟨true, 2, 1⟩
  | 69 => ⟨true, 3, -3⟩
  | 70 => ⟨true, 3, -2⟩
  | 71 => ⟨true, 3, -1⟩
  | 72 => ⟨true, 3, 0⟩
  | _ => ⟨false, 0, 0⟩

/-- Raw geometric witness for one listed sqrt-three triple. -/
structure PartsGadgetTriangleWitnessData where
  /-- First partner of the rooted triple. -/ left : Fin 73
  /-- Second partner of the rooted triple. -/ right : Fin 73
  /-- Vertex in the canonical A role. -/ a : Fin 73
  /-- Vertex in the canonical B role. -/ b : Fin 73
  /-- Vertex in the canonical C role. -/ c : Fin 73
  /-- Patch containing the triple. -/ rotated : Bool
  /-- First axial coordinate of its center. -/ centerQ : Int
  /-- Second axial coordinate of its center. -/ centerR : Int
  /-- Whether the canonical triangle is inverted. -/ negated : Bool
deriving DecidableEq

/-- A vertex has the requested axial coordinates in the requested patch.
The common origin belongs to both patches. -/
def partsGadgetAxialAt (rotated : Bool) (q r : Int)
    (vertex : Fin 73) : Prop :=
  let descriptor := partsGadgetVertex vertex
  descriptor.q = q ∧ descriptor.r = r ∧
    (descriptor.rotated = rotated ∨ (q = 0 ∧ r = 0))

instance (rotated : Bool) (q r : Int) (vertex : Fin 73) :
    Decidable (partsGadgetAxialAt rotated q r vertex) := by
  unfold partsGadgetAxialAt
  infer_instance

/-- Decidable equality-up-to-permutation for three named vertices. -/
def partsGadgetSameTriple (a b c x y z : Fin 73) : Prop :=
  (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
    (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
    (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)

instance (a b c x y z : Fin 73) :
    Decidable (partsGadgetSameTriple a b c x y z) := by
  unfold partsGadgetSameTriple
  infer_instance

/-- Exact validity conditions for a triangle witness. -/
def PartsGadgetTriangleWitnessData.Valid
    (witness : PartsGadgetTriangleWitnessData) (root : Fin 73) : Prop :=
  partsGadgetSameTriple witness.a witness.b witness.c
      root witness.left witness.right ∧
    partsGadgetAxialAt witness.rotated
      (witness.centerQ + if witness.negated then -1 else 1)
      witness.centerR witness.a ∧
    partsGadgetAxialAt witness.rotated witness.centerQ
      (witness.centerR + if witness.negated then 1 else -1)
      witness.b ∧
    partsGadgetAxialAt witness.rotated
      (witness.centerQ + if witness.negated then 1 else -1)
      (witness.centerR + if witness.negated then -1 else 1)
      witness.c

instance (witness : PartsGadgetTriangleWitnessData) (root : Fin 73) :
    Decidable (witness.Valid root) := by
  unfold PartsGadgetTriangleWitnessData.Valid
  infer_instance

/-- Geometric witnesses for every listed sqrt-three triple. -/
def partsGadgetTriangleWitnesses (vertex : Fin 73) :
    List PartsGadgetTriangleWitnessData :=
  match vertex.val with
  | 0 => [
    ⟨6, 10, 0, 6, 10, false, -2, 0, true⟩,
  ]
  | 1 => [
    ⟨4, 11, 11, 4, 1, false, -2, 0, false⟩,
    ⟨7, 11, 1, 7, 11, false, -2, 1, true⟩,
  ]
  | 2 => [
    ⟨5, 12, 12, 5, 2, false, -2, 1, false⟩,
    ⟨8, 12, 2, 8, 12, false, -2, 2, true⟩,
  ]
  | 3 => [
    ⟨6, 13, 13, 6, 3, false, -2, 2, false⟩,
  ]
  | 4 => [
    ⟨1, 11, 11, 4, 1, false, -2, 0, false⟩,
    ⟨11, 16, 4, 11, 16, false, -1, -1, true⟩,
  ]
  | 5 => [
    ⟨2, 12, 12, 5, 2, false, -2, 1, false⟩,
    ⟨9, 17, 17, 9, 5, false, -1, -1, false⟩,
    ⟨12, 17, 5, 12, 17, false, -1, 0, true⟩,
  ]
  | 6 => [
    ⟨0, 10, 0, 6, 10, false, -2, 0, true⟩,
    ⟨3, 13, 13, 6, 3, false, -2, 2, false⟩,
    ⟨10, 18, 18, 10, 6, false, -1, 0, false⟩,
    ⟨13, 18, 6, 13, 18, false, -1, 1, true⟩,
  ]
  | 7 => [
    ⟨1, 11, 1, 7, 11, false, -2, 1, true⟩,
    ⟨11, 19, 19, 11, 7, false, -1, 1, false⟩,
    ⟨14, 19, 7, 14, 19, false, -1, 2, true⟩,
  ]
  | 8 => [
    ⟨2, 12, 2, 8, 12, false, -2, 2, true⟩,
    ⟨12, 20, 20, 12, 8, false, -1, 2, false⟩,
  ]
  | 9 => [
    ⟨5, 17, 17, 9, 5, false, -1, -1, false⟩,
    ⟨17, 22, 9, 17, 22, false, 0, -2, true⟩,
  ]
  | 10 => [
    ⟨0, 6, 0, 6, 10, false, -2, 0, true⟩,
    ⟨6, 18, 18, 10, 6, false, -1, 0, false⟩,
    ⟨15, 23, 23, 15, 10, false, 0, -2, false⟩,
    ⟨18, 23, 10, 18, 23, false, 0, -1, true⟩,
  ]
  | 11 => [
    ⟨1, 4, 11, 4, 1, false, -2, 0, false⟩,
    ⟨1, 7, 1, 7, 11, false, -2, 1, true⟩,
    ⟨4, 16, 4, 11, 16, false, -1, -1, true⟩,
    ⟨7, 19, 19, 11, 7, false, -1, 1, false⟩,
    ⟨16, 24, 24, 16, 11, false, 0, -1, false⟩,
    ⟨19, 24, 11, 19, 24, false, 0, 0, true⟩,
  ]
  | 12 => [
    ⟨2, 5, 12, 5, 2, false, -2, 1, false⟩,
    ⟨2, 8, 2, 8, 12, false, -2, 2, true⟩,
    ⟨5, 17, 5, 12, 17, false, -1, 0, true⟩,
    ⟨8, 20, 20, 12, 8, false, -1, 2, false⟩,
    ⟨17, 25, 25, 17, 12, false, 0, 0, false⟩,
    ⟨20, 25, 12, 20, 25, false, 0, 1, true⟩,
  ]
  | 13 => [
    ⟨3, 6, 13, 6, 3, false, -2, 2, false⟩,
    ⟨6, 18, 6, 13, 18, false, -1, 1, true⟩,
    ⟨18, 26, 26, 18, 13, false, 0, 1, false⟩,
    ⟨21, 26, 13, 21, 26, false, 0, 2, true⟩,
  ]
  | 14 => [
    ⟨7, 19, 7, 14, 19, false, -1, 2, true⟩,
    ⟨19, 27, 27, 19, 14, false, 0, 2, false⟩,
  ]
  | 15 => [
    ⟨10, 23, 23, 15, 10, false, 0, -2, false⟩,
  ]
  | 16 => [
    ⟨4, 11, 4, 11, 16, false, -1, -1, true⟩,
    ⟨11, 24, 24, 16, 11, false, 0, -1, false⟩,
    ⟨24, 28, 16, 24, 28, false, 1, -2, true⟩,
  ]
  | 17 => [
    ⟨5, 9, 17, 9, 5, false, -1, -1, false⟩,
    ⟨5, 12, 5, 12, 17, false, -1, 0, true⟩,
    ⟨9, 22, 9, 17, 22, false, 0, -2, true⟩,
    ⟨12, 25, 25, 17, 12, false, 0, 0, false⟩,
    ⟨22, 29, 29, 22, 17, false, 1, -2, false⟩,
    ⟨25, 29, 17, 25, 29, false, 1, -1, true⟩,
  ]
  | 18 => [
    ⟨6, 10, 18, 10, 6, false, -1, 0, false⟩,
    ⟨6, 13, 6, 13, 18, false, -1, 1, true⟩,
    ⟨10, 23, 10, 18, 23, false, 0, -1, true⟩,
    ⟨13, 26, 26, 18, 13, false, 0, 1, false⟩,
    ⟨23, 30, 30, 23, 18, false, 1, -1, false⟩,
    ⟨26, 30, 18, 26, 30, false, 1, 0, true⟩,
    ⟨43, 47, 18, 47, 43, true, -1, 0, false⟩,
    ⟨43, 50, 43, 50, 18, true, -1, 1, true⟩,
    ⟨47, 59, 47, 18, 59, true, 0, -1, true⟩,
    ⟨50, 62, 62, 18, 50, true, 0, 1, false⟩,
    ⟨59, 66, 66, 59, 18, true, 1, -1, false⟩,
    ⟨62, 66, 18, 62, 66, true, 1, 0, true⟩,
  ]
  | 19 => [
    ⟨7, 11, 19, 11, 7, false, -1, 1, false⟩,
    ⟨7, 14, 7, 14, 19, false, -1, 2, true⟩,
    ⟨11, 24, 11, 19, 24, false, 0, 0, true⟩,
    ⟨14, 27, 27, 19, 14, false, 0, 2, false⟩,
    ⟨24, 31, 31, 24, 19, false, 1, 0, false⟩,
    ⟨27, 31, 19, 27, 31, false, 1, 1, true⟩,
  ]
  | 20 => [
    ⟨8, 12, 20, 12, 8, false, -1, 2, false⟩,
    ⟨12, 25, 12, 20, 25, false, 0, 1, true⟩,
    ⟨25, 32, 32, 25, 20, false, 1, 1, false⟩,
  ]
  | 21 => [
    ⟨13, 26, 13, 21, 26, false, 0, 2, true⟩,
  ]
  | 22 => [
    ⟨9, 17, 9, 17, 22, false, 0, -2, true⟩,
    ⟨17, 29, 29, 22, 17, false, 1, -2, false⟩,
  ]
  | 23 => [
    ⟨10, 15, 23, 15, 10, false, 0, -2, false⟩,
    ⟨10, 18, 10, 18, 23, false, 0, -1, true⟩,
    ⟨18, 30, 30, 23, 18, false, 1, -1, false⟩,
    ⟨30, 33, 23, 30, 33, false, 2, -2, true⟩,
  ]
  | 24 => [
    ⟨11, 16, 24, 16, 11, false, 0, -1, false⟩,
    ⟨11, 19, 11, 19, 24, false, 0, 0, true⟩,
    ⟨16, 28, 16, 24, 28, false, 1, -2, true⟩,
    ⟨19, 31, 31, 24, 19, false, 1, 0, false⟩,
    ⟨28, 34, 34, 28, 24, false, 2, -2, false⟩,
    ⟨31, 34, 24, 31, 34, false, 2, -1, true⟩,
  ]
  | 25 => [
    ⟨12, 17, 25, 17, 12, false, 0, 0, false⟩,
    ⟨12, 20, 12, 20, 25, false, 0, 1, true⟩,
    ⟨17, 29, 17, 25, 29, false, 1, -1, true⟩,
    ⟨20, 32, 32, 25, 20, false, 1, 1, false⟩,
    ⟨29, 35, 35, 29, 25, false, 2, -1, false⟩,
    ⟨32, 35, 25, 32, 35, false, 2, 0, true⟩,
  ]
  | 26 => [
    ⟨13, 18, 26, 18, 13, false, 0, 1, false⟩,
    ⟨13, 21, 13, 21, 26, false, 0, 2, true⟩,
    ⟨18, 30, 18, 26, 30, false, 1, 0, true⟩,
    ⟨30, 36, 36, 30, 26, false, 2, 0, false⟩,
  ]
  | 27 => [
    ⟨14, 19, 27, 19, 14, false, 0, 2, false⟩,
    ⟨19, 31, 19, 27, 31, false, 1, 1, true⟩,
  ]
  | 28 => [
    ⟨16, 24, 16, 24, 28, false, 1, -2, true⟩,
    ⟨24, 34, 34, 28, 24, false, 2, -2, false⟩,
  ]
  | 29 => [
    ⟨17, 22, 29, 22, 17, false, 1, -2, false⟩,
    ⟨17, 25, 17, 25, 29, false, 1, -1, true⟩,
    ⟨25, 35, 35, 29, 25, false, 2, -1, false⟩,
  ]
  | 30 => [
    ⟨18, 23, 30, 23, 18, false, 1, -1, false⟩,
    ⟨18, 26, 18, 26, 30, false, 1, 0, true⟩,
    ⟨23, 33, 23, 30, 33, false, 2, -2, true⟩,
    ⟨26, 36, 36, 30, 26, false, 2, 0, false⟩,
  ]
  | 31 => [
    ⟨19, 24, 31, 24, 19, false, 1, 0, false⟩,
    ⟨19, 27, 19, 27, 31, false, 1, 1, true⟩,
    ⟨24, 34, 24, 31, 34, false, 2, -1, true⟩,
  ]
  | 32 => [
    ⟨20, 25, 32, 25, 20, false, 1, 1, false⟩,
    ⟨25, 35, 25, 32, 35, false, 2, 0, true⟩,
  ]
  | 33 => [
    ⟨23, 30, 23, 30, 33, false, 2, -2, true⟩,
  ]
  | 34 => [
    ⟨24, 28, 34, 28, 24, false, 2, -2, false⟩,
    ⟨24, 31, 24, 31, 34, false, 2, -1, true⟩,
  ]
  | 35 => [
    ⟨25, 29, 35, 29, 25, false, 2, -1, false⟩,
    ⟨25, 32, 25, 32, 35, false, 2, 0, true⟩,
  ]
  | 36 => [
    ⟨26, 30, 36, 30, 26, false, 2, 0, false⟩,
  ]
  | 37 => [
    ⟨43, 47, 37, 43, 47, true, -2, 0, true⟩,
  ]
  | 38 => [
    ⟨41, 48, 48, 41, 38, true, -2, 0, false⟩,
    ⟨44, 48, 38, 44, 48, true, -2, 1, true⟩,
  ]
  | 39 => [
    ⟨42, 49, 49, 42, 39, true, -2, 1, false⟩,
    ⟨45, 49, 39, 45, 49, true, -2, 2, true⟩,
  ]
  | 40 => [
    ⟨43, 50, 50, 43, 40, true, -2, 2, false⟩,
  ]
  | 41 => [
    ⟨38, 48, 48, 41, 38, true, -2, 0, false⟩,
    ⟨48, 53, 41, 48, 53, true, -1, -1, true⟩,
  ]
  | 42 => [
    ⟨39, 49, 49, 42, 39, true, -2, 1, false⟩,
    ⟨46, 54, 54, 46, 42, true, -1, -1, false⟩,
    ⟨49, 54, 42, 49, 54, true, -1, 0, true⟩,
  ]
  | 43 => [
    ⟨18, 47, 18, 47, 43, true, -1, 0, false⟩,
    ⟨18, 50, 43, 50, 18, true, -1, 1, true⟩,
    ⟨37, 47, 37, 43, 47, true, -2, 0, true⟩,
    ⟨40, 50, 50, 43, 40, true, -2, 2, false⟩,
  ]
  | 44 => [
    ⟨38, 48, 38, 44, 48, true, -2, 1, true⟩,
    ⟨48, 55, 55, 48, 44, true, -1, 1, false⟩,
    ⟨51, 55, 44, 51, 55, true, -1, 2, true⟩,
  ]
  | 45 => [
    ⟨39, 49, 39, 45, 49, true, -2, 2, true⟩,
    ⟨49, 56, 56, 49, 45, true, -1, 2, false⟩,
  ]
  | 46 => [
    ⟨42, 54, 54, 46, 42, true, -1, -1, false⟩,
    ⟨54, 58, 46, 54, 58, true, 0, -2, true⟩,
  ]
  | 47 => [
    ⟨18, 43, 18, 47, 43, true, -1, 0, false⟩,
    ⟨18, 59, 47, 18, 59, true, 0, -1, true⟩,
    ⟨37, 43, 37, 43, 47, true, -2, 0, true⟩,
    ⟨52, 59, 59, 52, 47, true, 0, -2, false⟩,
  ]
  | 48 => [
    ⟨38, 41, 48, 41, 38, true, -2, 0, false⟩,
    ⟨38, 44, 38, 44, 48, true, -2, 1, true⟩,
    ⟨41, 53, 41, 48, 53, true, -1, -1, true⟩,
    ⟨44, 55, 55, 48, 44, true, -1, 1, false⟩,
    ⟨53, 60, 60, 53, 48, true, 0, -1, false⟩,
    ⟨55, 60, 48, 55, 60, true, 0, 0, true⟩,
  ]
  | 49 => [
    ⟨39, 42, 49, 42, 39, true, -2, 1, false⟩,
    ⟨39, 45, 39, 45, 49, true, -2, 2, true⟩,
    ⟨42, 54, 42, 49, 54, true, -1, 0, true⟩,
    ⟨45, 56, 56, 49, 45, true, -1, 2, false⟩,
    ⟨54, 61, 61, 54, 49, true, 0, 0, false⟩,
    ⟨56, 61, 49, 56, 61, true, 0, 1, true⟩,
  ]
  | 50 => [
    ⟨18, 43, 43, 50, 18, true, -1, 1, true⟩,
    ⟨18, 62, 62, 18, 50, true, 0, 1, false⟩,
    ⟨40, 43, 50, 43, 40, true, -2, 2, false⟩,
    ⟨57, 62, 50, 57, 62, true, 0, 2, true⟩,
  ]
  | 51 => [
    ⟨44, 55, 44, 51, 55, true, -1, 2, true⟩,
    ⟨55, 63, 63, 55, 51, true, 0, 2, false⟩,
  ]
  | 52 => [
    ⟨47, 59, 59, 52, 47, true, 0, -2, false⟩,
  ]
  | 53 => [
    ⟨41, 48, 41, 48, 53, true, -1, -1, true⟩,
    ⟨48, 60, 60, 53, 48, true, 0, -1, false⟩,
    ⟨60, 64, 53, 60, 64, true, 1, -2, true⟩,
  ]
  | 54 => [
    ⟨42, 46, 54, 46, 42, true, -1, -1, false⟩,
    ⟨42, 49, 42, 49, 54, true, -1, 0, true⟩,
    ⟨46, 58, 46, 54, 58, true, 0, -2, true⟩,
    ⟨49, 61, 61, 54, 49, true, 0, 0, false⟩,
    ⟨58, 65, 65, 58, 54, true, 1, -2, false⟩,
    ⟨61, 65, 54, 61, 65, true, 1, -1, true⟩,
  ]
  | 55 => [
    ⟨44, 48, 55, 48, 44, true, -1, 1, false⟩,
    ⟨44, 51, 44, 51, 55, true, -1, 2, true⟩,
    ⟨48, 60, 48, 55, 60, true, 0, 0, true⟩,
    ⟨51, 63, 63, 55, 51, true, 0, 2, false⟩,
    ⟨60, 67, 67, 60, 55, true, 1, 0, false⟩,
    ⟨63, 67, 55, 63, 67, true, 1, 1, true⟩,
  ]
  | 56 => [
    ⟨45, 49, 56, 49, 45, true, -1, 2, false⟩,
    ⟨49, 61, 49, 56, 61, true, 0, 1, true⟩,
    ⟨61, 68, 68, 61, 56, true, 1, 1, false⟩,
  ]
  | 57 => [
    ⟨50, 62, 50, 57, 62, true, 0, 2, true⟩,
  ]
  | 58 => [
    ⟨46, 54, 46, 54, 58, true, 0, -2, true⟩,
    ⟨54, 65, 65, 58, 54, true, 1, -2, false⟩,
  ]
  | 59 => [
    ⟨18, 47, 47, 18, 59, true, 0, -1, true⟩,
    ⟨18, 66, 66, 59, 18, true, 1, -1, false⟩,
    ⟨47, 52, 59, 52, 47, true, 0, -2, false⟩,
    ⟨66, 69, 59, 66, 69, true, 2, -2, true⟩,
  ]
  | 60 => [
    ⟨48, 53, 60, 53, 48, true, 0, -1, false⟩,
    ⟨48, 55, 48, 55, 60, true, 0, 0, true⟩,
    ⟨53, 64, 53, 60, 64, true, 1, -2, true⟩,
    ⟨55, 67, 67, 60, 55, true, 1, 0, false⟩,
    ⟨64, 70, 70, 64, 60, true, 2, -2, false⟩,
    ⟨67, 70, 60, 67, 70, true, 2, -1, true⟩,
  ]
  | 61 => [
    ⟨49, 54, 61, 54, 49, true, 0, 0, false⟩,
    ⟨49, 56, 49, 56, 61, true, 0, 1, true⟩,
    ⟨54, 65, 54, 61, 65, true, 1, -1, true⟩,
    ⟨56, 68, 68, 61, 56, true, 1, 1, false⟩,
    ⟨65, 71, 71, 65, 61, true, 2, -1, false⟩,
    ⟨68, 71, 61, 68, 71, true, 2, 0, true⟩,
  ]
  | 62 => [
    ⟨18, 50, 62, 18, 50, true, 0, 1, false⟩,
    ⟨18, 66, 18, 62, 66, true, 1, 0, true⟩,
    ⟨50, 57, 50, 57, 62, true, 0, 2, true⟩,
    ⟨66, 72, 72, 66, 62, true, 2, 0, false⟩,
  ]
  | 63 => [
    ⟨51, 55, 63, 55, 51, true, 0, 2, false⟩,
    ⟨55, 67, 55, 63, 67, true, 1, 1, true⟩,
  ]
  | 64 => [
    ⟨53, 60, 53, 60, 64, true, 1, -2, true⟩,
    ⟨60, 70, 70, 64, 60, true, 2, -2, false⟩,
  ]
  | 65 => [
    ⟨54, 58, 65, 58, 54, true, 1, -2, false⟩,
    ⟨54, 61, 54, 61, 65, true, 1, -1, true⟩,
    ⟨61, 71, 71, 65, 61, true, 2, -1, false⟩,
  ]
  | 66 => [
    ⟨18, 59, 66, 59, 18, true, 1, -1, false⟩,
    ⟨18, 62, 18, 62, 66, true, 1, 0, true⟩,
    ⟨59, 69, 59, 66, 69, true, 2, -2, true⟩,
    ⟨62, 72, 72, 66, 62, true, 2, 0, false⟩,
  ]
  | 67 => [
    ⟨55, 60, 67, 60, 55, true, 1, 0, false⟩,
    ⟨55, 63, 55, 63, 67, true, 1, 1, true⟩,
    ⟨60, 70, 60, 67, 70, true, 2, -1, true⟩,
  ]
  | 68 => [
    ⟨56, 61, 68, 61, 56, true, 1, 1, false⟩,
    ⟨61, 71, 61, 68, 71, true, 2, 0, true⟩,
  ]
  | 69 => [
    ⟨59, 66, 59, 66, 69, true, 2, -2, true⟩,
  ]
  | 70 => [
    ⟨60, 64, 70, 64, 60, true, 2, -2, false⟩,
    ⟨60, 67, 60, 67, 70, true, 2, -1, true⟩,
  ]
  | 71 => [
    ⟨61, 65, 71, 65, 61, true, 2, -1, false⟩,
    ⟨61, 68, 61, 68, 71, true, 2, 0, true⟩,
  ]
  | 72 => [
    ⟨62, 66, 72, 66, 62, true, 2, 0, false⟩,
  ]
  | _ => []

/-- Unit-edge neighbors used by the executable certificate checker. -/
def partsGadgetNeighbors (vertex : Fin 73) : List (Fin 73) :=
  match vertex.val with
  | 0 => [1, 4, 5]
  | 1 => [0, 2, 5, 6]
  | 2 => [1, 3, 6, 7]
  | 3 => [2, 7, 8]
  | 4 => [0, 5, 9, 10]
  | 5 => [0, 1, 4, 6, 10, 11, 42]
  | 6 => [1, 2, 5, 7, 11, 12]
  | 7 => [2, 3, 6, 8, 12, 13, 44]
  | 8 => [3, 7, 13, 14]
  | 9 => [4, 10, 15, 16]
  | 10 => [4, 5, 9, 11, 16, 17]
  | 11 => [5, 6, 10, 12, 17, 18]
  | 12 => [6, 7, 11, 13, 18, 19]
  | 13 => [7, 8, 12, 14, 19, 20]
  | 14 => [8, 13, 20, 21]
  | 15 => [9, 16, 22]
  | 16 => [9, 10, 15, 17, 22, 23, 53]
  | 17 => [10, 11, 16, 18, 23, 24]
  | 18 => [11, 12, 17, 19, 24, 25, 48, 49, 54, 55, 60, 61]
  | 19 => [12, 13, 18, 20, 25, 26]
  | 20 => [13, 14, 19, 21, 26, 27, 56]
  | 21 => [14, 20, 27]
  | 22 => [15, 16, 23, 28]
  | 23 => [16, 17, 22, 24, 28, 29]
  | 24 => [17, 18, 23, 25, 29, 30]
  | 25 => [18, 19, 24, 26, 30, 31]
  | 26 => [19, 20, 25, 27, 31, 32]
  | 27 => [20, 21, 26, 32]
  | 28 => [22, 23, 29, 33]
  | 29 => [23, 24, 28, 30, 33, 34, 65]
  | 30 => [24, 25, 29, 31, 34, 35]
  | 31 => [25, 26, 30, 32, 35, 36, 67]
  | 32 => [26, 27, 31, 36]
  | 33 => [28, 29, 34]
  | 34 => [29, 30, 33, 35]
  | 35 => [30, 31, 34, 36]
  | 36 => [31, 32, 35]
  | 37 => [38, 41, 42]
  | 38 => [37, 39, 42, 43]
  | 39 => [38, 40, 43, 44]
  | 40 => [39, 44, 45]
  | 41 => [37, 42, 46, 47]
  | 42 => [5, 37, 38, 41, 43, 47, 48]
  | 43 => [38, 39, 42, 44, 48, 49]
  | 44 => [7, 39, 40, 43, 45, 49, 50]
  | 45 => [40, 44, 50, 51]
  | 46 => [41, 47, 52, 53]
  | 47 => [41, 42, 46, 48, 53, 54]
  | 48 => [18, 42, 43, 47, 49, 54]
  | 49 => [18, 43, 44, 48, 50, 55]
  | 50 => [44, 45, 49, 51, 55, 56]
  | 51 => [45, 50, 56, 57]
  | 52 => [46, 53, 58]
  | 53 => [16, 46, 47, 52, 54, 58, 59]
  | 54 => [18, 47, 48, 53, 59, 60]
  | 55 => [18, 49, 50, 56, 61, 62]
  | 56 => [20, 50, 51, 55, 57, 62, 63]
  | 57 => [51, 56, 63]
  | 58 => [52, 53, 59, 64]
  | 59 => [53, 54, 58, 60, 64, 65]
  | 60 => [18, 54, 59, 61, 65, 66]
  | 61 => [18, 55, 60, 62, 66, 67]
  | 62 => [55, 56, 61, 63, 67, 68]
  | 63 => [56, 57, 62, 68]
  | 64 => [58, 59, 65, 69]
  | 65 => [29, 59, 60, 64, 66, 69, 70]
  | 66 => [60, 61, 65, 67, 70, 71]
  | 67 => [31, 61, 62, 66, 68, 71, 72]
  | 68 => [62, 63, 67, 72]
  | 69 => [64, 65, 70]
  | 70 => [65, 66, 69, 71]
  | 71 => [66, 67, 70, 72]
  | 72 => [67, 68, 71]
  | _ => []

/-- Opposite pairs completing sqrt-three triples at a vertex. -/
def partsGadgetTriplePairs (vertex : Fin 73) : List (Fin 73 × Fin 73) :=
  (partsGadgetTriangleWitnesses vertex).map fun witness =>
    (witness.left, witness.right)

/-- Central inversion of both lattice patches. -/
def partsGadgetNegation (vertex : Fin 73) : Fin 73 :=
  match vertex.val with
  | 0 => 36
  | 1 => 35
  | 2 => 34
  | 3 => 33
  | 4 => 32
  | 5 => 31
  | 6 => 30
  | 7 => 29
  | 8 => 28
  | 9 => 27
  | 10 => 26
  | 11 => 25
  | 12 => 24
  | 13 => 23
  | 14 => 22
  | 15 => 21
  | 16 => 20
  | 17 => 19
  | 18 => 18
  | 19 => 17
  | 20 => 16
  | 21 => 15
  | 22 => 14
  | 23 => 13
  | 24 => 12
  | 25 => 11
  | 26 => 10
  | 27 => 9
  | 28 => 8
  | 29 => 7
  | 30 => 6
  | 31 => 5
  | 32 => 4
  | 33 => 3
  | 34 => 2
  | 35 => 1
  | 36 => 0
  | 37 => 72
  | 38 => 71
  | 39 => 70
  | 40 => 69
  | 41 => 68
  | 42 => 67
  | 43 => 66
  | 44 => 65
  | 45 => 64
  | 46 => 63
  | 47 => 62
  | 48 => 61
  | 49 => 60
  | 50 => 59
  | 51 => 58
  | 52 => 57
  | 53 => 56
  | 54 => 55
  | 55 => 54
  | 56 => 53
  | 57 => 52
  | 58 => 51
  | 59 => 50
  | 60 => 49
  | 61 => 48
  | 62 => 47
  | 63 => 46
  | 64 => 45
  | 65 => 44
  | 66 => 43
  | 67 => 42
  | 68 => 41
  | 69 => 40
  | 70 => 39
  | 71 => 38
  | 72 => 37
  | _ => 18

end HadwigerNelsonBounds
