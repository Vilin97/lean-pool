/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Kernel-checked finite certificate for the Sp₄(F₂) normal-subgroup argument in
Zhou §6. The exhaustive Boolean matrix search is isolated here from the
conceptual action and transvection lemmas.
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4Basic

/-!
# Kernel-checked `Sp₄(𝔽₂)` normal-subgroup certificate

This module isolates an exhaustive Boolean-matrix certificate showing that
the finite symplectic factor has no nontrivial normal abelian subgroup. The
search is split into kernel-checked chunks and decoded back to Mathlib's
symplectic-matrix carrier for the public theorem used in Zhou §6.
-/

namespace Connes
namespace Sp4

private abbrev Matrix4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F
private abbrev BVMatrix := BitVec 16
private abbrev BMatrix := Fin 4 → Fin 4 → Bool

private def bvEntry (x : BVMatrix) : BMatrix := fun i j =>
  x.getLsbD (4 * i.val + j.val)

private def boolDot (a b : BMatrix) (i j : Fin 4) : Bool :=
  (a i 0 && b 0 j) ^^ (a i 1 && b 1 j) ^^
  (a i 2 && b 2 j) ^^ (a i 3 && b 3 j)

private def boolMul (a b : BMatrix) : BMatrix := boolDot a b
private def boolTranspose (a : BMatrix) : BMatrix := fun i j => a j i

private def boolMatrixEq (a b : BMatrix) : Prop :=
  a 0 0 = b 0 0 ∧ a 0 1 = b 0 1 ∧ a 0 2 = b 0 2 ∧ a 0 3 = b 0 3 ∧
  a 1 0 = b 1 0 ∧ a 1 1 = b 1 1 ∧ a 1 2 = b 1 2 ∧ a 1 3 = b 1 3 ∧
  a 2 0 = b 2 0 ∧ a 2 1 = b 2 1 ∧ a 2 2 = b 2 2 ∧ a 2 3 = b 2 3 ∧
  a 3 0 = b 3 0 ∧ a 3 1 = b 3 1 ∧ a 3 2 = b 3 2 ∧ a 3 3 = b 3 3

private def boolMatrixEqB (a b : BMatrix) : Bool :=
  (a 0 0 == b 0 0) && (a 0 1 == b 0 1) &&
  (a 0 2 == b 0 2) && (a 0 3 == b 0 3) &&
  (a 1 0 == b 1 0) && (a 1 1 == b 1 1) &&
  (a 1 2 == b 1 2) && (a 1 3 == b 1 3) &&
  (a 2 0 == b 2 0) && (a 2 1 == b 2 1) &&
  (a 2 2 == b 2 2) && (a 2 3 == b 2 3) &&
  (a 3 0 == b 3 0) && (a 3 1 == b 3 1) &&
  (a 3 2 == b 3 2) && (a 3 3 == b 3 3)

private theorem boolMatrixEqB_eq_true_iff (a b : BMatrix) :
    boolMatrixEqB a b = true ↔ boolMatrixEq a b := by
  simp only [boolMatrixEqB, Bool.and_eq_true, beq_iff_eq, boolMatrixEq]
  tauto

private def boolOne : BMatrix := bvEntry (BitVec.ofNat 16 0x8421)
private def boolJ : BMatrix := bvEntry (BitVec.ofNat 16 0x2184)
private def boolG1 : BMatrix := bvEntry (BitVec.ofNat 16 0x13DB)
private def boolG1Inv : BMatrix := bvEntry (BitVec.ofNat 16 0x5FC8)
private def boolG2 : BMatrix := bvEntry (BitVec.ofNat 16 0x21B7)
private def boolG2Inv : BMatrix := bvEntry (BitVec.ofNat 16 0xED84)

private def boolSymplectic (x : BMatrix) : Prop :=
  boolMatrixEq (boolMul (boolMul x boolJ) (boolTranspose x)) boolJ

private def boolConj (g gi x : BMatrix) : BMatrix := boolMul (boolMul g x) gi
private def boolCommutes (a b : BMatrix) : Prop :=
  boolMatrixEq (boolMul a b) (boolMul b a)

private def boolCommutesB (a b : BMatrix) : Bool :=
  boolMatrixEqB (boolMul a b) (boolMul b a)

private def detectorCheck (x : BVMatrix) : Bool :=
  !(boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
      (boolTranspose (bvEntry x))) boolJ) ||
  boolMatrixEqB (bvEntry x) boolOne ||
  !(boolCommutesB (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x)) ||
  !(boolCommutesB (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x))

section KernelDetectorChunks

private theorem detectorChunk0 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 0 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk1 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 1 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk2 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 2 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk3 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 3 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk4 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 4 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk5 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 5 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk6 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 6 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk7 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 7 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk8 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 8 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk9 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 9 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk10 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 10 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk11 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 11 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk12 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 12 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk13 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 13 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk14 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 14 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk15 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 15 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk16 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 16 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk17 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 17 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk18 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 18 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk19 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 19 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk20 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 20 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk21 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 21 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk22 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 22 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk23 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 23 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk24 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 24 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk25 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 25 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk26 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 26 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk27 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 27 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk28 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 28 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk29 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 29 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk30 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 30 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk31 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 31 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk32 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 32 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk33 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 33 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk34 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 34 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk35 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 35 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk36 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 36 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk37 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 37 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk38 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 38 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk39 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 39 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk40 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 40 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk41 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 41 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk42 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 42 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk43 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 43 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk44 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 44 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk45 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 45 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk46 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 46 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk47 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 47 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk48 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 48 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk49 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 49 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk50 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 50 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk51 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 51 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk52 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 52 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk53 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 53 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk54 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 54 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk55 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 55 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk56 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 56 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk57 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 57 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk58 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 58 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk59 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 59 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk60 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 60 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk61 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 61 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk62 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 62 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk63 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 63 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk64 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 64 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk65 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 65 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk66 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 66 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk67 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 67 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk68 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 68 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk69 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 69 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk70 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 70 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk71 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 71 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk72 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 72 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk73 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 73 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk74 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 74 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk75 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 75 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk76 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 76 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk77 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 77 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk78 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 78 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk79 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 79 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk80 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 80 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk81 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 81 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk82 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 82 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk83 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 83 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk84 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 84 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk85 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 85 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk86 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 86 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk87 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 87 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk88 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 88 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk89 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 89 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk90 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 90 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk91 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 91 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk92 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 92 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk93 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 93 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk94 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 94 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk95 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 95 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk96 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 96 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk97 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 97 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk98 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 98 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk99 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 99 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk100 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 100 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk101 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 101 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk102 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 102 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk103 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 103 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk104 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 104 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk105 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 105 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk106 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 106 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk107 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 107 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk108 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 108 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk109 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 109 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk110 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 110 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk111 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 111 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk112 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 112 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk113 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 113 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk114 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 114 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk115 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 115 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk116 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 116 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk117 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 117 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk118 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 118 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk119 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 119 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk120 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 120 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk121 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 121 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk122 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 122 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk123 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 123 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk124 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 124 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk125 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 125 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk126 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 126 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk127 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 127 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk128 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 128 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk129 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 129 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk130 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 130 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk131 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 131 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk132 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 132 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk133 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 133 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk134 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 134 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk135 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 135 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk136 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 136 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk137 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 137 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk138 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 138 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk139 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 139 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk140 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 140 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk141 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 141 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk142 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 142 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk143 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 143 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk144 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 144 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk145 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 145 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk146 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 146 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk147 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 147 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk148 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 148 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk149 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 149 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk150 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 150 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk151 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 151 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk152 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 152 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk153 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 153 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk154 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 154 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk155 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 155 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk156 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 156 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk157 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 157 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk158 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 158 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk159 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 159 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk160 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 160 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk161 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 161 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk162 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 162 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk163 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 163 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk164 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 164 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk165 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 165 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk166 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 166 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk167 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 167 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk168 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 168 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk169 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 169 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk170 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 170 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk171 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 171 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk172 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 172 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk173 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 173 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk174 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 174 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk175 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 175 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk176 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 176 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk177 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 177 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk178 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 178 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk179 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 179 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk180 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 180 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk181 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 181 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk182 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 182 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk183 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 183 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk184 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 184 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk185 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 185 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk186 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 186 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk187 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 187 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk188 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 188 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk189 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 189 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk190 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 190 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk191 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 191 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk192 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 192 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk193 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 193 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk194 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 194 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk195 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 195 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk196 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 196 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk197 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 197 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk198 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 198 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk199 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 199 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk200 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 200 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk201 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 201 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk202 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 202 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk203 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 203 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk204 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 204 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk205 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 205 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk206 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 206 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk207 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 207 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk208 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 208 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk209 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 209 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk210 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 210 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk211 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 211 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk212 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 212 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk213 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 213 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk214 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 214 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk215 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 215 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk216 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 216 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk217 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 217 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk218 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 218 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk219 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 219 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk220 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 220 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk221 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 221 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk222 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 222 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk223 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 223 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk224 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 224 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk225 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 225 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk226 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 226 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk227 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 227 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk228 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 228 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk229 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 229 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk230 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 230 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk231 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 231 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk232 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 232 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk233 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 233 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk234 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 234 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk235 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 235 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk236 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 236 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk237 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 237 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk238 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 238 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk239 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 239 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk240 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 240 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk241 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 241 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk242 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 242 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk243 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 243 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk244 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 244 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk245 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 245 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk246 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 246 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk247 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 247 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk248 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 248 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk249 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 249 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk250 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 250 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk251 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 251 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk252 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 252 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk253 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 253 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk254 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 254 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunk255 : ∀ mid low : Fin 16,
    detectorCheck (BitVec.ofNat 16 (256 * 255 + 16 * mid.val + low.val)) = true := by
  decide

private theorem detectorChunkFromParts (hi : ℕ)
    (h : ∀ mid low : Fin 16,
      detectorCheck (BitVec.ofNat 16 (256 * hi + 16 * mid.val + low.val)) = true)
    (lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * hi + lo.val)) = true := by
  let mid : Fin 16 := ⟨lo.val / 16, by omega⟩
  let low : Fin 16 := ⟨lo.val % 16, Nat.mod_lt _ (by omega)⟩
  have hval : 256 * hi + lo.val = 256 * hi + 16 * mid.val + low.val := by
    dsimp [mid, low]
    omega
  rw [hval]
  exact h mid low

private theorem detectorChunks0 (hi : Fin 64) (lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * hi.val + lo.val)) = true := by
  fin_cases hi
  · exact detectorChunkFromParts 0 detectorChunk0 lo
  · exact detectorChunkFromParts 1 detectorChunk1 lo
  · exact detectorChunkFromParts 2 detectorChunk2 lo
  · exact detectorChunkFromParts 3 detectorChunk3 lo
  · exact detectorChunkFromParts 4 detectorChunk4 lo
  · exact detectorChunkFromParts 5 detectorChunk5 lo
  · exact detectorChunkFromParts 6 detectorChunk6 lo
  · exact detectorChunkFromParts 7 detectorChunk7 lo
  · exact detectorChunkFromParts 8 detectorChunk8 lo
  · exact detectorChunkFromParts 9 detectorChunk9 lo
  · exact detectorChunkFromParts 10 detectorChunk10 lo
  · exact detectorChunkFromParts 11 detectorChunk11 lo
  · exact detectorChunkFromParts 12 detectorChunk12 lo
  · exact detectorChunkFromParts 13 detectorChunk13 lo
  · exact detectorChunkFromParts 14 detectorChunk14 lo
  · exact detectorChunkFromParts 15 detectorChunk15 lo
  · exact detectorChunkFromParts 16 detectorChunk16 lo
  · exact detectorChunkFromParts 17 detectorChunk17 lo
  · exact detectorChunkFromParts 18 detectorChunk18 lo
  · exact detectorChunkFromParts 19 detectorChunk19 lo
  · exact detectorChunkFromParts 20 detectorChunk20 lo
  · exact detectorChunkFromParts 21 detectorChunk21 lo
  · exact detectorChunkFromParts 22 detectorChunk22 lo
  · exact detectorChunkFromParts 23 detectorChunk23 lo
  · exact detectorChunkFromParts 24 detectorChunk24 lo
  · exact detectorChunkFromParts 25 detectorChunk25 lo
  · exact detectorChunkFromParts 26 detectorChunk26 lo
  · exact detectorChunkFromParts 27 detectorChunk27 lo
  · exact detectorChunkFromParts 28 detectorChunk28 lo
  · exact detectorChunkFromParts 29 detectorChunk29 lo
  · exact detectorChunkFromParts 30 detectorChunk30 lo
  · exact detectorChunkFromParts 31 detectorChunk31 lo
  · exact detectorChunkFromParts 32 detectorChunk32 lo
  · exact detectorChunkFromParts 33 detectorChunk33 lo
  · exact detectorChunkFromParts 34 detectorChunk34 lo
  · exact detectorChunkFromParts 35 detectorChunk35 lo
  · exact detectorChunkFromParts 36 detectorChunk36 lo
  · exact detectorChunkFromParts 37 detectorChunk37 lo
  · exact detectorChunkFromParts 38 detectorChunk38 lo
  · exact detectorChunkFromParts 39 detectorChunk39 lo
  · exact detectorChunkFromParts 40 detectorChunk40 lo
  · exact detectorChunkFromParts 41 detectorChunk41 lo
  · exact detectorChunkFromParts 42 detectorChunk42 lo
  · exact detectorChunkFromParts 43 detectorChunk43 lo
  · exact detectorChunkFromParts 44 detectorChunk44 lo
  · exact detectorChunkFromParts 45 detectorChunk45 lo
  · exact detectorChunkFromParts 46 detectorChunk46 lo
  · exact detectorChunkFromParts 47 detectorChunk47 lo
  · exact detectorChunkFromParts 48 detectorChunk48 lo
  · exact detectorChunkFromParts 49 detectorChunk49 lo
  · exact detectorChunkFromParts 50 detectorChunk50 lo
  · exact detectorChunkFromParts 51 detectorChunk51 lo
  · exact detectorChunkFromParts 52 detectorChunk52 lo
  · exact detectorChunkFromParts 53 detectorChunk53 lo
  · exact detectorChunkFromParts 54 detectorChunk54 lo
  · exact detectorChunkFromParts 55 detectorChunk55 lo
  · exact detectorChunkFromParts 56 detectorChunk56 lo
  · exact detectorChunkFromParts 57 detectorChunk57 lo
  · exact detectorChunkFromParts 58 detectorChunk58 lo
  · exact detectorChunkFromParts 59 detectorChunk59 lo
  · exact detectorChunkFromParts 60 detectorChunk60 lo
  · exact detectorChunkFromParts 61 detectorChunk61 lo
  · exact detectorChunkFromParts 62 detectorChunk62 lo
  · exact detectorChunkFromParts 63 detectorChunk63 lo

private theorem detectorChunks1 (hi : Fin 64) (lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * (64 + hi.val) + lo.val)) = true := by
  fin_cases hi
  · exact detectorChunkFromParts 64 detectorChunk64 lo
  · exact detectorChunkFromParts 65 detectorChunk65 lo
  · exact detectorChunkFromParts 66 detectorChunk66 lo
  · exact detectorChunkFromParts 67 detectorChunk67 lo
  · exact detectorChunkFromParts 68 detectorChunk68 lo
  · exact detectorChunkFromParts 69 detectorChunk69 lo
  · exact detectorChunkFromParts 70 detectorChunk70 lo
  · exact detectorChunkFromParts 71 detectorChunk71 lo
  · exact detectorChunkFromParts 72 detectorChunk72 lo
  · exact detectorChunkFromParts 73 detectorChunk73 lo
  · exact detectorChunkFromParts 74 detectorChunk74 lo
  · exact detectorChunkFromParts 75 detectorChunk75 lo
  · exact detectorChunkFromParts 76 detectorChunk76 lo
  · exact detectorChunkFromParts 77 detectorChunk77 lo
  · exact detectorChunkFromParts 78 detectorChunk78 lo
  · exact detectorChunkFromParts 79 detectorChunk79 lo
  · exact detectorChunkFromParts 80 detectorChunk80 lo
  · exact detectorChunkFromParts 81 detectorChunk81 lo
  · exact detectorChunkFromParts 82 detectorChunk82 lo
  · exact detectorChunkFromParts 83 detectorChunk83 lo
  · exact detectorChunkFromParts 84 detectorChunk84 lo
  · exact detectorChunkFromParts 85 detectorChunk85 lo
  · exact detectorChunkFromParts 86 detectorChunk86 lo
  · exact detectorChunkFromParts 87 detectorChunk87 lo
  · exact detectorChunkFromParts 88 detectorChunk88 lo
  · exact detectorChunkFromParts 89 detectorChunk89 lo
  · exact detectorChunkFromParts 90 detectorChunk90 lo
  · exact detectorChunkFromParts 91 detectorChunk91 lo
  · exact detectorChunkFromParts 92 detectorChunk92 lo
  · exact detectorChunkFromParts 93 detectorChunk93 lo
  · exact detectorChunkFromParts 94 detectorChunk94 lo
  · exact detectorChunkFromParts 95 detectorChunk95 lo
  · exact detectorChunkFromParts 96 detectorChunk96 lo
  · exact detectorChunkFromParts 97 detectorChunk97 lo
  · exact detectorChunkFromParts 98 detectorChunk98 lo
  · exact detectorChunkFromParts 99 detectorChunk99 lo
  · exact detectorChunkFromParts 100 detectorChunk100 lo
  · exact detectorChunkFromParts 101 detectorChunk101 lo
  · exact detectorChunkFromParts 102 detectorChunk102 lo
  · exact detectorChunkFromParts 103 detectorChunk103 lo
  · exact detectorChunkFromParts 104 detectorChunk104 lo
  · exact detectorChunkFromParts 105 detectorChunk105 lo
  · exact detectorChunkFromParts 106 detectorChunk106 lo
  · exact detectorChunkFromParts 107 detectorChunk107 lo
  · exact detectorChunkFromParts 108 detectorChunk108 lo
  · exact detectorChunkFromParts 109 detectorChunk109 lo
  · exact detectorChunkFromParts 110 detectorChunk110 lo
  · exact detectorChunkFromParts 111 detectorChunk111 lo
  · exact detectorChunkFromParts 112 detectorChunk112 lo
  · exact detectorChunkFromParts 113 detectorChunk113 lo
  · exact detectorChunkFromParts 114 detectorChunk114 lo
  · exact detectorChunkFromParts 115 detectorChunk115 lo
  · exact detectorChunkFromParts 116 detectorChunk116 lo
  · exact detectorChunkFromParts 117 detectorChunk117 lo
  · exact detectorChunkFromParts 118 detectorChunk118 lo
  · exact detectorChunkFromParts 119 detectorChunk119 lo
  · exact detectorChunkFromParts 120 detectorChunk120 lo
  · exact detectorChunkFromParts 121 detectorChunk121 lo
  · exact detectorChunkFromParts 122 detectorChunk122 lo
  · exact detectorChunkFromParts 123 detectorChunk123 lo
  · exact detectorChunkFromParts 124 detectorChunk124 lo
  · exact detectorChunkFromParts 125 detectorChunk125 lo
  · exact detectorChunkFromParts 126 detectorChunk126 lo
  · exact detectorChunkFromParts 127 detectorChunk127 lo

private theorem detectorChunks2 (hi : Fin 64) (lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * (128 + hi.val) + lo.val)) = true := by
  fin_cases hi
  · exact detectorChunkFromParts 128 detectorChunk128 lo
  · exact detectorChunkFromParts 129 detectorChunk129 lo
  · exact detectorChunkFromParts 130 detectorChunk130 lo
  · exact detectorChunkFromParts 131 detectorChunk131 lo
  · exact detectorChunkFromParts 132 detectorChunk132 lo
  · exact detectorChunkFromParts 133 detectorChunk133 lo
  · exact detectorChunkFromParts 134 detectorChunk134 lo
  · exact detectorChunkFromParts 135 detectorChunk135 lo
  · exact detectorChunkFromParts 136 detectorChunk136 lo
  · exact detectorChunkFromParts 137 detectorChunk137 lo
  · exact detectorChunkFromParts 138 detectorChunk138 lo
  · exact detectorChunkFromParts 139 detectorChunk139 lo
  · exact detectorChunkFromParts 140 detectorChunk140 lo
  · exact detectorChunkFromParts 141 detectorChunk141 lo
  · exact detectorChunkFromParts 142 detectorChunk142 lo
  · exact detectorChunkFromParts 143 detectorChunk143 lo
  · exact detectorChunkFromParts 144 detectorChunk144 lo
  · exact detectorChunkFromParts 145 detectorChunk145 lo
  · exact detectorChunkFromParts 146 detectorChunk146 lo
  · exact detectorChunkFromParts 147 detectorChunk147 lo
  · exact detectorChunkFromParts 148 detectorChunk148 lo
  · exact detectorChunkFromParts 149 detectorChunk149 lo
  · exact detectorChunkFromParts 150 detectorChunk150 lo
  · exact detectorChunkFromParts 151 detectorChunk151 lo
  · exact detectorChunkFromParts 152 detectorChunk152 lo
  · exact detectorChunkFromParts 153 detectorChunk153 lo
  · exact detectorChunkFromParts 154 detectorChunk154 lo
  · exact detectorChunkFromParts 155 detectorChunk155 lo
  · exact detectorChunkFromParts 156 detectorChunk156 lo
  · exact detectorChunkFromParts 157 detectorChunk157 lo
  · exact detectorChunkFromParts 158 detectorChunk158 lo
  · exact detectorChunkFromParts 159 detectorChunk159 lo
  · exact detectorChunkFromParts 160 detectorChunk160 lo
  · exact detectorChunkFromParts 161 detectorChunk161 lo
  · exact detectorChunkFromParts 162 detectorChunk162 lo
  · exact detectorChunkFromParts 163 detectorChunk163 lo
  · exact detectorChunkFromParts 164 detectorChunk164 lo
  · exact detectorChunkFromParts 165 detectorChunk165 lo
  · exact detectorChunkFromParts 166 detectorChunk166 lo
  · exact detectorChunkFromParts 167 detectorChunk167 lo
  · exact detectorChunkFromParts 168 detectorChunk168 lo
  · exact detectorChunkFromParts 169 detectorChunk169 lo
  · exact detectorChunkFromParts 170 detectorChunk170 lo
  · exact detectorChunkFromParts 171 detectorChunk171 lo
  · exact detectorChunkFromParts 172 detectorChunk172 lo
  · exact detectorChunkFromParts 173 detectorChunk173 lo
  · exact detectorChunkFromParts 174 detectorChunk174 lo
  · exact detectorChunkFromParts 175 detectorChunk175 lo
  · exact detectorChunkFromParts 176 detectorChunk176 lo
  · exact detectorChunkFromParts 177 detectorChunk177 lo
  · exact detectorChunkFromParts 178 detectorChunk178 lo
  · exact detectorChunkFromParts 179 detectorChunk179 lo
  · exact detectorChunkFromParts 180 detectorChunk180 lo
  · exact detectorChunkFromParts 181 detectorChunk181 lo
  · exact detectorChunkFromParts 182 detectorChunk182 lo
  · exact detectorChunkFromParts 183 detectorChunk183 lo
  · exact detectorChunkFromParts 184 detectorChunk184 lo
  · exact detectorChunkFromParts 185 detectorChunk185 lo
  · exact detectorChunkFromParts 186 detectorChunk186 lo
  · exact detectorChunkFromParts 187 detectorChunk187 lo
  · exact detectorChunkFromParts 188 detectorChunk188 lo
  · exact detectorChunkFromParts 189 detectorChunk189 lo
  · exact detectorChunkFromParts 190 detectorChunk190 lo
  · exact detectorChunkFromParts 191 detectorChunk191 lo

private theorem detectorChunks3 (hi : Fin 64) (lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * (192 + hi.val) + lo.val)) = true := by
  fin_cases hi
  · exact detectorChunkFromParts 192 detectorChunk192 lo
  · exact detectorChunkFromParts 193 detectorChunk193 lo
  · exact detectorChunkFromParts 194 detectorChunk194 lo
  · exact detectorChunkFromParts 195 detectorChunk195 lo
  · exact detectorChunkFromParts 196 detectorChunk196 lo
  · exact detectorChunkFromParts 197 detectorChunk197 lo
  · exact detectorChunkFromParts 198 detectorChunk198 lo
  · exact detectorChunkFromParts 199 detectorChunk199 lo
  · exact detectorChunkFromParts 200 detectorChunk200 lo
  · exact detectorChunkFromParts 201 detectorChunk201 lo
  · exact detectorChunkFromParts 202 detectorChunk202 lo
  · exact detectorChunkFromParts 203 detectorChunk203 lo
  · exact detectorChunkFromParts 204 detectorChunk204 lo
  · exact detectorChunkFromParts 205 detectorChunk205 lo
  · exact detectorChunkFromParts 206 detectorChunk206 lo
  · exact detectorChunkFromParts 207 detectorChunk207 lo
  · exact detectorChunkFromParts 208 detectorChunk208 lo
  · exact detectorChunkFromParts 209 detectorChunk209 lo
  · exact detectorChunkFromParts 210 detectorChunk210 lo
  · exact detectorChunkFromParts 211 detectorChunk211 lo
  · exact detectorChunkFromParts 212 detectorChunk212 lo
  · exact detectorChunkFromParts 213 detectorChunk213 lo
  · exact detectorChunkFromParts 214 detectorChunk214 lo
  · exact detectorChunkFromParts 215 detectorChunk215 lo
  · exact detectorChunkFromParts 216 detectorChunk216 lo
  · exact detectorChunkFromParts 217 detectorChunk217 lo
  · exact detectorChunkFromParts 218 detectorChunk218 lo
  · exact detectorChunkFromParts 219 detectorChunk219 lo
  · exact detectorChunkFromParts 220 detectorChunk220 lo
  · exact detectorChunkFromParts 221 detectorChunk221 lo
  · exact detectorChunkFromParts 222 detectorChunk222 lo
  · exact detectorChunkFromParts 223 detectorChunk223 lo
  · exact detectorChunkFromParts 224 detectorChunk224 lo
  · exact detectorChunkFromParts 225 detectorChunk225 lo
  · exact detectorChunkFromParts 226 detectorChunk226 lo
  · exact detectorChunkFromParts 227 detectorChunk227 lo
  · exact detectorChunkFromParts 228 detectorChunk228 lo
  · exact detectorChunkFromParts 229 detectorChunk229 lo
  · exact detectorChunkFromParts 230 detectorChunk230 lo
  · exact detectorChunkFromParts 231 detectorChunk231 lo
  · exact detectorChunkFromParts 232 detectorChunk232 lo
  · exact detectorChunkFromParts 233 detectorChunk233 lo
  · exact detectorChunkFromParts 234 detectorChunk234 lo
  · exact detectorChunkFromParts 235 detectorChunk235 lo
  · exact detectorChunkFromParts 236 detectorChunk236 lo
  · exact detectorChunkFromParts 237 detectorChunk237 lo
  · exact detectorChunkFromParts 238 detectorChunk238 lo
  · exact detectorChunkFromParts 239 detectorChunk239 lo
  · exact detectorChunkFromParts 240 detectorChunk240 lo
  · exact detectorChunkFromParts 241 detectorChunk241 lo
  · exact detectorChunkFromParts 242 detectorChunk242 lo
  · exact detectorChunkFromParts 243 detectorChunk243 lo
  · exact detectorChunkFromParts 244 detectorChunk244 lo
  · exact detectorChunkFromParts 245 detectorChunk245 lo
  · exact detectorChunkFromParts 246 detectorChunk246 lo
  · exact detectorChunkFromParts 247 detectorChunk247 lo
  · exact detectorChunkFromParts 248 detectorChunk248 lo
  · exact detectorChunkFromParts 249 detectorChunk249 lo
  · exact detectorChunkFromParts 250 detectorChunk250 lo
  · exact detectorChunkFromParts 251 detectorChunk251 lo
  · exact detectorChunkFromParts 252 detectorChunk252 lo
  · exact detectorChunkFromParts 253 detectorChunk253 lo
  · exact detectorChunkFromParts 254 detectorChunk254 lo
  · exact detectorChunkFromParts 255 detectorChunk255 lo

private theorem detectorChunks (hi lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * hi.val + lo.val)) = true := by
  by_cases h0 : hi.val < 64
  · exact detectorChunks0 ⟨hi.val, h0⟩ lo
  by_cases h1 : hi.val < 128
  · have hoffset : hi.val - 64 < 64 := by omega
    have hval : 64 + (hi.val - 64) = hi.val := by omega
    simpa only [hval] using detectorChunks1 ⟨hi.val - 64, hoffset⟩ lo
  by_cases h2 : hi.val < 192
  · have hoffset : hi.val - 128 < 64 := by omega
    have hval : 128 + (hi.val - 128) = hi.val := by omega
    simpa only [hval] using detectorChunks2 ⟨hi.val - 128, hoffset⟩ lo
  · have hoffset : hi.val - 192 < 64 := by omega
    have hval : 192 + (hi.val - 192) = hi.val := by omega
    simpa only [hval] using detectorChunks3 ⟨hi.val - 192, hoffset⟩ lo

private theorem detectorCheck_all (x : BVMatrix) : detectorCheck x = true := by
  have hxlt : x.toNat < 65536 := by
    simpa using x.toFin.isLt
  let hi : Fin 256 := ⟨x.toNat / 256, by omega⟩
  let lo : Fin 256 := ⟨x.toNat % 256, Nat.mod_lt _ (by omega)⟩
  have hval : 256 * hi.val + lo.val = x.toNat := by
    dsimp [hi, lo]
    omega
  have hx : BitVec.ofNat 16 (256 * hi.val + lo.val) = x := by
    apply BitVec.eq_of_toNat_eq
    have hxlt' : x.toNat < 2 ^ 16 := by
      norm_num at hxlt ⊢
      exact hxlt
    rw [BitVec.toNat_ofNat, hval, Nat.mod_eq_of_lt hxlt']
  rw [← hx]
  exact detectorChunks hi lo

private theorem boolean_detector_cover : ∀ x : BVMatrix,
    boolSymplectic (bvEntry x) → ¬boolMatrixEq (bvEntry x) boolOne →
    ¬boolCommutes (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x) ∨
    ¬boolCommutes (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x) := by
  intro x hs hn
  have hc := detectorCheck_all x
  have hsB :
      boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
        (boolTranspose (bvEntry x))) boolJ = true :=
    (boolMatrixEqB_eq_true_iff _ _).2 hs
  have hnB : boolMatrixEqB (bvEntry x) boolOne = false := by
    cases h : boolMatrixEqB (bvEntry x) boolOne
    · rfl
    · exact (hn ((boolMatrixEqB_eq_true_iff _ _).1 h)).elim
  rw [detectorCheck, hsB, hnB] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  by_cases h1 :
      boolCommutesB (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x) = true
  · right
    intro hp
    have h2 :
        boolCommutesB (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x) = true := by
      exact (boolMatrixEqB_eq_true_iff _ _).2 hp
    simp [h1, h2] at hc
  · left
    intro hp
    exact h1 ((boolMatrixEqB_eq_true_iff _ _).2 hp)

end KernelDetectorChunks

private abbrev MatrixIndex := Fin 2 ⊕ Fin 2

private def matrixIndex (i : MatrixIndex) : Fin 4 := finSumFinEquiv i
private def boolToF (b : Bool) : F := if b then 1 else 0

private theorem boolToF_and (a b : Bool) :
    boolToF (a && b) = boolToF a * boolToF b := by
  cases a <;> cases b <;> rfl

private theorem boolToF_xor (a b : Bool) :
    boolToF (a ^^ b) = boolToF a + boolToF b := by
  cases a <;> cases b <;> rfl

private theorem boolToF_decide_eq_one (a : F) :
    boolToF (decide (a = 1)) = a := by
  fin_cases a <;> rfl

private theorem boolToF_injective : Function.Injective boolToF := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolToF]

private def decodeBoolMatrix (a : BMatrix) : Matrix4 := fun i j =>
  boolToF (a (matrixIndex i) (matrixIndex j))

private theorem decodeBoolMatrix_mul (a b : BMatrix) :
    decodeBoolMatrix (boolMul a b) = decodeBoolMatrix a * decodeBoolMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decodeBoolMatrix, boolMul, boolDot, matrixIndex, Matrix.mul_apply,
      boolToF_and, boolToF_xor, Fin.sum_univ_two, finSumFinEquiv] <;>
    ring

private theorem decodeBoolMatrix_transpose (a : BMatrix) :
    decodeBoolMatrix (boolTranspose a) = (decodeBoolMatrix a).transpose := by
  rfl

private theorem boolMatrixEq_iff_decode_eq (a b : BMatrix) :
    boolMatrixEq a b ↔ decodeBoolMatrix a = decodeBoolMatrix b := by
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [boolMatrixEq, decodeBoolMatrix, matrixIndex, finSumFinEquiv]
  · intro h
    have hij (i j : Fin 4) : a i j = b i j := by
      have hm := congrFun (congrFun h (finSumFinEquiv.symm i))
        (finSumFinEquiv.symm j)
      apply boolToF_injective
      simpa [decodeBoolMatrix, matrixIndex] using hm
    simp only [boolMatrixEq]
    aesop

private def bvBit (n : Nat) (b : Bool) : BVMatrix :=
  (BitVec.ofBool b).setWidth 16 <<< n

private def bvBuild (f : Fin 16 → Bool) : BVMatrix :=
  bvBit 0 (f 0) ||| bvBit 1 (f 1) ||| bvBit 2 (f 2) ||| bvBit 3 (f 3) |||
  bvBit 4 (f 4) ||| bvBit 5 (f 5) ||| bvBit 6 (f 6) ||| bvBit 7 (f 7) |||
  bvBit 8 (f 8) ||| bvBit 9 (f 9) ||| bvBit 10 (f 10) ||| bvBit 11 (f 11) |||
  bvBit 12 (f 12) ||| bvBit 13 (f 13) ||| bvBit 14 (f 14) ||| bvBit 15 (f 15)

private theorem bvBuild_getLsbD (f : Fin 16 → Bool) (k : Fin 16) :
    (bvBuild f).getLsbD k.val = f k := by
  fin_cases k <;> simp [bvBuild, bvBit]

private def rowOfBit (k : Fin 16) : MatrixIndex :=
  finSumFinEquiv.symm ⟨k.val / 4, by omega⟩

private def colOfBit (k : Fin 16) : MatrixIndex :=
  finSumFinEquiv.symm ⟨k.val % 4, Nat.mod_lt _ (by omega)⟩

private def encodeMatrix (M : Matrix4) : BVMatrix :=
  bvBuild fun k => decide (M (rowOfBit k) (colOfBit k) = 1)

private theorem decode_encodeMatrix (M : Matrix4) :
    decodeBoolMatrix (bvEntry (encodeMatrix M)) = M := by
  ext i j
  let k : Fin 16 := ⟨4 * (matrixIndex i).val + (matrixIndex j).val, by omega⟩
  have hget := bvBuild_getLsbD
    (fun k => decide (M (rowOfBit k) (colOfBit k) = 1)) k
  change boolToF ((encodeMatrix M).getLsbD k.val) = M i j
  rw [show encodeMatrix M = bvBuild
      (fun k => decide (M (rowOfBit k) (colOfBit k) = 1)) by rfl, hget]
  have hrow : rowOfBit k = i := by
    have hval : k.val / 4 = (matrixIndex i).val := by
      dsimp [k]
      omega
    apply finSumFinEquiv.injective
    simp only [rowOfBit, Equiv.apply_symm_apply]
    exact Fin.ext hval
  have hcol : colOfBit k = j := by
    have hval : k.val % 4 = (matrixIndex j).val := by
      dsimp [k]
      omega
    apply finSumFinEquiv.injective
    simp only [colOfBit, Equiv.apply_symm_apply]
    exact Fin.ext hval
  rw [hrow, hcol]
  exact boolToF_decide_eq_one _

private theorem decode_boolOne : decodeBoolMatrix boolOne = (1 : Matrix4) := by
  decide

private theorem decode_boolJ :
    decodeBoolMatrix boolJ = Matrix.J (Fin 2) F := by
  decide

private def detectorOne : Group := ⟨decodeBoolMatrix boolG1, by
  change decodeBoolMatrix boolG1 * Matrix.J (Fin 2) F *
      (decodeBoolMatrix boolG1).transpose = Matrix.J (Fin 2) F
  decide⟩

private def detectorTwo : Group := ⟨decodeBoolMatrix boolG2, by
  change decodeBoolMatrix boolG2 * Matrix.J (Fin 2) F *
      (decodeBoolMatrix boolG2).transpose = Matrix.J (Fin 2) F
  decide⟩

private theorem detectorOne_inv :
    ((detectorOne⁻¹ : Group) : Matrix4) = decodeBoolMatrix boolG1Inv := by
  decide

private theorem detectorTwo_inv :
    ((detectorTwo⁻¹ : Group) : Matrix4) = decodeBoolMatrix boolG2Inv := by
  decide

private theorem encoded_symplectic (x : Group) :
    boolSymplectic (bvEntry (encodeMatrix (x : Matrix4))) := by
  unfold boolSymplectic
  apply (boolMatrixEq_iff_decode_eq _ _).2
  rw [decodeBoolMatrix_mul, decodeBoolMatrix_mul, decodeBoolMatrix_transpose,
    decode_encodeMatrix, decode_boolJ]
  exact x.property

private theorem encoded_ne_one (x : Group) (hx : x ≠ 1) :
    ¬boolMatrixEq (bvEntry (encodeMatrix (x : Matrix4))) boolOne := by
  intro h
  apply hx
  apply Subtype.ext
  have hm := (boolMatrixEq_iff_decode_eq _ _).1 h
  simpa [decode_encodeMatrix, decode_boolOne] using hm

private theorem conjugacy_detector :
    ∀ x : Group, x ≠ 1 →
      ∃ g : Group, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) := by
  intro x hx
  have hc := boolean_detector_cover (encodeMatrix (x : Matrix4))
    (encoded_symplectic x) (encoded_ne_one x hx)
  rcases hc with h | h
  · refine ⟨detectorOne, ?_⟩
    intro hcomm
    apply h
    unfold boolCommutes boolConj
    apply (boolMatrixEq_iff_decode_eq _ _).2
    simp only [decodeBoolMatrix_mul, decode_encodeMatrix]
    rw [show decodeBoolMatrix boolG1 = (detectorOne : Matrix4) by rfl]
    rw [← detectorOne_inv]
    exact congrArg Subtype.val hcomm
  · refine ⟨detectorTwo, ?_⟩
    intro hcomm
    apply h
    unfold boolCommutes boolConj
    apply (boolMatrixEq_iff_decode_eq _ _).2
    simp only [decodeBoolMatrix_mul, decode_encodeMatrix]
    rw [show decodeBoolMatrix boolG2 = (detectorTwo : Matrix4) by rfl]
    rw [← detectorTwo_inv]
    exact congrArg Subtype.val hcomm

/-- The finite symplectic factor has no nontrivial normal abelian subgroup.
This strengthens the elementary-abelian case used in Zhou §6. -/
theorem no_nontrivial_normal_abelian_subgroup
    (N : Subgroup Group) (hnormal : N.Normal)
    (hab : ∀ x y : N, x * y = y * x) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : Group) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  obtain ⟨g, hcomm⟩ := conjugacy_detector x hxne
  have hy : g * (x : Group) * g⁻¹ ∈ N := hnormal.conj_mem x hx g
  let y : N := ⟨g * (x : Group) * g⁻¹, hy⟩
  have hxy := hab y ⟨x, hx⟩
  apply hcomm
  exact congrArg Subtype.val hxy

end Sp4
end Connes
