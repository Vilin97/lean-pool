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

/-- Boolean certificate predicate used by the kernel-checked finite search. -/
def kernelDetectorCheck (x : BitVec 16) : Bool :=
  !(boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
      (boolTranspose (bvEntry x))) boolJ) ||
  boolMatrixEqB (bvEntry x) boolOne ||
  !(boolCommutesB (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x)) ||
  !(boolCommutesB (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x))

section KernelDetectorChunks

private theorem boolean_detector_cover
    (hcertificate : ∀ x : BitVec 16, kernelDetectorCheck x = true) : ∀ x : BVMatrix,
    boolSymplectic (bvEntry x) → ¬boolMatrixEq (bvEntry x) boolOne →
    ¬boolCommutes (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x) ∨
    ¬boolCommutes (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x) := by
  intro x hs hn
  have hc := hcertificate x
  have hsB :
      boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
        (boolTranspose (bvEntry x))) boolJ = true :=
    (boolMatrixEqB_eq_true_iff _ _).2 hs
  have hnB : boolMatrixEqB (bvEntry x) boolOne = false := by
    cases h : boolMatrixEqB (bvEntry x) boolOne
    · rfl
    · exact (hn ((boolMatrixEqB_eq_true_iff _ _).1 h)).elim
  rw [kernelDetectorCheck, hsB, hnB] at hc
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

private theorem conjugacy_detector
    (hcertificate : ∀ x : BitVec 16, kernelDetectorCheck x = true) :
    ∀ x : Group, x ≠ 1 →
      ∃ g : Group, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) := by
  intro x hx
  have hc := boolean_detector_cover hcertificate (encodeMatrix (x : Matrix4))
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

/-- A complete detector certificate implies that the finite symplectic factor has no
nontrivial normal abelian subgroup. -/
theorem no_nontrivial_normal_abelian_subgroup_of_kernelDetector
    (hcertificate : ∀ x : BitVec 16, kernelDetectorCheck x = true)
    (N : Subgroup Group) (hnormal : N.Normal)
    (hab : ∀ x y : N, x * y = y * x) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : Group) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  obtain ⟨g, hcomm⟩ := conjugacy_detector hcertificate x hxne
  have hy : g * (x : Group) * g⁻¹ ∈ N := hnormal.conj_mem x hx g
  let y : N := ⟨g * (x : Group) * g⁻¹, hy⟩
  have hxy := hab y ⟨x, hx⟩
  apply hcomm
  exact congrArg Subtype.val hxy

end Sp4
end Connes
