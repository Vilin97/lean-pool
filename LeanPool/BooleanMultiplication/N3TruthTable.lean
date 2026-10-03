/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N3
public import Batteries.Data.BitVec.Lemmas

/-!
# Independent truth-table cross-check for the `n = 3` lower bound

This module validates the concrete 64-bit encodings used while developing the
algebraic proof.  Nothing in `N3.lean` or the final theorem depends on it.
-/

public section

namespace UnrestrictedBooleanMul

/-- Interpret a Boolean bit as an element of the two-element field. -/
def bitF2 (b : Bool) : F₂ := if b then 1 else 0
/-- Convert a field element to its Boolean bit. -/
def f2Bit (x : F₂) : Bool := decide (x = 1)

@[simp] theorem f2Bit_zero : f2Bit 0 = false := by decide
@[simp] theorem f2Bit_one : f2Bit 1 = true := by decide

@[simp] theorem bitF2_f2Bit (x : F₂) : bitF2 (f2Bit x) = x := by
  fin_cases x <;> rfl

@[simp] theorem bitF2_xor (a b : Bool) : bitF2 (xor a b) = bitF2 a + bitF2 b := by
  cases a <;> cases b <;> decide

@[simp] theorem bitF2_and (a b : Bool) : bitF2 (a && b) = bitF2 a * bitF2 b := by
  cases a <;> cases b <;> decide

theorem bitF2_injective : Function.Injective bitF2 := by
  intro a b h
  cases a <;> cases b <;> simp [bitF2] at h ⊢

/-- Pack a field-valued coefficient vector with coordinate zero as the least significant bit. -/
def coeffBits {n : Nat} (c : Fin n → F₂) : BitVec n :=
  BitVec.ofFnLE (fun i ↦ f2Bit (c i))

theorem coeffBits_getLsb {n : Nat} (c : Fin n → F₂) (i : Fin n) :
    (coeffBits c).getLsb i = f2Bit (c i) := by
  simp [coeffBits]

@[simp] theorem coeffBits_getElem {n : Nat} (c : Fin n → F₂) (i : Nat) (h : i < n) :
    (coeffBits c)[i] = f2Bit (c ⟨i, h⟩) := by
  simp [coeffBits]

/-- Select a truth table when the coefficient bit is set, and the zero table otherwise. -/
def sel (b : Bool) (x : BitVec 64) : BitVec 64 := if b then x else 0

theorem bitF2_sel_getLsb (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 ((sel (f2Bit c) x).getLsb q) = c * bitF2 (x.getLsb q) := by
  cases h : f2Bit c
  · have hc : c = 0 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc, bitF2]
  · have hc : c = 1 := by rw [← bitF2_f2Bit c, h]; rfl
    simp [sel, hc]

theorem bitF2_sel_getElem (c : F₂) (x : BitVec 64) (q : Fin 64) :
    bitF2 (sel (f2Bit c) x)[q] = c * bitF2 x[q] :=
  bitF2_sel_getLsb c x q

@[simp] theorem bitF2_sel_getElemNat (c : F₂) (x : BitVec 64) (i : Nat) (h : i < 64) :
    bitF2 (sel (f2Bit c) x)[i] = c * bitF2 x[i] :=
  bitF2_sel_getLsb c x ⟨i, h⟩

/-- Truth-table column for input variable 0, in least-significant-bit assignment order. -/
def v0 : BitVec 64 := 0xAAAAAAAAAAAAAAAA#64
/-- Truth-table column for input variable 1, in least-significant-bit assignment order. -/
def v1 : BitVec 64 := 0xCCCCCCCCCCCCCCCC#64
/-- Truth-table column for input variable 2, in least-significant-bit assignment order. -/
def v2 : BitVec 64 := 0xF0F0F0F0F0F0F0F0#64
/-- Truth-table column for input variable 3, in least-significant-bit assignment order. -/
def v3 : BitVec 64 := 0xFF00FF00FF00FF00#64
/-- Truth-table column for input variable 4, in least-significant-bit assignment order. -/
def v4 : BitVec 64 := 0xFFFF0000FFFF0000#64
/-- Truth-table column for input variable 5, in least-significant-bit assignment order. -/
def v5 : BitVec 64 := 0xFFFFFFFF00000000#64

theorem bitF2_allOnes_getElem (q : Fin 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[q] = 1 := by
  fin_cases q <;> decide

@[simp] theorem bitF2_allOnes_getElemNat (i : Nat) (h : i < 64) :
    bitF2 (0xFFFFFFFFFFFFFFFF#64)[i] = 1 :=
  bitF2_allOnes_getElem ⟨i, h⟩

/-- Truth table for coefficient 0 of the product of two three-term polynomials. -/
def e0 := v0 &&& v3
/-- Truth table for coefficient 1 of the product of two three-term polynomials. -/
def e1 := (v0 &&& v4) ^^^ (v1 &&& v3)
/-- Truth table for coefficient 2 of the product of two three-term polynomials. -/
def e2 := (v0 &&& v5) ^^^ (v1 &&& v4) ^^^ (v2 &&& v3)
/-- Truth table for coefficient 3 of the product of two three-term polynomials. -/
def e3 := (v1 &&& v5) ^^^ (v2 &&& v4)
/-- Truth table for coefficient 4 of the product of two three-term polynomials. -/
def e4 := v2 &&& v5

/-- The six input-variable truth tables, in input order. -/
def tableVar : Fin 6 → BitVec 64 := ![v0, v1, v2, v3, v4, v5]
/-- Truth tables for the five coefficients of a three-term product. -/
def targetTable : Fin 5 → BitVec 64 := ![e0, e1, e2, e3, e4]

/-- The six Boolean input values encoded by a truth-table row. -/
def assignment (q : Fin 64) : Fin 6 → F₂ :=
  fun i ↦ bitF2 ((tableVar i).getLsb q)

theorem eval_Mul_three (i : Fin 5) (q : Fin 64) :
    eval (Mul 3 i) (assignment q) = bitF2 ((targetTable i).getLsb q) := by
  fin_cases i <;>
    simp [Mul, mulCoefficient, aVar, bVar, assignment, tableVar, targetTable, e0, e1, e2, e3,
      e4, Fin.sum_univ_succ]

/-- Truth table of a linear combination in the rational-place basis. -/
def truthR (x : BitVec 10) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e4 ^^^
  sel (x.getLsbD 9) (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4)

/-- Truth table of a linear combination in the affine-plus-target basis. -/
def truthW (x : BitVec 12) : BitVec 64 :=
  sel (x.getLsbD 0) (BitVec.allOnes 64) ^^^
  sel (x.getLsbD 1) v0 ^^^ sel (x.getLsbD 2) v1 ^^^
  sel (x.getLsbD 3) v2 ^^^ sel (x.getLsbD 4) v3 ^^^
  sel (x.getLsbD 5) v4 ^^^ sel (x.getLsbD 6) v5 ^^^
  sel (x.getLsbD 7) e0 ^^^ sel (x.getLsbD 8) e1 ^^^
  sel (x.getLsbD 9) e2 ^^^ sel (x.getLsbD 10) e3 ^^^
  sel (x.getLsbD 11) e4

theorem rationalRep_truth (c : Fin 10 → F₂) (q : Fin 64) :
    eval (rationalRep c) (assignment q) =
      bitF2 ((truthR (coeffBits c)).getLsb q) := by
  simp [rationalRep, rationalBasis, targetSum, truthR, eval_Mul_three, assignment, tableVar,
    targetTable, e0, e1, e2, e3, e4, Fin.sum_univ_succ, coeffBits]
  ring

theorem ambientRep_truth (c : Fin 12 → F₂) (q : Fin 64) :
    eval (ambientRep c) (assignment q) =
      bitF2 ((truthW (coeffBits c)).getLsb q) := by
  simp [ambientRep, ambientBasis, truthW, eval_Mul_three, assignment, tableVar, targetTable,
    e0, e1, e2, e3, e4, Fin.sum_univ_succ, coeffBits]

end UnrestrictedBooleanMul
