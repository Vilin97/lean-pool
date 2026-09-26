/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineFPBasics

/-!
# Verified one-bit machine logic

Boolean values are represented by the one-bit words `[false]` and `[true]`.
The definitions remain total on arbitrary bitstrings by inspecting only the
leading bit through the verified selector machine.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Negate the input word's head bit and return its singleton encoding. -/
def machineNotBit (a : List Bool) : List Bool :=
  machineIfHead a [false] [true]

/-- Negate the second bit word when the first head is true; otherwise return the second word
unchanged. -/
def machineXorBit (a b : List Bool) : List Bool :=
  machineIfHead a (machineNotBit b) b

/-- Return the second bit word when the first head is true, and a false singleton otherwise. -/
def machineAndBit (a b : List Bool) : List Bool :=
  machineIfHead a b [false]

/-- Return a true singleton when the first head is true, and the second bit word otherwise. -/
def machineOrBit (a b : List Bool) : List Bool :=
  machineIfHead a [true] b

/-- The majority operation on three encoded bits, expressed through pairwise conjunctions. -/
def machineMajorityBit (a b c : List Bool) : List Bool :=
  machineOrBit (machineAndBit a b)
    (machineOrBit (machineAndBit a c) (machineAndBit b c))

/-- The full-adder sum bit, given by XOR of both input bits and the incoming carry. -/
def machineFullAdderSum (a b carry : List Bool) : List Bool :=
  machineXorBit (machineXorBit a b) carry

/-- The full-adder carry bit, given by the majority of both input bits and the incoming carry. -/
def machineFullAdderCarry (a b carry : List Bool) : List Bool :=
  machineMajorityBit a b carry

theorem machineNotBit_mem_FP {a : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) :
    (fun word => machineNotBit (a word)) ∈ Complexity.FP := by
  exact machineIfHead_mem_FP ha (machineConst_mem_FP [false])
    (machineConst_mem_FP [true])

theorem machineXorBit_mem_FP
    {a b : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP) :
    (fun word => machineXorBit (a word) (b word)) ∈ Complexity.FP := by
  exact machineIfHead_mem_FP ha (machineNotBit_mem_FP hb) hb

theorem machineAndBit_mem_FP
    {a b : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP) :
    (fun word => machineAndBit (a word) (b word)) ∈ Complexity.FP := by
  exact machineIfHead_mem_FP ha hb (machineConst_mem_FP [false])

theorem machineOrBit_mem_FP
    {a b : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP) :
    (fun word => machineOrBit (a word) (b word)) ∈ Complexity.FP := by
  exact machineIfHead_mem_FP ha (machineConst_mem_FP [true]) hb

theorem machineMajorityBit_mem_FP
    {a b c : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hc : c ∈ Complexity.FP) :
    (fun word => machineMajorityBit (a word) (b word) (c word)) ∈
      Complexity.FP := by
  apply machineOrBit_mem_FP
  · exact machineAndBit_mem_FP ha hb
  · apply machineOrBit_mem_FP
    · exact machineAndBit_mem_FP ha hc
    · exact machineAndBit_mem_FP hb hc

theorem machineFullAdderSum_mem_FP
    {a b carry : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hcarry : carry ∈ Complexity.FP) :
    (fun word => machineFullAdderSum (a word) (b word) (carry word)) ∈
      Complexity.FP := by
  exact machineXorBit_mem_FP (machineXorBit_mem_FP ha hb) hcarry

theorem machineFullAdderCarry_mem_FP
    {a b carry : List Bool → List Bool}
    (ha : a ∈ Complexity.FP) (hb : b ∈ Complexity.FP)
    (hcarry : carry ∈ Complexity.FP) :
    (fun word => machineFullAdderCarry (a word) (b word) (carry word)) ∈
      Complexity.FP := by
  exact machineMajorityBit_mem_FP ha hb hcarry

@[simp] theorem machineNotBit_one (a : Bool) :
    machineNotBit [a] = [!a] := by
  cases a <;> rfl

@[simp] theorem machineXorBit_one (a b : Bool) :
    machineXorBit [a] [b] = [xor a b] := by
  cases a <;> cases b <;> rfl

@[simp] theorem machineAndBit_one (a b : Bool) :
    machineAndBit [a] [b] = [a && b] := by
  cases a <;> cases b <;> rfl

@[simp] theorem machineOrBit_one (a b : Bool) :
    machineOrBit [a] [b] = [a || b] := by
  cases a <;> cases b <;> rfl

@[simp] theorem machineFullAdderSum_one (a b carry : Bool) :
    machineFullAdderSum [a] [b] [carry] = [xor (xor a b) carry] := by
  simp [machineFullAdderSum]

@[simp] theorem machineFullAdderCarry_one (a b carry : Bool) :
    machineFullAdderCarry [a] [b] [carry] =
      [(a && b) || (a && carry) || (b && carry)] := by
  cases a <;> cases b <;> cases carry <;> rfl

end BeyondBethe
