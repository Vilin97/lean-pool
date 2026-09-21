/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineEncoding
import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Algebra
import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Reverse

/-!
# Small verified polynomial-time bitstring combinators

These lemmas are a thin project-local surface over Complexitylib's concrete
Turing machines and Cobham soundness theorem.  They are used to assemble the
arithmetic and dynamic-state machines below without appealing to a semantic
"all Lean programs are efficient" principle.
-/

namespace BeyondBethe

open Complexity

theorem machineConst_mem_FP (word : List Bool) :
    (fun _ : List Bool => word) ∈ Complexity.FP := by
  exact CobhamFP_subset_FP (Cobham.const word)

theorem machinePrepend_mem_FP (bit : Bool) :
    (fun word : List Bool => bit :: word) ∈ Complexity.FP := by
  exact Cobham.cons_mem_FP bit

theorem machineTail_mem_FP :
    (fun word : List Bool => word.tail) ∈ Complexity.FP := by
  exact CobhamFP_subset_FP Cobham.tail

theorem machineReverse_mem_FP :
    List.reverse ∈ Complexity.FP := by
  exact reverse_mem_FP

/-- Replace every input bit by zero while preserving the input length. -/
theorem machineZeroBlock_mem_FP :
    (fun word : List Bool => List.replicate word.length false) ∈
      Complexity.FP := by
  exact CobhamFP_subset_FP Cobham.lengthPad

theorem machineCompose_mem_FP {f g : List Bool → List Bool}
    (hf : f ∈ Complexity.FP) (hg : g ∈ Complexity.FP) :
    (fun word => g (f word)) ∈ Complexity.FP := by
  simpa only [Function.comp_apply] using mem_FP_comp hf hg

theorem machinePair_mem_FP {left right : List Bool → List Bool}
    (hleft : left ∈ Complexity.FP) (hright : right ∈ Complexity.FP) :
    (fun word => pair (left word) (right word)) ∈ Complexity.FP := by
  exact Cobham.pairFn_mem_FP hleft hright

theorem machineAppend_mem_FP {left right : List Bool → List Bool}
    (hleft : left ∈ Complexity.FP) (hright : right ∈ Complexity.FP) :
    (fun word => left word ++ right word) ∈ Complexity.FP := by
  exact Cobham.appendFn_mem_FP hleft hright

/-- Take a prefix of one computed word whose length is another computed word. -/
theorem machineTake_mem_FP {ruler data : List Bool → List Bool}
    (hruler : ruler ∈ Complexity.FP) (hdata : data ∈ Complexity.FP) :
    (fun word => (data word).take (ruler word).length) ∈ Complexity.FP := by
  exact CobhamFP_subset_FP
    (Cobham.takeFn (FP_subset_CobhamFP hruler) (FP_subset_CobhamFP hdata))

/-- Select by the leading bit of a verified bitstring computation. -/
def machineIfHead (flag whenTrue whenFalse : List Bool) : List Bool :=
  Cobham.selectHead flag whenTrue whenFalse

theorem machineIfHead_mem_FP
    {flag whenTrue whenFalse : List Bool → List Bool}
    (hflag : flag ∈ Complexity.FP)
    (htrue : whenTrue ∈ Complexity.FP)
    (hfalse : whenFalse ∈ Complexity.FP) :
    (fun word => machineIfHead (flag word)
      (whenTrue word) (whenFalse word)) ∈ Complexity.FP := by
  exact Cobham.selectHeadFn_mem_FP hflag htrue hfalse

@[simp] theorem machineIfHead_true (tail whenTrue whenFalse : List Bool) :
    machineIfHead (true :: tail) whenTrue whenFalse = whenTrue := by
  simp [machineIfHead, Cobham.selectHead]

@[simp] theorem machineIfHead_false (tail whenTrue whenFalse : List Bool) :
    machineIfHead (false :: tail) whenTrue whenFalse = whenFalse := by
  simp [machineIfHead, Cobham.selectHead]

/-- Select the first branch exactly when `test` is empty. -/
def machineIfEmpty (test whenEmpty whenNonempty : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag test) whenEmpty whenNonempty

theorem machineIfEmpty_mem_FP
    {test whenEmpty whenNonempty : List Bool → List Bool}
    (htest : test ∈ Complexity.FP)
    (hempty : whenEmpty ∈ Complexity.FP)
    (hnonempty : whenNonempty ∈ Complexity.FP) :
    (fun word => machineIfEmpty (test word)
      (whenEmpty word) (whenNonempty word)) ∈ Complexity.FP := by
  exact Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP htest)
    hempty hnonempty

@[simp] theorem machineIfEmpty_nil (whenEmpty whenNonempty : List Bool) :
    machineIfEmpty [] whenEmpty whenNonempty = whenEmpty := by
  exact Cobham.selectHead_emptyFlag_nil _ _

@[simp] theorem machineIfEmpty_cons (bit : Bool) (tail whenEmpty whenNonempty : List Bool) :
    machineIfEmpty (bit :: tail) whenEmpty whenNonempty = whenNonempty := by
  exact Cobham.selectHead_emptyFlag_cons bit tail _ _

/-- One-bit word equal to the head of `word`, defaulting to `false` on the
empty word. -/
def machineHeadBit (word : List Bool) : List Bool :=
  machineIfEmpty word [false]
    (machineIfHead word [true] [false])

theorem machineHeadBit_mem_FP : machineHeadBit ∈ Complexity.FP := by
  apply machineIfEmpty_mem_FP id_mem_FP
    (machineConst_mem_FP [false])
  exact machineIfHead_mem_FP id_mem_FP
    (machineConst_mem_FP [true]) (machineConst_mem_FP [false])

@[simp] theorem machineHeadBit_nil : machineHeadBit [] = [false] := by
  rfl

@[simp] theorem machineHeadBit_cons (bit : Bool) (tail : List Bool) :
    machineHeadBit (bit :: tail) = [bit] := by
  cases bit <;> simp [machineHeadBit]

@[simp] theorem machineHeadBit_length (word : List Bool) :
    (machineHeadBit word).length = 1 := by
  cases word <;> simp

end BeyondBethe
