/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryMul

/-! # Machine Natural Combinators -/

@[expose] public section

namespace BeyondBethe

open Complexity

/-!
# Combinators for binary-natural word machines

These wrappers keep later arithmetic schedules readable.  They do not add a
new computational primitive: each is just pairing followed by the verified
binary addition or multiplication machine.
-/

/-- Adds the binary outputs of two machines evaluated on the same input word. -/
def machineBinaryAddOf (f g : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineBinaryAddBits (pair (f word) (g word))

/-- Multiplies the binary outputs of two machines evaluated on the same input word. -/
def machineBinaryMulOf (f g : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  machineBinaryMulBits (pair (f word) (g word))

/-- Returns the binary natural-number code for the fixed constant `k`, independently of the
input. -/
def machineBinaryConst (k : ℕ) (_word : List Bool) : List Bool := k.bits

theorem machineBinaryAddOf_mem_FP {f g : List Bool → List Bool}
    (hf : f ∈ FP) (hg : g ∈ FP) : machineBinaryAddOf f g ∈ FP := by
  simpa only [machineBinaryAddOf] using!
    machineCompose_mem_FP (machinePair_mem_FP hf hg)
      machineBinaryAddBits_mem_FP

theorem machineBinaryMulOf_mem_FP {f g : List Bool → List Bool}
    (hf : f ∈ FP) (hg : g ∈ FP) : machineBinaryMulOf f g ∈ FP := by
  simpa only [machineBinaryMulOf] using!
    machineCompose_mem_FP (machinePair_mem_FP hf hg)
      machineBinaryMulBits_mem_FP

theorem machineBinaryConst_mem_FP (k : ℕ) : machineBinaryConst k ∈ FP := by
  simpa only [machineBinaryConst] using! machineConst_mem_FP k.bits

@[simp] theorem machineBinaryAddOf_natBits
    (f g : List Bool → List Bool) (word : List Bool) (a b : ℕ)
    (hf : f word = a.bits) (hg : g word = b.bits) :
    machineBinaryAddOf f g word = (a + b).bits := by
  rw [machineBinaryAddOf, hf, hg, machineBinaryAddBits_pair_natBits]

@[simp] theorem machineBinaryMulOf_natBits
    (f g : List Bool → List Bool) (word : List Bool) (a b : ℕ)
    (hf : f word = a.bits) (hg : g word = b.bits) :
    machineBinaryMulOf f g word = (a * b).bits := by
  rw [machineBinaryMulOf, hf, hg, machineBinaryMulBits_pair_natBits]

@[simp] theorem machineBinaryConst_apply (k : ℕ) (word : List Bool) :
    machineBinaryConst k word = k.bits := rfl

end BeyondBethe
