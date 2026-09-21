/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Vec

/-!
# What the block scanners compute — proof internals

The two total parsers of a self-delimiting block — `Cobham.fstBlock` decodes the
leading block's payload, `Cobham.sndBlock` returns the suffix after it — and the
control states their scanners share. `Complexity.pairSplitCoreTM` handles only
valid pair inputs, so the total decoders need machines of their own; those are
`Internal.SndBlock`, `Internal.FstBlock` and `Internal.Cat`, one per machine.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- Decode the payload of the leading self-delimiting block: read doubled bits
until the `[false, true]` separator. On a valid pair `pair x y` this
returns `x` (see `fstBlock_pair`); on malformed input it returns the bits decoded
so far. This total, incremental form is what the `fstBlockTM` scanner computes. -/
def fstBlock : List Bool → List Bool
  | false :: false :: z => false :: fstBlock z
  | true :: true :: z => true :: fstBlock z
  | _ => []

/-- Take the suffix after the leading self-delimiting block (the second `unpair?`
component), or `[]` if the input is not a valid block. On `encodeVec` of a
nonempty vector this returns the head component `v 0`. -/
def sndBlock (z : List Bool) : List Bool :=
  match unpair? z with
  | some (_, s) => s
  | none => []

@[simp] theorem fstBlock_pair (x y : List Bool) : fstBlock (pair x y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> (rw [pair_cons_eq]; simp [fstBlock, ih])

@[simp] theorem sndBlock_pair (x y : List Bool) : sndBlock (pair x y) = y := by
  simp [sndBlock]

/-- Stripping the head component of an encoded vector yields the encoded tail.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`fstBlock_pair`.) -/
theorem fstBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    fstBlock (encodeVec v) = encodeVec (Fin.tail v) := by
  simp

/-- The suffix of an encoded vector is its head component.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`sndBlock_pair`.) -/
theorem sndBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    sndBlock (encodeVec v) = v 0 := by
  simp

/-- Control states of the block-decoding scanners. -/
inductive ScanPhase where
  | skip | scanA | scanBfalse | scanBtrue | emit | done
  deriving DecidableEq

instance : Fintype ScanPhase where
  elems := {.skip, .scanA, .scanBfalse, .scanBtrue, .emit, .done}
  complete := fun x => by cases x <;> simp

end Cobham

end Complexity
