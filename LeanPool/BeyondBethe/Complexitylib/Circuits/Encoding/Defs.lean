/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Circuits.AndOrNot.Defs

/-!
# Machine-facing encoding of fan-in-two AND/OR circuits

This file defines a proof-free, on-tape representation of the library's
`Basis.andOr2` circuits.  A raw circuit is an ordered list of gates.  For an
input arity `N`, wires `0, ..., N - 1` are primary inputs and gate `i` produces
wire `N + i`.  Thus topological well-formedness says that both references of
gate `i` are strictly less than `N + i`.  The last gate is the sole output.

The evaluator is intentionally iterative.  It stores each wire value in an
array exactly once, so sharing in the circuit DAG does not cause the recursive
recomputation performed by the proof-oriented `Circuit.wireValue` definition.

The bit format is deterministic and self-delimiting.  Naturals use terminated
unary (`n` one-bits followed by a zero-bit), a gate stores three fixed bits and
two unary references, and a circuit starts with its unary gate count.  Exact
decoding rejects truncation and trailing garbage.  Unary references make the
format polynomially long in the input arity and number of gates; a binary
format can be added later without changing the raw circuit semantics.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

/-- A proof-free fan-in-two AND/OR gate.

`input₀` and `input₁` are absolute wire indices.  Negation flags are applied
before the AND/OR operation, matching `Gate.negated` in the typed circuit
model. -/
structure RawGate where
  /-- Whether the gate computes AND or OR of its (possibly negated) inputs. -/
  op : AndOrOp
  /-- Absolute wire index of the first input. -/
  input₀ : ℕ
  /-- Absolute wire index of the second input. -/
  input₁ : ℕ
  /-- Whether the first input value is negated before applying `op`. -/
  negated₀ : Bool
  /-- Whether the second input value is negated before applying `op`. -/
  negated₁ : Bool
  deriving DecidableEq

/-- A raw single-output circuit.  The output is the value of the last gate. -/
abbrev RawCircuit := List RawGate

namespace RawGate

/-- Both inputs of a gate must refer to already available wires. -/
def WellFormedAt (g : RawGate) (available : ℕ) : Prop :=
  g.input₀ < available ∧ g.input₁ < available

instance (g : RawGate) (available : ℕ) : Decidable (g.WellFormedAt available) :=
  by
    unfold WellFormedAt
    exact inferInstance

/-- Boolean checker corresponding to `WellFormedAt`. -/
def isWellFormedAt (g : RawGate) (available : ℕ) : Bool :=
  decide (g.WellFormedAt available)

/-- Evaluate a gate once its two (unnegated) input values are known. -/
def eval (g : RawGate) (value₀ value₁ : Bool) : Bool :=
  let value₀ := g.negated₀.xor value₀
  let value₁ := g.negated₁.xor value₁
  match g.op with
  | .and => value₀ && value₁
  | .or => value₀ || value₁

end RawGate

namespace RawCircuit

/-- Every gate reference points to a primary input or an earlier gate. -/
def TopologicallyWellFormed (N : ℕ) (c : RawCircuit) : Prop :=
  ∀ i : Fin c.length, (c.get i).WellFormedAt (N + i.val)

instance (N : ℕ) (c : RawCircuit) : Decidable (TopologicallyWellFormed N c) :=
  by
    unfold TopologicallyWellFormed
    exact Fintype.decidableForallFintype

/-- A valid single-output raw circuit is nonempty and topologically ordered. -/
def WellFormed (N : ℕ) (c : RawCircuit) : Prop :=
  c ≠ [] ∧ c.TopologicallyWellFormed N

instance (N : ℕ) (c : RawCircuit) : Decidable (WellFormed N c) :=
  by
    unfold WellFormed
    exact inferInstance

/-- Boolean checker for the explicit well-formedness predicate. -/
def isWellFormed (N : ℕ) (c : RawCircuit) : Bool :=
  decide (c.WellFormed N)

/-- Evaluate gates in order, appending each result to the memo array.

Failure means that a gate contains a forward or out-of-range reference. -/
def evalAux? : RawCircuit → Array Bool → Option (Array Bool)
  | [], wires => some wires
  | gate :: gates, wires => do
      let value₀ ← wires[gate.input₀]?
      let value₁ ← wires[gate.input₁]?
      evalAux? gates (wires.push (gate.eval value₀ value₁))

/-- Evaluate a raw circuit on a list of primary-input values.

The empty gate list has no designated output and is rejected. -/
def eval? (c : RawCircuit) (input : List Bool) : Option Bool := do
  if c.isEmpty then
    none
  else
    let wires ← evalAux? c input.toArray
    wires[input.length + c.length - 1]?

end RawCircuit

/-! ## Terminated unary fields -/

namespace NatCode

/-- Self-delimiting unary: `n` one-bits followed by a zero terminator. -/
def encode (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- Parse one terminated-unary prefix, returning the unconsumed suffix. -/
def decodeAux? : List Bool → ℕ → Option (ℕ × List Bool)
  | [], _ => none
  | false :: rest, acc => some (acc, rest)
  | true :: rest, acc => decodeAux? rest (acc + 1)

/-- Parse one terminated-unary prefix. -/
def decodePrefix? (bits : List Bool) : Option (ℕ × List Bool) :=
  decodeAux? bits 0

end NatCode

/-! ## Gate serialization -/

namespace RawGate

/-- Operation bit: one is AND and zero is OR. -/
def opBit (g : RawGate) : Bool :=
  match g.op with
  | .and => true
  | .or => false

/-- Decode the operation bit used by `opBit`. -/
def opOfBit : Bool → AndOrOp
  | true => .and
  | false => .or

/-- Encode a gate as operation, negation flags, then two unary references. -/
def encode (g : RawGate) : List Bool :=
  [g.opBit, g.negated₀, g.negated₁] ++
    NatCode.encode g.input₀ ++ NatCode.encode g.input₁

/-- Parse one gate prefix, returning the unconsumed suffix. -/
def decodePrefix? : List Bool → Option (RawGate × List Bool)
  | op :: negated₀ :: negated₁ :: rest =>
      match NatCode.decodePrefix? rest with
      | none => none
      | some (input₀, rest) =>
          match NatCode.decodePrefix? rest with
          | none => none
          | some (input₁, rest) =>
              some ({ op := opOfBit op, input₀, input₁, negated₀, negated₁ }, rest)
  | _ => none

end RawGate

/-! ## Circuit serialization -/

namespace RawCircuit

/-- Parse exactly `count` gate prefixes and return the remaining suffix. -/
def decodeGates? : ℕ → List Bool → Option (RawCircuit × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
      match RawGate.decodePrefix? bits with
      | none => none
      | some (gate, rest) =>
          match decodeGates? count rest with
          | none => none
          | some (gates, rest) => some (gate :: gates, rest)

/-- Serialize a circuit as its unary gate count followed by its gates. -/
def encode (c : RawCircuit) : List Bool :=
  NatCode.encode c.length ++ c.flatMap RawGate.encode

/-- Decode one circuit prefix and return the unconsumed suffix. -/
def decodePrefix? (bits : List Bool) : Option (RawCircuit × List Bool) :=
  match NatCode.decodePrefix? bits with
  | none => none
  | some (count, rest) => decodeGates? count rest

/-- Decode exactly one circuit.  Any trailing bits are rejected. -/
def decode? (bits : List Bool) : Option RawCircuit :=
  match decodePrefix? bits with
  | some (c, []) => some c
  | _ => none

end RawCircuit

/-- Translate a typed fan-in-two gate to the proof-free wire format. -/
def RawGate.ofGate {W : ℕ} (g : Gate Basis.andOr2 W) : RawGate := by
  have hfan : g.fanIn = 2 := fanIn_andOr2 g
  exact
    { op := g.op
      input₀ := (g.inputs ⟨0, by omega⟩).val
      input₁ := (g.inputs ⟨1, by omega⟩).val
      negated₀ := g.negated ⟨0, by omega⟩
      negated₁ := g.negated ⟨1, by omega⟩ }

/-- Translate a typed single-output circuit to an ordered raw circuit.

Internal gates retain their order and the typed output gate is appended as the
last raw gate. -/
def RawCircuit.ofCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : RawCircuit :=
  List.ofFn (fun i : Fin G => RawGate.ofGate (c.gates i)) ++
    [RawGate.ofGate (c.outputs 0)]

/-- Serialize a typed fan-in-two circuit as machine-facing bits. -/
def encodeCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : List Bool :=
  (RawCircuit.ofCircuit c).encode

/-- Decode and evaluate a circuit code against an input of exactly `N` bits. -/
def evalCode (N : ℕ) (code input : List Bool) : Option Bool := do
  if input.length = N then
    let circuit ← RawCircuit.decode? code
    circuit.eval? input
  else
    none

end CircuitCode

end Complexity
