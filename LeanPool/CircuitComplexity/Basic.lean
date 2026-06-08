/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Lattice

/-! # Boolean Circuit Complexity

This file defines Boolean circuits parameterized by a basis of operations and
establishes the circuit size complexity measure for Boolean functions.

## Main definitions

* `BitString` — a string of bits of a specific length
* `BoolFunFamily` — a family of Boolean functions indexed by input length
* `Basis` — a basis of Boolean operations with arity constraints
* `Circuit` — an acyclic Boolean circuit (well-formedness by construction)
* `CompleteBasis` — typeclass for functionally complete bases
* `Circuit.wireDepth` — depth of a wire in the circuit DAG
* `Circuit.outputDepth` — depth of a single output gate
* `Circuit.depth` — depth of a (possibly multi-output) circuit
* `Circuit.sizeComplexity` — minimum circuit size computing a given function

## Main results

* `Circuit.size_complexity_pos` — for complete bases, size complexity is positive
-/

namespace CircuitComplexity


/-- A BitString of length `n`. -/
abbrev BitString n := Fin n → Bool

/-- A family of Boolean functions indexed by input length `N`.

Each member maps `N`-bit strings to a single output bit. -/
abbrev BoolFunFamily := (N : Nat) → BitString N → Bool

/-- Arity constraint for operations in a basis. -/
inductive Arity where
  | unbounded
  | exactly (k : Nat)
  | upto (k : Nat)
  deriving Repr, DecidableEq

/-- Whether `n` satisfies an arity constraint. -/
def Arity.satisfiedBy : Arity → Nat → Prop
  | .unbounded, _ => True
  | .exactly k, n => n = k
  | .upto k, n => n ≤ k

instance (a : Arity) (n : Nat) : Decidable (a.satisfiedBy n) := by
  cases a <;> simp only [Arity.satisfiedBy] <;> exact inferInstance

/--
A basis of Boolean operations.

Each operation has an arity constraint and an evaluation function that computes
the output bit from any valid number of input bits.
-/
structure Basis where
  /-- The type of operations (e.g., AND, OR, NOT). -/
  Op : Type
  /-- The arity constraint for each operation. -/
  arity : Op → Arity
  /-- Evaluate an operation on `n` input bits, given that `n` satisfies the arity. -/
  eval : (op : Op) → (n : Nat) → (arity op).satisfiedBy n → BitString n → Bool

/--
A gate in a circuit over basis `B` with `W` wires available as inputs.
The gate's fan-in must satisfy the arity constraint of its operation, and each
input is wired to one of the `W` available wires.
-/
structure Gate (B : Basis) (W : Nat) where
  /-- The operation computed by this gate. -/
  op : B.Op
  /-- The number of inputs (fan-in) of this gate. -/
  fanIn : Nat
  /-- Proof that the fan-in satisfies the operation's arity constraint. -/
  arityOk : (B.arity op).satisfiedBy fanIn
  /-- Wiring: each gate input is connected to one of the `W` available wires. -/
  inputs : Fin fanIn → Fin W
  /-- Per-input negation flag. Negations are free in circuit complexity. -/
  negated : Fin fanIn → Bool

/-- Evaluate a gate given a wire-value assignment. -/
def Gate.eval (g : Gate B W) (wireVal : BitString W) : Bool :=
  B.eval g.op g.fanIn g.arityOk (fun i => (g.negated i).xor (wireVal (g.inputs i)))

/--
A Boolean circuit over basis `B` with `N` inputs, `M` outputs, and `G`
internal gates.

All gates reference wires from `Fin (N + G)`. The `acyclic` field ensures
that internal gate `i` only reads wires `0, …, N + i − 1`, preventing cycles.
-/
structure Circuit (B : Basis) (N M G : Nat) [NeZero N] [NeZero M] where
  /-- The `G` internal gates of the circuit. -/
  gates : Fin G → Gate B (N + G)
  /-- The `M` output gates of the circuit. -/
  outputs : Fin M → Gate B (N + G)
  /-- Acyclicity: internal gate `i` only reads wires `0, …, N + i − 1`. -/
  acyclic : ∀ (i : Fin G) (k : Fin (gates i).fanIn),
    ((gates i).inputs k).val < N + i.val

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Value of wire `w` when the circuit is fed `input`.

The first `N` wires carry the primary inputs. Wire `N + i` carries the
output of internal gate `i`. -/
def wireValue (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun k => (gate.negated k).xor (c.wireValue input (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

theorem wireValue_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireValue input w = input ⟨w.val, h⟩ := by
  unfold wireValue
  simp [h]

theorem wireValue_ge (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireValue input w =
      (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue input) := by
  unfold wireValue
  simp only [h, dite_false]
  rfl

/-- Depth of wire `w` in the circuit DAG.

Primary inputs have depth 0. Wire `N + i` (internal gate `i`) has depth
`1 + max over input wires`. -/
def wireDepth (c : Circuit B N M G) (w : Fin (N + G)) : Nat :=
  if h : w.val < N then
    0
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    1 + Fin.foldl gate.fanIn (fun acc k => max acc (c.wireDepth (gate.inputs k))) 0
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Primary input wires (index < N) have depth 0. -/
@[simp] theorem inputWireDepth (c : Circuit B N M G)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireDepth w = 0 := by
  unfold wireDepth; simp [h]

/-- Internal gate wires (index ≥ N) have depth 1 + max over their input wires.
Unfolds one step of `wireDepth` for the gate case. -/
theorem gateWireDepth (c : Circuit B N M G)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireDepth w =
      1 + Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, by omega⟩).inputs k))) 0 := by
  conv_lhs => unfold wireDepth
  simp only [h, dite_false]

/-- Depth contributed by a single output gate: one layer for the gate itself
plus the maximum `wireDepth` of its inputs. Always ≥ 1. -/
def outputDepth (c : Circuit B N M G) (j : Fin M) : Nat :=
  let outGate := c.outputs j
  1 + Fin.foldl outGate.fanIn (fun acc k => max acc (c.wireDepth (outGate.inputs k))) 0

/-- Depth of a circuit: the maximum `outputDepth` over all output gates. -/
def depth (c : Circuit B N M G) : Nat :=
  Fin.foldl M (fun acc j => max acc (c.outputDepth j)) 0

/-- Evaluate a circuit: map an `N`-bit input to an `M`-bit output. -/
def eval (c : Circuit B N M G) (input : BitString N) : BitString M :=
  fun j => (c.outputs j).eval (c.wireValue input)

/-- The size of a circuit is its total number of gates (internal + output). -/
def size (c : Circuit B N M G) : Nat :=
  G + M + (c.outputs 0).fanIn * 0

end Circuit

/-- A basis is complete if every Boolean function can be computed by some circuit over it. -/
class CompleteBasis (B : Basis) : Prop where
  complete : ∀ {N M} [NeZero N] [NeZero M] (f : BitString N → BitString M),
    ∃ G, ∃ c : Circuit B N M G, c.eval = f

/-- If every circuit over `B₁` can be simulated by a circuit over `B₂`
    (possibly with a different number of internal gates), then completeness
    of `B₁` implies completeness of `B₂`.

    This is the generic tool for proving new bases complete: show you can
    compile each gate of a known-complete basis into a subcircuit of the
    new basis. -/
theorem CompleteBasis.of_simulation (B₁ B₂ : Basis) [CompleteBasis B₁]
    (sim : ∀ {N M G} [NeZero N] [NeZero M] (c : Circuit B₁ N M G),
      ∃ G', ∃ c' : Circuit B₂ N M G', c'.eval = c.eval)
    : CompleteBasis B₂ where
  complete f := by
    obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B₁) f
    obtain ⟨G', c', hc'⟩ := sim c
    exact ⟨G', c', hc'.trans hc⟩

namespace Circuit
variable {B : Basis} {N : Nat} [NeZero N]

/-- The minimum circuit size over basis `B` computing a Boolean function `f`.

A single-output circuit `Circuit B N 1 G` computes `f` when
`(fun x => (c.eval x) 0) = f`. The size is `G + 1` (internal gates +
output gate). Returns 0 if no circuit over `B` computes `f`. -/
noncomputable def sizeComplexity
    (B : Basis) (f : BitString N → Bool) : Nat :=
  sInf {s | ∃ G, ∃ c : Circuit B N 1 G, c.size = s ∧ (fun x => (c.eval x) 0) = f}

private theorem size_complexity_set_nonempty [CompleteBasis B]
    (f : BitString N → Bool) :
    {s | ∃ G, ∃ c : Circuit B N 1 G, c.size = s ∧ (fun x => (c.eval x) 0) = f}.Nonempty := by
  obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) (fun x => (fun _ : Fin 1 => f x))
  refine ⟨c.size, G, c, rfl, ?_⟩
  funext x; have := congr_fun (congr_fun hc x) 0; exact this

/-- For a complete basis, circuit size complexity is always positive. -/
theorem size_complexity_pos [CompleteBasis B]
    (f : BitString N → Bool) :
    0 < sizeComplexity B f := by
  obtain ⟨_, _, hs, _⟩ := Nat.sInf_mem (size_complexity_set_nonempty (B := B) f)
  simp only [sizeComplexity]
  rw [← hs, size]
  omega

/-- Any circuit computing `f` has size at least `sizeComplexity B f`. -/
theorem size_complexity_le {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexity B f ≤ c.size :=
  Nat.sInf_le ⟨G, c, rfl, hf⟩

/-- For a complete basis, `sizeComplexity` is realized by some circuit. -/
theorem size_complexity_witness [CompleteBasis B]
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit B N 1 G,
      c.size = sizeComplexity B f ∧ (fun x => (c.eval x) 0) = f :=
  Nat.sInf_mem (size_complexity_set_nonempty (B := B) f)

end Circuit

end CircuitComplexity
