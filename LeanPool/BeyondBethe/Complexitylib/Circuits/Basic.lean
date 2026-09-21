/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Lattice

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
* `Circuit.Realizable` — whether a function is computed by some circuit over a basis
* `Circuit.sizeComplexityWithTop` — generic minimum size, with `⊤` for unrealizable functions
* `Circuit.sizeComplexity` — natural-valued minimum size over a complete basis

## Main results

* `Circuit.sizeComplexity_pos` — for complete bases, size complexity is positive
-/


@[expose] public section

namespace Complexity

/-- A BitString of length `n`. -/
abbrev BitString n := Fin n → Bool

/-- A family of Boolean functions indexed by input length `N`.

Each member maps `N`-bit strings to a single output bit. -/
abbrev BoolFunFamily := (N : Nat) → BitString N → Bool

/-- Arity constraint for operations in a basis. -/
inductive Arity where
  /-- Any number of inputs is allowed. -/
  | unbounded
  /-- Exactly `k` inputs are required. -/
  | exactly (k : Nat)
  /-- At most `k` inputs are allowed. -/
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
  /-- The basis operation this gate computes. -/
  op : B.Op
  /-- The number of inputs this gate reads. -/
  fanIn : Nat
  /-- Proof that `fanIn` satisfies the arity constraint of `op`. -/
  arityOk : (B.arity op).satisfiedBy fanIn
  /-- The wire each of the gate's `fanIn` inputs is connected to. -/
  inputs : Fin fanIn → Fin W
  /-- Per-input negation flag. Negations are free under this library's size
      convention. -/
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
  /-- The internal gates; gate `i` drives wire `N + i`. -/
  gates : Fin G → Gate B (N + G)
  /-- The output gates; output bit `j` is the value of gate `outputs j`. -/
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

/-- On primary input wires (index < `N`), `wireValue` is the corresponding input bit. -/
theorem wireValue_of_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireValue input w = input ⟨w.val, h⟩ := by
  unfold wireValue
  simp [h]

/-- On internal gate wires (index ≥ `N`), `wireValue` is the evaluation of gate
`w − N` on the values of its input wires. -/
theorem wireValue_of_not_lt (c : Circuit B N M G) (input : BitString N)
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
@[simp] theorem wireDepth_of_lt (c : Circuit B N M G)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireDepth w = 0 := by
  unfold wireDepth; simp [h]

/-- Internal gate wires (index ≥ N) have depth 1 + max over their input wires.
Unfolds one step of `wireDepth` for the gate case. -/
theorem wireDepth_of_not_lt (c : Circuit B N M G)
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

/-- The library's circuit size: internal gates plus output gates.

Primary input vertices are not counted, and the negation flags on gate inputs
have zero cost. Some texts instead count input vertices and explicit NOT gates;
those conventions agree only up to additive/linear overhead, not on exact size
bounds. -/
-- The circuit argument is unused by design: `size` is determined by the
-- indices, and the argument exists purely to enable `c.size` dot notation.
def size (_ : Circuit B N M G) : Nat := G + M

end Circuit

/-- A basis is complete if every Boolean function can be computed by some circuit over it. -/
class CompleteBasis (B : Basis) : Prop where
  /-- Every function `BitString N → BitString M` is the evaluation of some circuit over `B`. -/
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

/-- A Boolean function is realizable over `B` when some single-output circuit
over `B` computes it. -/
def Realizable (B : Basis) (f : BitString N → Bool) : Prop :=
  ∃ G, ∃ c : Circuit B N 1 G, (fun x => (c.eval x) 0) = f

/-- Sizes of all single-output circuits over `B` that realize `f`. -/
def realizationSizes (B : Basis) (f : BitString N → Bool) : Set Nat :=
  {s | ∃ G, ∃ c : Circuit B N 1 G,
    c.size = s ∧ (fun x => (c.eval x) 0) = f}

/-- The minimum circuit size over an arbitrary basis, as an extended natural.

A single-output circuit `Circuit B N 1 G` has size `G + 1`. The value is `⊤`
exactly when no circuit over `B` computes `f`; thus an unrealizable function
cannot be confused with a zero-size function. -/
noncomputable def sizeComplexityWithTop
    (B : Basis) (f : BitString N → Bool) : WithTop Nat :=
  sInf ((fun s : Nat => (s : WithTop Nat)) '' realizationSizes B f)

/-- The minimum circuit size over a complete basis `B` computing `f`.

This natural-valued interface requires completeness so that the set of
realizing circuits is nonempty. Use `sizeComplexityWithTop` when the basis may
be incomplete. -/
-- Completeness is an intentional API precondition. The infimum expression
-- itself does not inspect the selected witness.
noncomputable def sizeComplexity
    (B : Basis) [CompleteBasis B] (f : BitString N → Bool) : Nat :=
  sInf (realizationSizes B f)

private theorem realizationSizes_nonempty [CompleteBasis B]
    (f : BitString N → Bool) :
    (realizationSizes B f).Nonempty := by
  obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) (fun x => (fun _ : Fin 1 => f x))
  refine ⟨c.size, G, c, rfl, ?_⟩
  funext x
  exact congrFun (congrFun hc x) 0

/-- Any circuit computing `f` gives an upper bound on the generic extended
size complexity. -/
theorem sizeComplexityWithTop_le {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexityWithTop B f ≤ c.size := by
  apply sInf_le
  exact ⟨c.size, ⟨G, c, rfl, hf⟩, rfl⟩

/-- Generic size complexity is infinite exactly for functions that cannot be
realized over the chosen basis. -/
theorem sizeComplexityWithTop_eq_top_iff
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f = ⊤ ↔ ¬ Realizable B f := by
  rw [sizeComplexityWithTop, sInf_eq_top]
  constructor
  · intro h hrealizable
    obtain ⟨G, c, hc⟩ := hrealizable
    have htop := h (c.size : WithTop Nat)
      ⟨c.size, ⟨G, c, rfl, hc⟩, rfl⟩
    exact (WithTop.coe_ne_top : (c.size : WithTop Nat) ≠ ⊤) htop
  · intro h a ha
    obtain ⟨s, ⟨G, c, _, hc⟩, rfl⟩ := ha
    exact (h ⟨G, c, hc⟩).elim

/-- Generic size complexity is finite exactly for realizable functions. -/
theorem sizeComplexityWithTop_ne_top_iff
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f ≠ ⊤ ↔ Realizable B f := by
  rw [ne_eq, sizeComplexityWithTop_eq_top_iff]
  simp only [not_not]

/-- Whenever the generic size complexity is finite, a circuit realizes its
minimum value. -/
theorem sizeComplexityWithTop_witness
    (f : BitString N → Bool)
    (hfinite : sizeComplexityWithTop B f ≠ ⊤) :
    ∃ G, ∃ c : Circuit B N 1 G,
      (c.size : WithTop Nat) = sizeComplexityWithTop B f ∧
        (fun x => (c.eval x) 0) = f := by
  have hrealizable := (sizeComplexityWithTop_ne_top_iff (B := B) f).mp hfinite
  obtain ⟨G₀, c₀, hc₀⟩ := hrealizable
  have hset : ((fun s : Nat => (s : WithTop Nat)) ''
      realizationSizes B f).Nonempty :=
    ⟨c₀.size, c₀.size, ⟨G₀, c₀, rfl, hc₀⟩, rfl⟩
  have hmem := csInf_mem hset
  obtain ⟨s, ⟨G, c, hs, hc⟩, hcoe⟩ := hmem
  exact ⟨G, c, hs ▸ hcoe, hc⟩

/-- Over a complete basis, the generic extended measure agrees with the
natural-valued minimum. -/
theorem sizeComplexityWithTop_eq_coe [CompleteBasis B]
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f = (sizeComplexity B f : WithTop Nat) := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨sizeComplexity B f,
      Nat.sInf_mem (realizationSizes_nonempty (B := B) f), rfl⟩
  · apply le_sInf
    rintro _ ⟨s, hs, rfl⟩
    exact WithTop.coe_le_coe.mpr (Nat.sInf_le hs)

/-- For a complete basis, circuit size complexity is always positive. -/
theorem sizeComplexity_pos [CompleteBasis B]
    (f : BitString N → Bool) :
    0 < sizeComplexity B f := by
  obtain ⟨_, _, hs, _⟩ := Nat.sInf_mem (realizationSizes_nonempty (B := B) f)
  simp only [sizeComplexity]
  rw [← hs, size]
  omega

/-- Any circuit computing `f` has size at least `sizeComplexity B f`. -/
theorem sizeComplexity_le [CompleteBasis B] {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexity B f ≤ c.size :=
  Nat.sInf_le ⟨G, c, rfl, hf⟩

/-- For a complete basis, `sizeComplexity` is realized by some circuit. -/
theorem sizeComplexity_witness [CompleteBasis B]
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit B N 1 G,
      c.size = sizeComplexity B f ∧ (fun x => (c.eval x) 0) = f :=
  Nat.sInf_mem (realizationSizes_nonempty (B := B) f)

end Circuit

end Complexity
