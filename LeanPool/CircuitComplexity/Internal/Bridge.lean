/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.AON.Defs
import LeanPool.CircuitComplexity.Internal.CircDesc
import LeanPool.CircuitComplexity.Internal.Schnorr

/-! # Internal: Bridge from CircDesc to Circuit Model

This internal module connects the `CircDesc` counting model to the general
`Circuit` model by proving that circuits over `Basis.andOr2` encode faithfully
into circuit descriptors.

The public theorems `shannon_lower_bound_circuit` and
`schnorr_lower_bound_circuit` are accessible through `Circ.Shannon` and
`Circ.Schnorr` respectively.
-/

namespace CircuitComplexity


/-! ## Encoding -/

/-- Encode a `Basis.andOr2` gate as a `GateSlot`. -/
def encodeGate {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W') : GateSlot W' :=
  have h2 := andOr2_fanIn g
  (match g.op with | .and => true | .or => false,
   (⟨(g.inputs ⟨0, by omega⟩).val, by omega⟩,
    ⟨(g.inputs ⟨1, by omega⟩).val, by omega⟩),
   (g.negated ⟨0, by omega⟩, g.negated ⟨1, by omega⟩))

/-- Encode a circuit over `Basis.andOr2` as a circuit descriptor.
    Internal gates map to positions `0..G-1`; the output gate to position `G`. -/
def circuitToDesc {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : CircDesc N (G + 1) := fun i =>
  if h : i.val < G then
    encodeGate (c.gates ⟨i.val, h⟩) (by omega : N + G ≤ N + (G + 1))
  else
    encodeGate (c.outputs 0) (by omega : N + G ≤ N + (G + 1))

/-! ## Semantic Equivalence -/

/-- Gate evaluation over `Basis.andOr2` matches the `GateSlot` encoding semantics. -/
private theorem gate_eval_eq_slot {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W')
    (wireVal : Fin W → Bool) (wireVal' : Fin W' → Bool)
    (hwv : ∀ w : Fin W, wireVal w = wireVal' ⟨w.val, by omega⟩) :
    g.eval wireVal =
      let (isAnd, (w1, w2), (n1, n2)) := encodeGate g hW
      if isAnd then
        (n1.xor (wireVal' w1)) && (n2.xor (wireVal' w2))
      else
        (n1.xor (wireVal' w1)) || (n2.xor (wireVal' w2)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;> simp [Gate.eval, Basis.andOr2, encodeGate, AONOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, hwv]

/-- Wire values agree between `Circuit.wireValue` and `wireValD` for wires
    in the range `0..N+G-1`. -/
theorem wireValue_eq_wireValD {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (input : BitString N) (w : Fin (N + G)) :
    c.wireValue input w =
      wireValD (circuitToDesc c) input ⟨w.val, by omega⟩ := by
  by_cases hwN : w.val < N
  · -- Primary input wire
    rw [Circuit.wireValue_lt _ _ _ hwN]
    conv_rhs => unfold wireValD
    simp [hwN]
  · -- Gate wire
    push Not at hwN
    have hG : w.val - N < G := by omega
    rw [Circuit.wireValue_ge c input w (by omega)]
    -- h2 first, so omega can resolve Fin bounds
    have h2 : (c.gates ⟨w.val - N, hG⟩).fanIn = 2 := andOr2_fanIn _
    -- Acyclicity (before set, so set rewrites them consistently)
    have hacyc0 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨0, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨0, by omega⟩
      simp only [] at h; omega
    have hacyc1 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨1, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨1, by omega⟩
      simp only [] at h; omega
    -- set gate — rewrites h2, hacyc0, hacyc1 and the goal
    set gate := c.gates ⟨w.val - N, hG⟩ with gate_def
    -- IH for the two input wires
    have ih0 := wireValue_eq_wireValD c input
      ⟨(gate.inputs ⟨0, by omega⟩).val, by omega⟩
    have ih1 := wireValue_eq_wireValD c input
      ⟨(gate.inputs ⟨1, by omega⟩).val, by omega⟩
    -- Unfold wireValD one step
    conv_rhs => unfold wireValD
    simp only [show ¬((⟨w.val, (by omega : w.val < N + (G + 1))⟩ : Fin (N + (G + 1))).val < N)
      from by simp; omega, dite_false]
    -- circuitToDesc lookup
    simp only [circuitToDesc, show (⟨w.val - N, (by omega : w.val - N < G + 1)⟩ :
      Fin (G + 1)).val < G from hG, dite_true, encodeGate, Fin.val_mk]
    -- Normalize all c.gates ⟨↑w-N, _⟩ to gate (for any proof, via Fin.ext)
    have hgate : ∀ h : w.val - N < G, c.gates ⟨w.val - N, h⟩ = gate :=
      fun h => (congrArg c.gates (Fin.ext rfl)).trans gate_def.symm
    simp_rw [hgate]
    -- Guards pass by acyclicity
    simp only [hacyc0, hacyc1, ↓reduceIte]
    -- Rewrite wireValD back to wireValue using IH
    rw [← ih0, ← ih1]
    -- The RHS has (c.gates ⟨↑w-N,⋯⟩).negated with an opaque Fin proof.
    -- Prove .negated equality using a helper that transports across the gate equality.
    suffices h : ∀ (h' : ↑w - N < G) (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j =
          gate.negated (j.cast (show (c.gates ⟨↑w - N, h'⟩).fanIn = gate.fanIn by
            rw [hgate h'])) by
      -- First apply h to rewrite all .negated terms to gate.negated (Fin.cast ...)
      simp only [h, Fin.cast_mk]
      -- The LHS is gate.eval and the RHS is the 2-input expansion.
      -- Use gate_eval_eq_slot which produces encodeGate terms,
      -- then show encodeGate gate matches the RHS
      have := gate_eval_eq_slot gate (show N + G ≤ N + G by omega)
        (c.wireValue input) (c.wireValue input) (fun _ => rfl)
      rw [this]; clear this
      -- Now both sides use encodeGate gate; unfold and simplify
      simp [encodeGate]
    intro h' j
    exact (show ∀ (g : Gate Basis.andOr2 (N + G)) (heq : g = c.gates ⟨↑w - N, h'⟩)
        (hfanIn : (c.gates ⟨↑w - N, h'⟩).fanIn = g.fanIn)
        (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j = g.negated (j.cast hfanIn)
      from fun g heq _ j => by subst heq; rfl)
      _ (hgate h').symm (by simp [hgate h']) j
  termination_by w.val

/-- Circuit evaluation agrees with descriptor evaluation. -/
theorem circuit_eval_eq_evalD {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (fun x => (c.eval x) 0) = evalD (Nat.succ_pos G) (circuitToDesc c) := by
  funext x
  simp only [Circuit.eval, evalD]
  rw [gate_eval_eq_slot (c.outputs 0) (by omega : N + G ≤ N + (G + 1))
    (c.wireValue x) _ (fun w => wireValue_eq_wireValD c x w)]
  conv_rhs => unfold wireValD
  simp only []
  simp only [circuitToDesc, show ¬((⟨N + G.succ - 1 - N, (by omega : N + G.succ - 1 - N < G + 1)⟩ :
    Fin (G + 1)).val < G) from by simp, dite_false]
  have h2 := andOr2_fanIn (c.outputs 0)
  simp only [encodeGate, Fin.val_mk,
    show ((c.outputs 0).inputs ⟨0, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨0, by omega⟩).isLt (by omega),
    show ((c.outputs 0).inputs ⟨1, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨1, by omega⟩).isLt (by omega),
    ite_true]
  simp only [show ¬(N + G.succ - 1 < N) from by omega, dite_false]

/-! ## Padding -/

/-- Pad a descriptor to a larger size by appending copy gates.
    Each padded gate is `OR(last_output, last_output)` which copies the
    original output value. -/
def padDesc {N s : Nat} (d : CircDesc N s) (s' : Nat) (hs : 0 < s) (h : s ≤ s') :
    CircDesc N s' := fun i =>
  if hi : i.val < s then
    let slot := d ⟨i.val, hi⟩
    (slot.1,
     (⟨slot.2.1.1.val, by omega⟩, ⟨slot.2.1.2.val, by omega⟩),
     slot.2.2)
  else
    -- Copy gate: OR(last_original_output, last_original_output)
    (false, (⟨N + s - 1, by omega⟩, ⟨N + s - 1, by omega⟩), (false, false))

-- Helper: wireValD agrees on original wires
private theorem wireValD_padDesc_lt {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : w.val < N + s) :
    wireValD (padDesc d s' hs h) x w =
      wireValD d x ⟨w.val, hw⟩ := by
  by_cases hwN : w.val < N
  · simp [wireValD, hwN]
  · push Not at hwN
    have hi : w.val - N < s := by omega
    conv_lhs => unfold wireValD
    simp only [show ¬(w.val < N) from by omega, dite_false]
    conv_rhs => unfold wireValD
    simp only [show ¬(w.val < N) from by omega, dite_false]
    -- Both sides look up the gate at index w.val - N
    simp only [padDesc, show (w.val - N) < s from hi, dite_true]
    have hw1 : (d ⟨↑w - N, hi⟩).2.1.1.val < N + s := (d ⟨↑w - N, hi⟩).2.1.1.isLt
    have hw2 : (d ⟨↑w - N, hi⟩).2.1.2.val < N + s := (d ⟨↑w - N, hi⟩).2.1.2.isLt
    congr 1 <;> (congr 1 <;> (first | rfl | (congr 1; split_ifs with hlt <;> (
      first
      | exact wireValD_padDesc_lt d hs h x _ (by first | exact hw1 | exact hw2)
      | rfl))))
  termination_by w.val

-- Helper: padded wire values equal the last original output
private theorem wireValD_padDesc_ge {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : N + s ≤ w.val) :
    wireValD (padDesc d s' hs h) x w =
      wireValD d x ⟨N + s - 1, by omega⟩ := by
  conv_lhs => unfold wireValD
  simp only [show ¬(w.val < N) from by omega, dite_false]
  -- The gate at index w.val - N ≥ s, so padDesc gives the copy gate
  simp only [padDesc, show ¬(w.val - N < s) from by omega, dite_false]
  -- Copy gate: OR(N+s-1, N+s-1) with no negation
  simp only [Bool.false_xor, Bool.or_self]
  -- The wire N+s-1 < w, so the guard passes
  simp only [show (N + s - 1 : Nat) < w.val from by omega, ↓reduceIte]
  -- Now we need wireValD (padDesc ...) x ⟨N+s-1, _⟩ = wireValD d x ⟨N+s-1, _⟩
  have hlt : N + s - 1 < N + s := by omega
  exact wireValD_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ hlt

/-- Padding preserves evaluation. -/
theorem evalD_padDesc {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (hs' : 0 < s') :
    evalD hs' (padDesc d s' hs h) = evalD hs d := by
  funext x
  simp only [evalD]
  by_cases hsle : N + s ≤ N + s' - 1
  · -- s < s': the last wire is in the padded region
    rw [wireValD_padDesc_ge d hs h x ⟨N + s' - 1, by omega⟩ (by omega)]
  · -- s = s': both point to the same wire
    push Not at hsle
    have : s = s' := by omega
    subst this
    exact wireValD_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ (by omega)

/-! ## Main Theorems -/

/-- **Shannon lower bound for circuits**: for N ≥ 6, there exists a Boolean
    function on N inputs that cannot be computed by any fan-in-2 AND/OR
    circuit of size at most 2^N/(5N). -/
theorem shannon_lower_bound_circuit (N : Nat) [NeZero N] (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ G (c : Circuit Basis.andOr2 N 1 G),
        G + 1 ≤ 2 ^ N / (5 * N) →
        (fun x => (c.eval x) 0) ≠ f := by
  obtain ⟨f, hf⟩ := shannon_lower_bound N hN
  exact ⟨f, fun G c hsize habs => by
    have hspos := s_pos N hN
    have hG1 : 0 < G + 1 := Nat.succ_pos G
    let d := circuitToDesc c
    let d' := padDesc d (2 ^ N / (5 * N)) hG1 hsize
    have h1 : evalD hspos d' = evalD hG1 d := evalD_padDesc d hG1 hsize hspos
    have h2 : (fun x => (c.eval x) 0) = evalD hG1 d := circuit_eval_eq_evalD c
    have h3 : evalD hspos d' = f := by rw [h1, ← h2, habs]
    exact hf d' h3⟩

/-- **Schnorr's lower bound for circuits**: any fan-in-2 AND/OR circuit
    computing XOR_N (or its complement) has at least 2(N-1) internal gates,
    i.e., G + 1 (total gates including output) ≥ 2N - 1. -/
theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x))
    (hN : 1 ≤ N) : G + 2 ≥ 2 * N := by
  have hG1 : 0 < G + 1 := Nat.succ_pos G
  have h := circuit_eval_eq_evalD c
  have heval' : ∀ x, evalD hG1 (circuitToDesc c) x = comp.xor (Schnorr.xorBool N x) :=
    fun x => (congr_fun h x).symm ▸ heval x
  exact Schnorr.xor_lower_bound_2 N (G + 1) hG1 (circuitToDesc c) comp heval' hN

end CircuitComplexity
