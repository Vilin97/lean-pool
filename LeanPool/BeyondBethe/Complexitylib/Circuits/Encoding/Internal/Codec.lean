/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Encoding.Defs
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Correctness of the machine-facing circuit codec

This internal module proves that the proof-free encoding and iterative
evaluator in `Encoding.Defs` faithfully enforce their advertised syntactic
invariants.  Semantic agreement with typed circuit evaluation is deliberately
kept in a separate proof layer.
-/


public section

namespace Complexity

namespace CircuitCode

namespace NatCode

/-- The unary encoding of `n` uses exactly `n + 1` bits (`n` trues and a false). -/
@[simp] theorem length_encode (n : ℕ) : (encode n).length = n + 1 := by
  simp [encode]

private theorem decodeAux?_replicate_true (n acc : ℕ) (suffix : List Bool) :
    decodeAux? (List.replicate n true ++ false :: suffix) acc =
      some (acc + n, suffix) := by
  induction n generalizing acc with
  | zero => simp [decodeAux?]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [decodeAux?]
      rw [ih]
      congr 2
      omega

/-- A unary field can be decoded in front of an arbitrary suffix. -/
@[simp] theorem decodePrefix?_encode_append (n : ℕ) (suffix : List Bool) :
    decodePrefix? (encode n ++ suffix) = some (n, suffix) := by
  rw [decodePrefix?, encode, List.append_assoc]
  change decodeAux? (List.replicate n true ++ false :: suffix) 0 = _
  simpa using decodeAux?_replicate_true n 0 suffix

private theorem decodeAux?_sound {bits : List Bool} {acc n : ℕ}
    {suffix : List Bool} (h : decodeAux? bits acc = some (n, suffix)) :
    ∃ consumed : ℕ,
      n = acc + consumed ∧
        bits = List.replicate consumed true ++ false :: suffix := by
  induction bits generalizing acc with
  | nil => simp [decodeAux?] at h
  | cons bit bits ih =>
      cases bit with
      | false =>
          simp only [decodeAux?] at h
          cases h
          exact ⟨0, by simp⟩
      | true =>
          simp only [decodeAux?] at h
          obtain ⟨consumed, hn, hbits⟩ := ih h
          refine ⟨consumed + 1, by omega, ?_⟩
          rw [List.replicate_succ]
          simp [hbits]

private theorem decodeAux?_eq_none_iff (bits : List Bool) (acc : ℕ) :
    decodeAux? bits acc = none ↔
      bits = List.replicate bits.length true := by
  induction bits generalizing acc with
  | nil => simp [decodeAux?]
  | cons bit bits ih =>
      cases bit <;> simp [decodeAux?, ih, List.replicate_succ]

/-- Unary prefix decoding fails exactly when every available bit is a one,
so no zero terminator occurs. -/
theorem decodePrefix?_eq_none_iff (bits : List Bool) :
    decodePrefix? bits = none ↔
      bits = List.replicate bits.length true := by
  simpa [decodePrefix?] using decodeAux?_eq_none_iff bits 0

/-- Successful unary prefix decoding reconstructs the consumed input exactly. -/
theorem decodePrefix?_eq_some_iff (bits : List Bool) (n : ℕ) (suffix : List Bool) :
    decodePrefix? bits = some (n, suffix) ↔ bits = encode n ++ suffix := by
  constructor
  · intro h
    obtain ⟨consumed, hn, hbits⟩ := decodeAux?_sound h
    simp only [decodePrefix?] at h
    have : consumed = n := by omega
    subst consumed
    simpa [encode, List.append_assoc] using hbits
  · rintro rfl
    exact decodePrefix?_encode_append n suffix

end NatCode

namespace RawGate

/-- The Boolean well-formedness check agrees with the `WellFormedAt` predicate. -/
@[simp] theorem isWellFormedAt_eq_true (gate : RawGate) (available : ℕ) :
    gate.isWellFormedAt available = true ↔ gate.WellFormedAt available := by
  simp [isWellFormedAt]

/-- Decoding a gate's operation bit recovers its operation. -/
@[simp] theorem opOfBit_opBit (g : RawGate) : opOfBit g.opBit = g.op := by
  cases g with
  | mk op input₀ input₁ negated₀ negated₁ => cases op <;> rfl

/-- A gate encoding uses five header/delimiter bits plus one bit per unary
    input reference. -/
@[simp] theorem length_encode (g : RawGate) :
    g.encode.length = 5 + g.input₀ + g.input₁ := by
  simp [encode, NatCode.length_encode]
  omega

/-- A gate can be decoded in front of an arbitrary suffix. -/
@[simp] theorem decodePrefix?_encode_append (g : RawGate) (suffix : List Bool) :
    decodePrefix? (g.encode ++ suffix) = some (g, suffix) := by
  cases g with
  | mk op input₀ input₁ negated₀ negated₁ =>
      cases op <;>
        simp [encode, decodePrefix?, opBit, opOfBit, List.append_assoc]

/-- Successful gate-prefix decoding reconstructs the consumed input exactly. -/
theorem decodePrefix?_eq_some_iff (bits : List Bool) (gate : RawGate)
    (suffix : List Bool) :
    decodePrefix? bits = some (gate, suffix) ↔ bits = gate.encode ++ suffix := by
  constructor
  · intro h
    cases bits with
    | nil => simp [decodePrefix?] at h
    | cons op bits =>
        cases bits with
        | nil => simp [decodePrefix?] at h
        | cons negated₀ bits =>
            cases bits with
            | nil => simp [decodePrefix?] at h
            | cons negated₁ rest =>
                cases h₀ : NatCode.decodePrefix? rest with
                | none => simp [decodePrefix?, h₀] at h
                | some parsed₀ =>
                    obtain ⟨input₀, rest₀⟩ := parsed₀
                    cases h₁ : NatCode.decodePrefix? rest₀ with
                    | none => simp [decodePrefix?, h₀, h₁] at h
                    | some parsed₁ =>
                        obtain ⟨input₁, rest₁⟩ := parsed₁
                        simp only [decodePrefix?, h₀, h₁] at h
                        cases h
                        have hrest₀ :=
                          (NatCode.decodePrefix?_eq_some_iff rest input₀ rest₀).mp h₀
                        have hrest₁ :=
                          (NatCode.decodePrefix?_eq_some_iff rest₀ input₁ suffix).mp h₁
                        cases op <;>
                          simp [encode, opBit, opOfBit, hrest₀, hrest₁,
                            List.append_assoc]
  · rintro rfl
    exact decodePrefix?_encode_append gate suffix

end RawGate

namespace RawCircuit

/-- The Boolean well-formedness check agrees with the `WellFormed` predicate. -/
@[simp] theorem isWellFormed_eq_true (circuit : RawCircuit) (N : ℕ) :
    circuit.isWellFormed N = true ↔ circuit.WellFormed N := by
  simp [isWellFormed]

/-- Parsing an encoded gate list consumes exactly that list and leaves the
    caller-supplied suffix untouched. -/
@[simp] theorem decodeGates?_flatMap_encode_append
    (c : RawCircuit) (suffix : List Bool) :
    decodeGates? c.length (c.flatMap RawGate.encode ++ suffix) = some (c, suffix) := by
  induction c with
  | nil => simp [decodeGates?]
  | cons gate gates ih =>
      simp [decodeGates?, ih, List.append_assoc]

/-- A circuit prefix can be decoded in front of an arbitrary suffix. -/
@[simp] theorem decodePrefix?_encode_append (c : RawCircuit) (suffix : List Bool) :
    decodePrefix? (c.encode ++ suffix) = some (c, suffix) := by
  simp [decodePrefix?, encode, List.append_assoc]

/-- Exact decoding is a left inverse of circuit serialization. -/
@[simp] theorem decode?_encode (c : RawCircuit) : decode? c.encode = some c := by
  rw [show c.encode = c.encode ++ [] by simp]
  unfold decode?
  rw [decodePrefix?_encode_append]

/-- Exact decoding rejects any nonempty suffix after a canonical encoding. -/
theorem decode?_encode_append_eq_none (c : RawCircuit) {suffix : List Bool}
    (h : suffix ≠ []) : decode? (c.encode ++ suffix) = none := by
  simp [decode?, h]

/-- A circuit encoding consists of the unary gate count followed by the
    concatenated gate encodings. -/
@[simp] theorem length_encode (c : RawCircuit) :
    c.encode.length = c.length + 1 + (c.map fun gate => gate.encode.length).sum := by
  simp [encode, NatCode.length_encode, List.length_flatMap]

/-- Topological well-formedness of a nonempty gate list splits at its head. -/
theorem topologicallyWellFormed_cons (N : ℕ) (gate : RawGate) (gates : RawCircuit) :
    TopologicallyWellFormed N (gate :: gates) ↔
      gate.WellFormedAt N ∧ TopologicallyWellFormed (N + 1) gates := by
  constructor
  · intro h
    constructor
    · simpa [TopologicallyWellFormed] using h (0 : Fin (gate :: gates).length)
    · intro i
      have hi := h i.succ
      change (gates.get i).WellFormedAt (N + (i.val + 1)) at hi
      unfold RawGate.WellFormedAt at hi ⊢
      omega
  · rintro ⟨hgate, hgates⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hgate
    · have hj := hgates j
      change (gates.get j).WellFormedAt (N + (j.val + 1))
      unfold RawGate.WellFormedAt at hj ⊢
      omega

/-- Successful fixed-count gate decoding reconstructs the consumed input. -/
theorem decodeGates?_eq_some_iff (count : ℕ) (bits : List Bool)
    (circuit : RawCircuit) (suffix : List Bool) :
    decodeGates? count bits = some (circuit, suffix) ↔
      circuit.length = count ∧ bits = circuit.flatMap RawGate.encode ++ suffix := by
  constructor
  · intro h
    induction count generalizing bits circuit with
    | zero =>
        simp only [decodeGates?] at h
        cases h
        simp
    | succ count ih =>
        cases hgate : RawGate.decodePrefix? bits with
        | none => simp [decodeGates?, hgate] at h
        | some parsedGate =>
            obtain ⟨gate, rest⟩ := parsedGate
            cases hgates : decodeGates? count rest with
            | none => simp [decodeGates?, hgate, hgates] at h
            | some parsedGates =>
                obtain ⟨gates, final⟩ := parsedGates
                simp only [decodeGates?, hgate, hgates] at h
                cases h
                obtain ⟨hlen, hrest⟩ := ih rest gates hgates
                have hbits :=
                  (RawGate.decodePrefix?_eq_some_iff bits gate rest).mp hgate
                constructor
                · simp [hlen]
                · rw [hbits, hrest]
                  simp [List.append_assoc]
  · rintro ⟨hlen, rfl⟩
    subst count
    exact decodeGates?_flatMap_encode_append circuit suffix

/-- Successful circuit-prefix decoding reconstructs its canonical encoding. -/
theorem decodePrefix?_eq_some_iff (bits : List Bool) (circuit : RawCircuit)
    (suffix : List Bool) :
    decodePrefix? bits = some (circuit, suffix) ↔
      bits = circuit.encode ++ suffix := by
  constructor
  · intro h
    cases hcount : NatCode.decodePrefix? bits with
    | none => simp [decodePrefix?, hcount] at h
    | some parsedCount =>
        obtain ⟨count, rest⟩ := parsedCount
        simp only [decodePrefix?, hcount] at h
        have hbits :=
          (NatCode.decodePrefix?_eq_some_iff bits count rest).mp hcount
        obtain ⟨hlen, hrest⟩ :=
          (decodeGates?_eq_some_iff count rest circuit suffix).mp h
        rw [hbits, hrest]
        simp [encode, hlen, List.append_assoc]
  · rintro rfl
    exact decodePrefix?_encode_append circuit suffix

/-- Exact decoding succeeds precisely on canonical encodings. -/
theorem decode?_eq_some_iff_internal (bits : List Bool) (circuit : RawCircuit) :
    decode? bits = some circuit ↔ bits = circuit.encode := by
  constructor
  · intro h
    cases hprefix : decodePrefix? bits with
    | none => simp [decode?, hprefix] at h
    | some parsed =>
        obtain ⟨decoded, suffix⟩ := parsed
        cases suffix with
        | nil =>
            simp only [decode?, hprefix] at h
            cases h
            simpa using (decodePrefix?_eq_some_iff bits circuit []).mp hprefix
        | cons bit suffix => simp [decode?, hprefix] at h
  · rintro rfl
    exact decode?_encode circuit

/-- Running the iterative evaluator succeeds exactly for topological gate lists. -/
theorem evalAux?_isSome_iff (circuit : RawCircuit) (wires : Array Bool) :
    (evalAux? circuit wires).isSome ↔
      circuit.TopologicallyWellFormed wires.size := by
  induction circuit generalizing wires with
  | nil => simp [evalAux?, TopologicallyWellFormed]
  | cons gate gates ih =>
      rw [topologicallyWellFormed_cons]
      simp only [evalAux?]
      by_cases h₀ : gate.input₀ < wires.size
      · rw [Array.getElem?_eq_getElem h₀]
        by_cases h₁ : gate.input₁ < wires.size
        · rw [Array.getElem?_eq_getElem h₁]
          simp [ih, RawGate.WellFormedAt, h₀, h₁, Array.size_push]
        · rw [Array.getElem?_eq_none (by omega)]
          simp [RawGate.WellFormedAt, h₁]
      · rw [Array.getElem?_eq_none (by omega)]
        simp [RawGate.WellFormedAt, h₀]

/-- Successful iterative evaluation appends exactly one wire per gate. -/
theorem evalAux?_size {circuit : RawCircuit} {wires result : Array Bool}
    (h : evalAux? circuit wires = some result) :
    result.size = wires.size + circuit.length := by
  induction circuit generalizing wires result with
  | nil =>
      simp only [evalAux?] at h
      cases h
      simp
  | cons gate gates ih =>
      cases h₀ : wires[gate.input₀]? with
      | none => simp [evalAux?, h₀] at h
      | some value₀ =>
          cases h₁ : wires[gate.input₁]? with
          | none => simp [evalAux?, h₀, h₁] at h
          | some value₁ =>
              simp only [evalAux?, h₀, h₁] at h
              have hsize := ih h
              rw [Array.size_push] at hsize
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize

/-- Raw evaluation succeeds precisely for nonempty topologically ordered circuits. -/
theorem eval?_isSome_iff_internal (circuit : RawCircuit) (input : List Bool) :
    (circuit.eval? input).isSome ↔ circuit.WellFormed input.length := by
  cases circuit with
  | nil => simp [eval?, WellFormed]
  | cons gate gates =>
      constructor
      · intro h
        cases haux : evalAux? (gate :: gates) input.toArray with
        | none => simp [eval?, haux] at h
        | some result =>
            have htop :
                TopologicallyWellFormed input.toArray.size (gate :: gates) :=
              (evalAux?_isSome_iff (gate :: gates) input.toArray).mp (by simp [haux])
            constructor
            · simp
            · simpa using htop
      · rintro ⟨_, htop⟩
        have htop' :
            TopologicallyWellFormed input.toArray.size (gate :: gates) := by
          simpa using htop
        have hsome :=
          (evalAux?_isSome_iff (gate :: gates) input.toArray).mpr htop'
        obtain ⟨result, haux⟩ := Option.isSome_iff_exists.mp hsome
        have hsize := evalAux?_size haux
        have hlt :
            input.length + (gate :: gates).length - 1 < result.size := by
          rw [hsize, List.size_toArray]
          simp
        rw [eval?]
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, haux]
        change (result[input.length + (gate :: gates).length - 1]?).isSome
        rw [Array.getElem?_eq_getElem hlt]
        simp

end RawCircuit

/-- Code evaluation succeeds exactly when the input length is the declared arity,
the code is canonical, and the decoded raw circuit is well formed. -/
theorem evalCode_isSome_iff (N : ℕ) (code input : List Bool) :
    (evalCode N code input).isSome ↔
      input.length = N ∧
        ∃ circuit : RawCircuit,
          code = circuit.encode ∧ circuit.WellFormed N := by
  constructor
  · intro h
    by_cases hlen : input.length = N
    · cases hdecode : RawCircuit.decode? code with
      | none => simp [evalCode, hlen, hdecode] at h
      | some circuit =>
          have heval : (circuit.eval? input).isSome := by
            simpa [evalCode, hlen, hdecode] using h
          have hwellInput :=
            (RawCircuit.eval?_isSome_iff_internal circuit input).mp heval
          have hcode :=
            (RawCircuit.decode?_eq_some_iff_internal code circuit).mp hdecode
          exact ⟨hlen, circuit, hcode, by simpa [hlen] using hwellInput⟩
    · simp [evalCode, hlen] at h
  · rintro ⟨hlen, circuit, hcode, hwell⟩
    subst code
    have heval : (circuit.eval? input).isSome :=
      (RawCircuit.eval?_isSome_iff_internal circuit input).mpr
        (by simpa [hlen] using hwell)
    simpa [evalCode, hlen] using heval

namespace RawGate

/-- The first raw reference is the first typed input wire. -/
@[simp] theorem ofGate_input₀ {W : ℕ} (gate : Gate Basis.andOr2 W) :
    (RawGate.ofGate gate).input₀ = (gate.inputs ⟨0, by rw [fanIn_andOr2 gate]; omega⟩).val := by
  simp [RawGate.ofGate]

/-- The second raw reference is the second typed input wire. -/
@[simp] theorem ofGate_input₁ {W : ℕ} (gate : Gate Basis.andOr2 W) :
    (RawGate.ofGate gate).input₁ = (gate.inputs ⟨1, by rw [fanIn_andOr2 gate]; omega⟩).val := by
  simp [RawGate.ofGate]

/-- Erasing a typed gate's proofs never introduces an out-of-range reference. -/
theorem ofGate_wellFormedAt {W : ℕ} (gate : Gate Basis.andOr2 W) :
    (RawGate.ofGate gate).WellFormedAt W := by
  constructor <;> simp

end RawGate

namespace RawCircuit

/-- Translating a typed single-output circuit produces one raw gate per
internal gate, followed by its output gate. -/
@[simp] theorem length_ofCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (ofCircuit c).length = G + 1 := by
  simp [ofCircuit]

/-- Translation preserves the typed circuit's topological ordering. -/
theorem ofCircuit_topologicallyWellFormed {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (ofCircuit c).TopologicallyWellFormed N := by
  intro i
  rw [List.get_eq_getElem]
  change
    (List.ofFn (fun j : Fin G => RawGate.ofGate (c.gates j)) ++
      [RawGate.ofGate (c.outputs 0)])[i.val].WellFormedAt (N + i.val)
  by_cases hi : i.val < G
  · rw [List.getElem_append_left (by simp [hi])]
    rw [List.getElem_ofFn]
    constructor
    · rw [RawGate.ofGate_input₀]
      exact c.acyclic ⟨i.val, hi⟩
        ⟨0, by rw [fanIn_andOr2 (c.gates ⟨i.val, hi⟩)]; omega⟩
    · rw [RawGate.ofGate_input₁]
      exact c.acyclic ⟨i.val, hi⟩
        ⟨1, by rw [fanIn_andOr2 (c.gates ⟨i.val, hi⟩)]; omega⟩
  · have hieq : i.val = G := by
      have := i.isLt
      simp only [length_ofCircuit] at this
      omega
    rw [List.getElem_append_right (by simp; omega)]
    simpa [hieq] using RawGate.ofGate_wellFormedAt (c.outputs 0)

/-- Translation of a typed circuit is a valid raw single-output circuit. -/
theorem ofCircuit_wellFormed {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (ofCircuit c).WellFormed N := by
  constructor
  · intro hempty
    have hlen := length_ofCircuit c
    rw [hempty] at hlen
    simp at hlen
  · exact ofCircuit_topologicallyWellFormed c

private theorem sum_encode_length_le (N : ℕ) (circuit : RawCircuit)
    (hwell : circuit.TopologicallyWellFormed N) :
    (circuit.map fun gate => gate.encode.length).sum ≤
      circuit.length * (2 * (N + circuit.length) + 5) := by
  induction circuit generalizing N with
  | nil => simp
  | cons gate gates ih =>
      obtain ⟨hgate, hgates⟩ :=
        (topologicallyWellFormed_cons N gate gates).mp hwell
      have hgateLength : gate.encode.length ≤ 2 * N + 5 := by
        rw [RawGate.length_encode]
        unfold RawGate.WellFormedAt at hgate
        omega
      have htail := ih (N + 1) hgates
      let K := 2 * (N + (gate :: gates).length) + 5
      have htail' :
          (gates.map fun next => next.encode.length).sum ≤ gates.length * K := by
        simpa [K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      have hgateLength' : gate.encode.length ≤ K := by
        dsimp only [K]
        simp only [List.length_cons]
        omega
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        gate.encode.length + (gates.map fun next => next.encode.length).sum ≤
            K + gates.length * K := Nat.add_le_add hgateLength' htail'
        _ = (gates.length + 1) * K := by
          rw [Nat.add_mul]
          simp [Nat.add_comm]

/-- A generic topological raw circuit with `G` gates and input arity `N` has
quadratic-size unary encoding. -/
theorem encode_length_le (N G : ℕ) (circuit : RawCircuit)
    (hlen : circuit.length = G)
    (hwell : circuit.TopologicallyWellFormed N) :
    circuit.encode.length ≤ G + 1 + G * (2 * (N + G) + 5) := by
  subst G
  rw [RawCircuit.length_encode]
  exact Nat.add_le_add_left (sum_encode_length_le N circuit hwell) _

end RawCircuit

/-- A code produced from a typed circuit is evaluable exactly on inputs of
the circuit's declared arity. -/
theorem evalCode_encodeCircuit_isSome_iff {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : List Bool) :
    (evalCode N (encodeCircuit c) input).isSome ↔ input.length = N := by
  rw [evalCode_isSome_iff]
  constructor
  · exact And.left
  · intro hlen
    exact ⟨hlen, RawCircuit.ofCircuit c, rfl, RawCircuit.ofCircuit_wellFormed c⟩

/-- The unary encoding of a typed `G`-internal-gate circuit has a concrete
quadratic length bound. -/
theorem encodeCircuit_length_le {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (encodeCircuit c).length ≤
      (G + 1) + 1 + (G + 1) * (2 * (N + (G + 1)) + 5) := by
  exact RawCircuit.encode_length_le N (G + 1) (RawCircuit.ofCircuit c)
    (RawCircuit.length_ofCircuit c) (RawCircuit.ofCircuit_topologicallyWellFormed c)

/-- In the library's size convention, which counts internal and output gates
but not primary inputs or free negations, unary circuit codes have quadratic
length in the input arity and circuit size. -/
theorem encodeCircuit_length_le_size_internal {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (encodeCircuit c).length ≤
      1 + c.size * (2 * (N + c.size) + 6) := by
  calc
    (encodeCircuit c).length ≤
        (G + 1) + 1 + (G + 1) * (2 * (N + (G + 1)) + 5) :=
      encodeCircuit_length_le c
    _ = 1 + c.size * (2 * (N + c.size) + 6) := by
      simp only [Circuit.size]
      conv_rhs =>
        rw [show 2 * (N + (G + 1)) + 6 =
          (2 * (N + (G + 1)) + 5) + 1 by omega]
        rw [Nat.mul_add]
      omega

end CircuitCode

end Complexity
