/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Internal.AON

/-! # Internal: Completeness of fan-in-2 AND/OR

This module proves `CompleteBasis Basis.andOr2` using the generic simulation
lemma `CompleteBasis.of_simulation`. The proof compiles any circuit over
`Basis.unboundedAON` into one over `Basis.andOr2` by decomposing each
unbounded fan-in gate into a chain of fan-in-2 gates.

## Strategy

Given a circuit `c : Circuit Basis.unboundedAON N M G`, we construct
`c' : Circuit Basis.andOr2 N M G'` with `c'.eval = c.eval`.

Each original gate with fan-in `k` is replaced by a chain of `chainLen k`
fan-in-2 gates:
- `k = 0`: one constant gate (dual-op trick: `OR(x₀, ¬x₀) = true`, etc.)
- `k = 1`: one passthrough gate (`op(x₀, x₀) = x₀`)
- `k ≥ 2`: `k - 1` gates chaining the inputs left-to-right

The new circuit's internal gates consist of chains for all original internal
gates followed by chains for all original output gates. The new output gates
are trivial passthroughs reading the last wire of each output chain.
-/

namespace CircuitComplexity


/-! ## AONOp extensions -/

/-- Dual operation: swaps AND ↔ OR. Used for constant-gate construction. -/
def AONOp.dual : AONOp → AONOp
  | .and => .or
  | .or => .and

/-- Identity element for fold: `true` for AND, `false` for OR. -/
def AONOp.identity : AONOp → Bool
  | .and => true
  | .or => false

/-- The binary operation corresponding to an AONOp. -/
def AONOp.binOp : AONOp → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)

lemma AONOp.eval_eq_foldl (op : AONOp) (n : Nat) (v : BitString n) :
    op.eval n v = Fin.foldl n (fun acc i => op.binOp acc (v i)) op.identity := by
  cases op <;> rfl

lemma AONOp.identity_binOp (op : AONOp) (b : Bool) : op.binOp op.identity b = b := by
  cases op <;> simp [AONOp.binOp, AONOp.identity]

lemma AONOp.binOp_self (op : AONOp) (b : Bool) : op.binOp b b = b := by
  cases op <;> cases b <;> rfl

lemma AONOp.binOp_assoc (op : AONOp) (a b c : Bool) :
    op.binOp (op.binOp a b) c = op.binOp a (op.binOp b c) := by
  cases op <;> simp [AONOp.binOp, Bool.and_assoc, Bool.or_assoc]

/-- The dual-op trick for constants: `OR(b, ¬b) = true`, `AND(b, ¬b) = false`. -/
lemma AONOp.dual_const (op : AONOp) (b : Bool) :
    op.dual.eval 2 (fun i => (if i.val = 0 then false else true).xor b) =
    op.identity := by
  cases op <;> cases b <;>
    simp [AONOp.dual, AONOp.identity, AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- A passthrough evaluates to the input value. -/
lemma AONOp.passthrough_eq (op : AONOp) (v : Bool) :
    op.eval 2 (fun _ => v) = v := by
  cases op <;> cases v <;>
    simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- `eval` on 0 inputs gives the identity. -/
lemma AONOp.eval_zero (op : AONOp) : op.eval 0 Fin.elim0 = op.identity := by
  cases op <;> simp [AONOp.eval, AONOp.identity, Fin.foldl_zero]

/-- `eval` on 1 input gives `identity op input`. -/
lemma AONOp.eval_one (op : AONOp) (v : Fin 1 → Bool) :
    op.eval 1 v = op.binOp op.identity (v 0) := by
  cases op <;> simp [AONOp.eval, AONOp.binOp, AONOp.identity, Fin.foldl_succ_last, Fin.foldl_zero]

namespace CompileAON

/-! ## Chain length and prefix sums -/

/-- Number of fan-in-2 gates needed to simulate one gate with `k` inputs. -/
def chainLen (k : Nat) : Nat := if k ≤ 1 then 1 else k - 1

@[simp] lemma chainLen_zero : chainLen 0 = 1 := rfl
@[simp] lemma chainLen_one : chainLen 1 = 1 := rfl

lemma chainLen_pos (k : Nat) : 0 < chainLen k := by
  unfold chainLen; split <;> omega

lemma chainLen_of_ge_two {k : Nat} (hk : 2 ≤ k) : chainLen k = k - 1 := by
  simp only [chainLen, show ¬(k ≤ 1) from by omega, ite_false]

/-- Prefix sum: `prefixSum f n = f 0 + f 1 + ⋯ + f (n-1)`. -/
def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

@[simp] lemma prefixSum_zero' (f : Nat → Nat) : prefixSum f 0 = 0 := rfl

lemma prefixSum_succ (f : Nat → Nat) (n : Nat) :
    prefixSum f (n + 1) = prefixSum f n + f n := rfl

lemma prefixSum_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    prefixSum f i ≤ prefixSum f j := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ ih => rw [prefixSum_succ]; omega

/-! ## Segment lookup -/

/-- Given a flat index into a segmented array, find the segment and position. -/
def segLookup (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    Nat × Nat :=
  match n with
  | 0 => absurd h (by simp)
  | n + 1 =>
    if hlt : idx < prefixSum f n then segLookup n f idx hlt
    else (n, idx - prefixSum f n)

lemma segLookup_fst_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).1 < n := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact Nat.lt_succ_of_lt (ih _)
    · exact Nat.lt_succ_of_le (Nat.le_refl n)

lemma segLookup_snd_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).2 < f (segLookup n f idx h).1 := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · rename_i h'
      dsimp only
      rw [prefixSum_succ] at h; omega

lemma segLookup_sum (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    prefixSum f (segLookup n f idx h).1 + (segLookup n f idx h).2 = idx := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · rename_i h'
      dsimp only; omega

/-! ## Wire layout definitions -/

variable {N M G : Nat} [NeZero N] [NeZero M]

/-- Chain size function for internal gates (0-padded beyond G). -/
def iChainF (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  if h : i < G then chainLen (c.gates ⟨i, h⟩).fanIn else 0

/-- Chain size function for output gates (0-padded beyond M). -/
def oChainF (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  if h : j < M then chainLen (c.outputs ⟨j, h⟩).fanIn else 0

/-- Total number of compiled gates contributed by the internal gates. -/
def iTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (iChainF c) G
/-- Total number of compiled gates contributed by the output gates. -/
def oTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (oChainF c) M

/-- Total internal gates in the compiled circuit. -/
def G' (c : Circuit Basis.unboundedAON N M G) : Nat := iTotal c + oTotal c

/-- Offset of the chain for internal gate `i`. -/
def iOffset (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  prefixSum (iChainF c) i

/-- Offset of the chain for output gate `j`. -/
def oOffset (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  iTotal c + prefixSum (oChainF c) j

lemma iChainF_eq (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iChainF c i = chainLen (c.gates ⟨i, hi⟩).fanIn := by simp [iChainF, hi]

lemma oChainF_eq (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oChainF c j = chainLen (c.outputs ⟨j, hj⟩).fanIn := by simp [oChainF, hj]

lemma iOffset_succ (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c (i + 1) = iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn := by
  simp [iOffset, prefixSum_succ, iChainF, hi]

lemma iOffset_chain_le_iTotal (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn ≤ iTotal c := by
  rw [← iOffset_succ c hi]; exact prefixSum_mono _ (by omega)

lemma oOffset_succ (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c (j + 1) = oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn := by
  unfold oOffset; rw [prefixSum_succ, oChainF_eq c hj]; omega

lemma oOffset_chain_le_G' (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn ≤ G' c := by
  suffices h : prefixSum (oChainF c) j + chainLen (c.outputs ⟨j, hj⟩).fanIn
      ≤ prefixSum (oChainF c) M by unfold oOffset G' iTotal oTotal at *; omega
  calc prefixSum (oChainF c) j + chainLen (c.outputs ⟨j, hj⟩).fanIn
      = prefixSum (oChainF c) j + oChainF c j := by rw [oChainF_eq c hj]
    _ = prefixSum (oChainF c) (j + 1) := (prefixSum_succ _ _).symm
    _ ≤ prefixSum (oChainF c) M := prefixSum_mono _ (by omega)

/-! ## Wire remapping -/

/-- Map an old wire index to its new position. Input wires are unchanged;
    internal gate `i` maps to the last gate of its chain. -/
def remapWire (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G)) :
    Fin (N + G' c) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else
    have hi : w.val - N < G := by omega
    have hle := iOffset_chain_le_iTotal c hi
    have hpos := chainLen_pos (c.gates ⟨w.val - N, hi⟩).fanIn
    ⟨N + iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, hi⟩).fanIn - 1, by
      unfold G'; omega⟩

lemma remapWire_input (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    (hw : w.val < N) : (remapWire c w).val = w.val := by
  simp [remapWire, hw]

lemma remapWire_gate (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    (remapWire c ⟨N + i, by omega⟩).val =
      N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1 := by
  unfold remapWire
  simp [show ¬(N + i < N) from by omega]

/-- If `w < N + i` in the old circuit, `remapWire w < N + iOffset i` in the new. -/
lemma remapWire_lt_of_lt (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    {i : Nat} (hi : i ≤ G) (hw : w.val < N + i) :
    (remapWire c w).val < N + iOffset c i := by
  unfold remapWire
  split
  · simp [iOffset]; omega
  · rename_i hNotLt
    push Not at hNotLt
    have hwN : w.val - N < i := by omega
    simp only []
    have key : iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, by omega⟩).fanIn
        ≤ iOffset c i := by
      calc iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, by omega⟩).fanIn
          = iOffset c (w.val - N + 1) := by rw [iOffset_succ c (by omega : w.val - N < G)]
        _ ≤ iOffset c i := prefixSum_mono _ (by omega)
    have := chainLen_pos (c.gates ⟨w.val - N, by omega⟩).fanIn
    omega

/-- `remapWire` maps to a wire that comes before any output chain. -/
lemma remapWire_lt_oOffset (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    (j : Nat) : (remapWire c w).val < N + oOffset c j := by
  have h := remapWire_lt_of_lt c w (Nat.le.refl) w.isLt
  have : iOffset c G = iTotal c := rfl
  unfold oOffset at *; omega

/-! ## Chain gate construction -/

/-- Helper: construct a function `Fin 2 → α` from two values. -/
def fin2 (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

@[simp] lemma fin2_zero (a b : α) : fin2 a b 0 = a := rfl
@[simp] lemma fin2_one (a b : α) : fin2 a b 1 = b := rfl

/-- Operation for the chain gate: dual-op for constants, same op otherwise. -/
private def mkChainOp (op : AONOp) (k : Nat) : AONOp :=
  if k = 0 then op.dual else op

/-- Input wires for the j-th chain gate. -/
private def mkChainInputs {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat)
    (hj : j < chainLen k) (hbase : base + chainLen k ≤ W) : Fin 2 → Fin W :=
  if hk0 : k = 0 then fun _ => ⟨0, hW⟩
  else if hk1 : k = 1 then fun _ => ri ⟨0, by omega⟩
  else if hj0 : j = 0 then fin2 (ri ⟨0, by omega⟩) (ri ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    have : j + 1 < k := by omega
    have : 1 ≤ j := by omega
    fin2 ⟨base + j - 1, by omega⟩ (ri ⟨j + 1, by omega⟩)

/-- Negation flags for the j-th chain gate. -/
private def mkChainNeg (k : Nat) (rn : Fin k → Bool) (j : Nat)
    (hj : j < chainLen k) : Fin 2 → Bool :=
  if hk0 : k = 0 then fin2 false true
  else if hk1 : k = 1 then fun _ => rn ⟨0, by omega⟩
  else if _ : j = 0 then fin2 (rn ⟨0, by omega⟩) (rn ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    fin2 false (rn ⟨j + 1, by omega⟩)

/-- Build the `j`-th fan-in-2 gate in a chain for an original gate.
    Components are split out so projections reduce without unfolding `dite`. -/
def mkChainGate {W : Nat} (hW : 0 < W) (op : AONOp) (k : Nat)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W) : Gate Basis.andOr2 W :=
  { op := mkChainOp op k, fanIn := 2, arityOk := rfl,
    inputs := mkChainInputs hW k ri base j hj hbase,
    negated := mkChainNeg k rn j hj }

/-- All inputs of a chain are strictly before `base + j` in the wire ordering. -/
private lemma mkChainInputs_lt {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W)
    (hri_lt : ∀ i, (ri i).val < base) (hbase_pos : 0 < base)
    (i : Fin 2) :
    (mkChainInputs hW k ri base j hj hbase i).val < base + j := by
  simp only [mkChainInputs]
  split_ifs with hk0 hk1 hj0
  · dsimp only; omega
  · simp only []; exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)
  · simp only [fin2]; split_ifs
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
  · simp only [fin2]; split_ifs
    · dsimp only; omega
    · exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)

/-! ## Compiled circuit -/

/-- Input wires for the compiled gate at flat index `idx`. -/
private def compileGateInputs (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Fin (N + G' c) :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainInputs (by omega) (c.gates ⟨seg.1, hi⟩).fanIn
      (fun i => remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i))
      (N + iOffset c seg.1) seg.2 hj
      (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainInputs (by omega) (c.outputs ⟨seg.1, hj⟩).fanIn
      (fun i => remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i))
      (N + oOffset c seg.1) seg.2 hk
      (by have := oOffset_chain_le_G' c hj; omega)

/-- Operation for the compiled gate at flat index `idx`. -/
private def compileGateOp (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) : AONOp :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    mkChainOp (c.gates ⟨seg.1, hi⟩).op (c.gates ⟨seg.1, hi⟩).fanIn
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    mkChainOp (c.outputs ⟨seg.1, hj⟩).op (c.outputs ⟨seg.1, hj⟩).fanIn

/-- Negation flags for the compiled gate at flat index `idx`. -/
private def compileGateNeg (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Bool :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainNeg (c.gates ⟨seg.1, hi⟩).fanIn (c.gates ⟨seg.1, hi⟩).negated seg.2 hj
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainNeg (c.outputs ⟨seg.1, hj⟩).fanIn (c.outputs ⟨seg.1, hj⟩).negated seg.2 hk

/-- Gate function for the compiled circuit. Components are separated so
    projections reduce without going through `dite`. -/
def compileGates (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Gate Basis.andOr2 (N + G' c) :=
  { op := compileGateOp c idx, fanIn := 2, arityOk := rfl,
    inputs := compileGateInputs c idx,
    negated := compileGateNeg c idx }

/-- Output gates: passthroughs reading the last wire of each output chain. -/
def compileOutputs (c : Circuit Basis.unboundedAON N M G) (j : Fin M) :
    Gate Basis.andOr2 (N + G' c) :=
  let lastWire : Fin (N + G' c) :=
    ⟨N + oOffset c j.val + chainLen (c.outputs j).fanIn - 1, by
      have hle : oOffset c j.val + chainLen (c.outputs j).fanIn ≤ G' c :=
        oOffset_chain_le_G' c j.isLt
      have hpos := chainLen_pos (c.outputs j).fanIn
      omega⟩
  { op := .and, fanIn := 2, arityOk := rfl,
    inputs := fun _ => lastWire, negated := fun _ => false }

/-- The compiled circuit over `Basis.andOr2`. -/
def compileFn (c : Circuit Basis.unboundedAON N M G) : Circuit Basis.andOr2 N M (G' c) where
  gates := compileGates c
  outputs := compileOutputs c
  acyclic := by
    intro idx k
    change (compileGateInputs c idx k).val < N + idx.val
    have hN : 0 < N := by have := NeZero.ne N; omega
    unfold compileGateInputs
    split
    case isTrue h =>
      -- Internal region: idx.val < iTotal c
      set seg := segLookup G (iChainF c) idx.val h with hseg_def
      have hi : seg.1 < G := segLookup_fst_lt G _ _ h
      have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
        rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
      have hsum : prefixSum (iChainF c) seg.1 + seg.2 = idx.val :=
        segLookup_sum G _ _ h
      have hiOff : iOffset c seg.1 = prefixSum (iChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i)).val <
          N + iOffset c seg.1 :=
        fun i => remapWire_lt_of_lt c _ (by omega) (c.acyclic ⟨seg.1, hi⟩ i)
      have hbase_eq : N + iOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hiOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hj
        (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
        hri_lt (by omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)
    case isFalse h =>
      -- Output region: idx.val ≥ iTotal c
      have hoff : idx.val - iTotal c < oTotal c := by
        have := idx.isLt; unfold G' at this; omega
      set seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff with hseg_def
      have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
      have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
        rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
      have hsum : prefixSum (oChainF c) seg.1 + seg.2 = idx.val - iTotal c :=
        segLookup_sum M _ _ hoff
      have hoOff : oOffset c seg.1 = iTotal c + prefixSum (oChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i)).val <
          N + oOffset c seg.1 :=
        fun i => remapWire_lt_oOffset c _ seg.1
      have hbase_eq : N + oOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hoOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hk
        (by have := oOffset_chain_le_G' c hj; omega)
        hri_lt (by rw [hoOff]; omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)

/-! ## Eval equivalence -/

/-- `segLookup` inverts `prefixSum`: if `idx = prefixSum f i + j` and `j < f i`,
    then `segLookup` returns `(i, j)`. -/
lemma segLookup_of_prefixSum (n : Nat) (f : Nat → Nat) (i j : Nat)
    (hi : i < n) (hj : j < f i)
    (h : prefixSum f i + j < prefixSum f n) :
    segLookup n f (prefixSum f i + j) h = (i, j) := by
  induction n with
  | zero => omega
  | succ n ihn =>
    simp only [segLookup]
    by_cases hlt : prefixSum f i + j < prefixSum f n
    · have hin : i < n := by
        by_contra h'
        push Not at h'
        have : n ≤ i := by omega
        have := prefixSum_mono f this
        omega
      simp [hlt, ihn hin hlt]
    · -- i = n
      push Not at hlt
      have : i = n := by
        by_contra h'
        have : i < n := by omega
        have := prefixSum_mono f (by omega : i + 1 ≤ n)
        rw [prefixSum_succ] at this
        omega
      subst this
      simp

/-- Partial fold: the result of folding `op.binOp` over the first `j` values. -/
private def partialFold (op : AONOp) (v : Fin k → Bool) (j : Nat) : Bool :=
  if h : j ≤ k then
    Fin.foldl j (fun acc i => op.binOp acc (v ⟨i.val, by omega⟩)) op.identity
  else op.eval k v

private lemma partialFold_zero (op : AONOp) (v : Fin k → Bool) :
    partialFold op v 0 = op.identity := by
  simp [partialFold, Fin.foldl_zero]

private lemma partialFold_succ (op : AONOp) (v : Fin k → Bool) (j : Nat) (hj : j < k) :
    partialFold op v (j + 1) = op.binOp (partialFold op v j) (v ⟨j, hj⟩) := by
  simp only [partialFold, show j + 1 ≤ k from by omega, show j ≤ k from by omega, dite_true]
  rw [Fin.foldl_succ_last]; congr 1

private lemma partialFold_one (op : AONOp) (v : Fin k → Bool) (hk : 0 < k) :
    partialFold op v 1 = op.binOp op.identity (v ⟨0, hk⟩) := by
  rw [partialFold_succ op v 0 hk, partialFold_zero]

private lemma partialFold_two (op : AONOp) (v : Fin k → Bool) (hk : 1 < k) :
    partialFold op v 2 = op.binOp (op.binOp op.identity (v ⟨0, by omega⟩)) (v ⟨1, hk⟩) := by
  rw [partialFold_succ op v 1 hk, partialFold_one op v (by omega)]

private lemma partialFold_full (op : AONOp) (v : Fin k → Bool) :
    partialFold op v k = op.eval k v := by
  simp only [partialFold, le_refl, dite_true, AONOp.eval_eq_foldl]

/-- The segLookup at `iOffset c i + j` returns `(i, j)`. -/
private lemma iSegLookup_eq (c : Circuit Basis.unboundedAON N M G)
    (i : Nat) (hi : i < G) (j : Nat) (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn)
    (h : iOffset c i + j < iTotal c := by
      have := iOffset_chain_le_iTotal c hi; omega) :
    segLookup G (iChainF c) (iOffset c i + j) h = (i, j) := by
  apply segLookup_of_prefixSum
  · exact hi
  · rw [iChainF_eq c hi]; exact hj

/-- The segLookup at `prefixSum (oChainF c) j' + p` returns `(j', p)`. -/
private lemma oSegLookup_eq (c : Circuit Basis.unboundedAON N M G)
    (j' : Nat) (hj' : j' < M) (p : Nat) (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn)
    (h : prefixSum (oChainF c) j' + p < oTotal c := by
      have := oOffset_chain_le_G' c hj'; unfold G' oOffset oTotal at *; omega) :
    segLookup M (oChainF c) (prefixSum (oChainF c) j' + p) h = (j', p) := by
  apply segLookup_of_prefixSum
  · exact hj'
  · rw [oChainF_eq c hj']; exact hp

/-- Evaluating a fan-in-2 gate: `op.eval 2 v = op.binOp (v 0) (v 1)`. -/
private lemma andOr2_eval (op : AONOp) (v : BitString 2) :
    op.eval 2 v = op.binOp (v 0) (v 1) := by
  cases op <;> simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero, AONOp.binOp]

/-- For k = 0: the single chain gate computes `op.identity`. -/
private lemma mkChainGate_eval_zero {W base : Nat} (op : AONOp) (ri : Fin 0 → Fin W)
  (rn : Fin 0 → Bool)
    (hW : 0 < W) (hj : 0 < chainLen 0) (hbase : base + chainLen 0 ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op 0 ri rn base 0 hj hbase).eval wv = op.identity := by
  simp only [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg,
             dite_true]
  exact AONOp.dual_const op (wv ⟨0, hW⟩)

/-- For k = 1: the single chain gate is a passthrough. -/
private lemma mkChainGate_eval_one {W base : Nat} (op : AONOp) (ri : Fin 1 → Fin W)
  (rn : Fin 1 → Bool)
    (hW : 0 < W) (hj : 0 < chainLen 1) (hbase : base + chainLen 1 ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op 1 ri rn base 0 hj hbase).eval wv =
    (rn ⟨0, by omega⟩).xor (wv (ri ⟨0, by omega⟩)) := by
  simp [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg,
        AONOp.passthrough_eq]

/-- For k ≥ 2, j = 0: first chain gate computes `op.binOp (v 0) (v 1)`. -/
private lemma mkChainGate_eval_ge2_zero {W base : Nat} (op : AONOp) {k : Nat} (hk : 2 ≤ k)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (hW : 0 < W) (hj : 0 < chainLen k) (hbase : base + chainLen k ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op k ri rn base 0 hj hbase).eval wv =
    op.binOp ((rn ⟨0, by omega⟩).xor (wv (ri ⟨0, by omega⟩)))
             ((rn ⟨1, by omega⟩).xor (wv (ri ⟨1, by omega⟩))) := by
  simp only [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg]
  simp only [show ¬(k = 0) from by omega, show ¬(k = 1) from by omega, ite_false, dite_false]
  rw [andOr2_eval]; simp [fin2]

/-- For k ≥ 2, j > 0: chain gate reads previous chain output and next original input. -/
private lemma mkChainGate_eval_ge2_succ {W base : Nat} (op : AONOp) {k : Nat} (hk : 2 ≤ k)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (hW : 0 < W) {j' : Nat} (hj : j' + 1 < chainLen k) (hbase : base + chainLen k ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op k ri rn base (j' + 1) hj hbase).eval wv =
    op.binOp (wv ⟨base + j', by have := chainLen_of_ge_two hk; omega⟩)
             ((rn ⟨j' + 2, by have := chainLen_of_ge_two hk; omega⟩).xor
              (wv (ri ⟨j' + 2, by have := chainLen_of_ge_two hk; omega⟩))) := by
  simp only [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg]
  simp only [show ¬(k = 0) from by omega, show ¬(k = 1) from by omega,
             show ¬(j' + 1 = 0) from by omega, ite_false, dite_false]
  rw [andOr2_eval]
  simp only [fin2, show ¬(1 : Fin 2).val = 0 from by decide,
             show (0 : Fin 2).val = 0 from by decide, ite_true, ite_false]
  simp only [Bool.false_xor]; congr 1

/-- The eval of the compiled gate at `iOffset c i + j` equals the chain gate's eval.
    This requires showing that `segLookup` at `iOffset c i + j` returns `(i, j)` and
    the resulting gate components match. -/
private lemma compileGate_eval_at_iOffset (c : Circuit Basis.unboundedAON N M G)
    (i : Nat) (hi : i < G) (j : Nat) (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn)
    (hidx : iOffset c i + j < G' c := by
      have := iOffset_chain_le_iTotal c hi; have := chainLen_pos (c.gates ⟨i, hi⟩).fanIn;
      unfold G'; omega)
    (wv : BitString (N + G' c)) :
    (compileGates c ⟨iOffset c i + j, hidx⟩).eval wv =
      (mkChainGate (by omega : 0 < N + G' c) (c.gates ⟨i, hi⟩).op (c.gates ⟨i, hi⟩).fanIn
        (fun p => remapWire c ((c.gates ⟨i, hi⟩).inputs p))
        (c.gates ⟨i, hi⟩).negated
        (N + iOffset c i) j hj
        (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)).eval wv := by
  -- Both sides compute the same Bool value. The compiled gate at this index uses
  -- segLookup which returns (i, j), giving the same op/inputs/negated.
  -- The technical challenge is that segLookup produces Fin G values with different
  -- proof terms than hi. We handle this by unfolding to AONOp.eval, then showing
  -- the function arguments agree at each Fin 2 element.
  have hInternal : iOffset c i + j < iTotal c := by
    have := iOffset_chain_le_iTotal c hi; omega
  have hSeg := iSegLookup_eq c i hi j hj hInternal
  have hSeg1 : (segLookup G (iChainF c) (iOffset c i + j) hInternal).1 = i := by rw [hSeg]
  have hSeg2 : (segLookup G (iChainF c) (iOffset c i + j) hInternal).2 = j := by rw [hSeg]
  -- All differences are segLookup results vs (i, j). Use convert at high depth
  -- and close subgoals with Fin.ext + iSegLookup_eq.
  unfold compileGates
  simp only [compileGateOp, compileGateInputs, compileGateNeg, Fin.val_mk,
             dif_pos hInternal, mkChainGate]
  convert rfl using 8
  all_goals first
    | rfl
    | exact (Fin.ext (by simp [iSegLookup_eq c i hi j hj])).symm
    | (simp [iSegLookup_eq c i hi j hj])

/-- The last chain gate for internal gate `i` evaluates to the original gate's eval. -/
private theorem lastChainValue_eq (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (i : Nat) (hi : i < G)
    (ih_outer : ∀ w : Fin (N + G), w.val < N + i →
      (compileFn c).wireValue input (remapWire c w) = c.wireValue input w) :
    (compileFn c).wireValue input
      ⟨N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1, by
        have := iOffset_chain_le_iTotal c hi
        have := chainLen_pos (c.gates ⟨i, hi⟩).fanIn
        unfold G'; omega⟩ =
    (c.gates ⟨i, hi⟩).eval (c.wireValue input) := by
  -- Reindex: N + x + y - 1 → N + x + (y - 1) to match chain_wire format
  have hle := iOffset_chain_le_iTotal c hi
  have hpos := chainLen_pos (c.gates ⟨i, hi⟩).fanIn
  suffices h : (compileFn c).wireValue input
      ⟨N + iOffset c i + (chainLen (c.gates ⟨i, hi⟩).fanIn - 1), by unfold G'; omega⟩ =
      (c.gates ⟨i, hi⟩).eval (c.wireValue input) by
    have heq : N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1 =
        N + iOffset c i + (chainLen (c.gates ⟨i, hi⟩).fanIn - 1) := by omega
    rwa [show (⟨N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1, _⟩ : Fin (N + G' c)) =
        ⟨N + iOffset c i + (chainLen (c.gates ⟨i, hi⟩).fanIn - 1), by unfold G'; omega⟩ from
        Fin.ext heq]
  -- Each chain wire evaluates to its compiled gate
  have chain_wire : ∀ j : Nat, (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn) →
      (compileFn c).wireValue input ⟨N + iOffset c i + j, by unfold G'; omega⟩ =
      (mkChainGate (by unfold G'; omega : 0 < N + G' c) (c.gates ⟨i, hi⟩).op (c.gates ⟨i, hi⟩).fanIn
        (fun p => remapWire c ((c.gates ⟨i, hi⟩).inputs p)) (c.gates ⟨i, hi⟩).negated
        (N + iOffset c i) j hj (by unfold G'; omega)).eval
        ((compileFn c).wireValue input) := by
    intro j hj
    rw [Circuit.wireValue_ge _ _ _ (by simp; omega)]
    change ((compileFn c).gates ⟨N + iOffset c i + j - N, _⟩).eval ((compileFn c).wireValue input)
      = _
    simp only [show N + iOffset c i + j - N = iOffset c i + j from by omega, compileFn]
    change (compileGates c ⟨iOffset c i + j, _⟩).eval ((compileFn c).wireValue input) = _
    exact compileGate_eval_at_iOffset c i hi j hj _ _
  rw [chain_wire (chainLen (c.gates ⟨i, hi⟩).fanIn - 1) (by omega)]
  -- Now: last chain gate eval = Gate.eval. Case split on fanIn.
  rcases Nat.eq_zero_or_pos (c.gates ⟨i, hi⟩).fanIn with hk0 | hk_pos
  · -- fanIn = 0: both sides equal op.identity
    trans (c.gates ⟨i, hi⟩).op.identity
    · -- LHS = identity: unfold and use dual_const
      simp only [hk0, chainLen_zero, Nat.sub_self,
                 mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                 dite_true, ite_true,
                 Gate.eval, Basis.andOr2, fin2]
      exact AONOp.dual_const _ _
    · -- RHS = identity: unfold Gate.eval, use AONOp.eval_eq_foldl, then simplify
      simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk0, Fin.foldl_zero]
  · rcases Nat.eq_or_lt_of_le hk_pos with hk1 | hk_ge2
    · -- fanIn = 1: passthrough
      have hk1' : (c.gates ⟨i, hi⟩).fanIn = 1 := hk1.symm
      -- Both sides equal (neg 0).xor (wireValue (inputs 0))
      trans ((c.gates ⟨i, hi⟩).negated ⟨0, by omega⟩).xor
            (c.wireValue input ((c.gates ⟨i, hi⟩).inputs ⟨0, by omega⟩))
      · -- LHS: chain gate evaluates to neg.xor(compiled_wireValue(remap(inputs 0)))
        simp only [hk1', chainLen_one, Nat.sub_self,
                   mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                   dite_true, dite_false,
                   Gate.eval, Basis.andOr2, AONOp.passthrough_eq,
                   show ¬(1 = 0) from by omega]
        congr 1
        exact ih_outer _ (c.acyclic ⟨i, hi⟩ ⟨0, by omega⟩)
      · -- RHS: gate eval on 1 input
        simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk1',
                   Fin.foldl_succ_last, Fin.foldl_zero, AONOp.identity_binOp]
        congr 1
    · -- fanIn ≥ 2
      have hcl : chainLen (c.gates ⟨i, hi⟩).fanIn = (c.gates ⟨i, hi⟩).fanIn - 1 :=
        chainLen_of_ge_two (by omega)
      let v := fun p : Fin (c.gates ⟨i, hi⟩).fanIn =>
        ((c.gates ⟨i, hi⟩).negated p).xor (c.wireValue input ((c.gates ⟨i, hi⟩).inputs p))
      have hv_remap : ∀ p : Fin (c.gates ⟨i, hi⟩).fanIn,
          ((c.gates ⟨i, hi⟩).negated p).xor
            ((compileFn c).wireValue input (remapWire c ((c.gates ⟨i, hi⟩).inputs p))) = v p := by
        intro p; show _ = _; congr 1
        exact ih_outer _ (c.acyclic ⟨i, hi⟩ p)
      have h_fold : ∀ j : Nat, (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn) →
          (mkChainGate (by unfold G'; omega : 0 < N + G' c) (c.gates ⟨i, hi⟩).op
            (c.gates ⟨i, hi⟩).fanIn
            (fun p => remapWire c ((c.gates ⟨i, hi⟩).inputs p)) (c.gates ⟨i, hi⟩).negated
            (N + iOffset c i) j hj (by unfold G'; omega)).eval
            ((compileFn c).wireValue input) = partialFold (c.gates ⟨i, hi⟩).op v (j + 2) := by
        intro j hj
        induction j with
        | zero =>
          rw [mkChainGate_eval_ge2_zero _ (by omega : 2 ≤ _)]
          rw [hv_remap ⟨0, by omega⟩, hv_remap ⟨1, by omega⟩]
          rw [partialFold_two _ v (by omega)]
          rw [AONOp.identity_binOp]
        | succ j' ih =>
          rw [mkChainGate_eval_ge2_succ _ (by omega : 2 ≤ _) _ _
            (by unfold G'; omega) hj (by unfold G'; omega)]
          rw [hv_remap ⟨j' + 2, by rw [hcl] at hj; omega⟩]
          rw [chain_wire j' (by rw [hcl] at hj ⊢; omega),
              ih (by rw [hcl] at hj ⊢; omega)]
          rw [partialFold_succ _ v (j' + 2) (by rw [hcl] at hj; omega)]
      rw [h_fold _ (by omega)]
      have hk_eq : chainLen (c.gates ⟨i, hi⟩).fanIn - 1 + 2 = (c.gates ⟨i, hi⟩).fanIn := by omega
      rw [hk_eq, partialFold_full]
      simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl]
      rfl

/-- Key lemma: `remapWire` values in the compiled circuit match the original. -/
theorem wireValue_remapWire (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (w : Fin (N + G)) :
    (compileFn c).wireValue input (remapWire c w) = c.wireValue input w := by
  have hmain : ∀ n, (hn : n < N + G) →
      (compileFn c).wireValue input (remapWire c ⟨n, hn⟩) = c.wireValue input ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      by_cases hw : n < N
      · rw [Circuit.wireValue_lt _ _ _ (by rw [remapWire_input c _ hw]; exact hw)]
        rw [Circuit.wireValue_lt _ _ _ hw]
        congr 1; exact Fin.ext (remapWire_input c _ hw)
      · push Not at hw
        have hi : n - N < G := by omega
        -- RHS = gate eval
        have rhs_eq : c.wireValue input ⟨n, hn⟩ =
            (c.gates ⟨n - N, hi⟩).eval (c.wireValue input) := by
          rw [Circuit.wireValue_ge]; simp; omega
        rw [rhs_eq]
        -- LHS: remapWire maps to last chain wire
        rw [show ⟨n, hn⟩ = (⟨N + (n - N), by omega⟩ : Fin (N + G)) from Fin.ext (by simp; omega)]
        rw [show remapWire c ⟨N + (n - N), by omega⟩ =
            ⟨N + iOffset c (n - N) + chainLen (c.gates ⟨n - N, hi⟩).fanIn - 1, by
            have := iOffset_chain_le_iTotal c hi; have := chainLen_pos
              (c.gates ⟨n - N, hi⟩).fanIn; unfold G'; omega⟩
            from Fin.ext (by rw [remapWire_gate c hi])]
        exact lastChainValue_eq c input (n - N) hi (fun w' hw' => by
          have hwlt : w'.val < n := by
            have : w'.val < N + (n - N) := hw'
            omega
          exact ih w'.val hwlt w'.isLt)
  exact hmain w.val w.isLt

/-- The eval of the compiled gate at output offset position equals the chain gate's eval. -/
private lemma compileGate_eval_at_oOffset (c : Circuit Basis.unboundedAON N M G)
    (j' : Nat) (hj' : j' < M) (p : Nat) (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn)
    (hidx : iTotal c + prefixSum (oChainF c) j' + p < G' c := by
      have := oOffset_chain_le_G' c hj'; unfold oOffset G' at *; omega)
    (wv : BitString (N + G' c)) :
    (compileGates c ⟨iTotal c + prefixSum (oChainF c) j' + p, hidx⟩).eval wv =
      (mkChainGate (by omega : 0 < N + G' c) (c.outputs ⟨j', hj'⟩).op (c.outputs ⟨j', hj'⟩).fanIn
        (fun i => remapWire c ((c.outputs ⟨j', hj'⟩).inputs i))
        (c.outputs ⟨j', hj'⟩).negated
        (N + oOffset c j') p hp
        (by have := oOffset_chain_le_G' c hj'; omega)).eval wv := by
  have hNotInternal : ¬(iTotal c + prefixSum (oChainF c) j' + p < iTotal c) := by omega
  have hoff : (iTotal c + prefixSum (oChainF c) j' + p) - iTotal c = prefixSum (oChainF c) j' + p
    := by omega
  have hoff_lt : prefixSum (oChainF c) j' + p < oTotal c := by
    have := oOffset_chain_le_G' c hj'; unfold G' oOffset oTotal at *; omega
  have hSeg := oSegLookup_eq c j' hj' p hp hoff_lt
  unfold compileGates
  simp only [compileGateOp, compileGateInputs, compileGateNeg, Fin.val_mk,
             dif_neg hNotInternal, mkChainGate]
  convert rfl using 8
  all_goals first
    | rfl
    | (simp only [hoff]; exact (Fin.ext (by simp [oSegLookup_eq c j' hj' p hp])).symm)
    | (simp only [hoff]; simp [oSegLookup_eq c j' hj' p hp])

/-- The last chain gate for output `j` evaluates to the original output gate's eval. -/
private theorem lastOutputChainValue_eq (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (j' : Nat) (hj' : j' < M) :
    (compileFn c).wireValue input
      ⟨N + oOffset c j' + chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1, by
        have := oOffset_chain_le_G' c hj'
        have := chainLen_pos (c.outputs ⟨j', hj'⟩).fanIn
        omega⟩ =
    (c.outputs ⟨j', hj'⟩).eval (c.wireValue input) := by
  have hle := oOffset_chain_le_G' c hj'
  have hpos := chainLen_pos (c.outputs ⟨j', hj'⟩).fanIn
  -- Reindex: N + x + y - 1 → N + x + (y - 1)
  suffices h : (compileFn c).wireValue input
      ⟨N + oOffset c j' + (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1), by omega⟩ =
      (c.outputs ⟨j', hj'⟩).eval (c.wireValue input) by
    have heq : N + oOffset c j' + chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1 =
        N + oOffset c j' + (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1) := by omega
    rwa [show (⟨N + oOffset c j' + chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1, _⟩ : Fin (N + G' c)) =
        ⟨N + oOffset c j' + (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1), by omega⟩ from
        Fin.ext heq]
  -- Each chain wire evaluates to its compiled gate
  have chain_wire : ∀ p : Nat, (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn) →
      (compileFn c).wireValue input ⟨N + oOffset c j' + p, by omega⟩ =
      (mkChainGate (by omega : 0 < N + G' c) (c.outputs ⟨j', hj'⟩).op (c.outputs ⟨j', hj'⟩).fanIn
        (fun i => remapWire c ((c.outputs ⟨j', hj'⟩).inputs i)) (c.outputs ⟨j', hj'⟩).negated
        (N + oOffset c j') p hp (by omega)).eval
        ((compileFn c).wireValue input) := by
    intro p hp
    rw [Circuit.wireValue_ge _ _ _ (by simp; omega)]
    change ((compileFn c).gates ⟨N + oOffset c j' + p - N, _⟩).eval
      ((compileFn c).wireValue input) = _
    simp only [show N + oOffset c j' + p - N = oOffset c j' + p from by omega, compileFn]
    have hoOff : oOffset c j' = iTotal c + prefixSum (oChainF c) j' := rfl
    change (compileGates c ⟨iTotal c + prefixSum (oChainF c) j' + p, _⟩).eval
      ((compileFn c).wireValue input) = _
    exact compileGate_eval_at_oOffset c j' hj' p hp _ _
  rw [chain_wire (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1) (by omega)]
  -- Case split on fanIn
  rcases Nat.eq_zero_or_pos (c.outputs ⟨j', hj'⟩).fanIn with hk0 | hk_pos
  · -- fanIn = 0
    trans (c.outputs ⟨j', hj'⟩).op.identity
    · simp only [hk0, chainLen_zero, Nat.sub_self,
                 mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                 dite_true, ite_true,
                 Gate.eval, Basis.andOr2, fin2]
      exact AONOp.dual_const _ _
    · simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk0, Fin.foldl_zero]
  · rcases Nat.eq_or_lt_of_le hk_pos with hk1 | hk_ge2
    · -- fanIn = 1
      have hk1' : (c.outputs ⟨j', hj'⟩).fanIn = 1 := hk1.symm
      trans ((c.outputs ⟨j', hj'⟩).negated ⟨0, by omega⟩).xor
            (c.wireValue input ((c.outputs ⟨j', hj'⟩).inputs ⟨0, by omega⟩))
      · simp only [hk1', chainLen_one, Nat.sub_self,
                   mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                   dite_true, dite_false,
                   Gate.eval, Basis.andOr2, AONOp.passthrough_eq,
                   show ¬(1 = 0) from by omega]
        congr 1
        exact wireValue_remapWire c input _
      · simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk1',
                   Fin.foldl_succ_last, Fin.foldl_zero, AONOp.identity_binOp]
        congr 1
    · -- fanIn ≥ 2
      have hcl : chainLen (c.outputs ⟨j', hj'⟩).fanIn = (c.outputs ⟨j', hj'⟩).fanIn - 1 :=
        chainLen_of_ge_two (by omega)
      let v := fun p : Fin (c.outputs ⟨j', hj'⟩).fanIn =>
        ((c.outputs ⟨j', hj'⟩).negated p).xor (c.wireValue input ((c.outputs ⟨j', hj'⟩).inputs p))
      have hv_remap : ∀ p : Fin (c.outputs ⟨j', hj'⟩).fanIn,
          ((c.outputs ⟨j', hj'⟩).negated p).xor
            ((compileFn c).wireValue input (remapWire c ((c.outputs ⟨j', hj'⟩).inputs p))) = v p
              := by
        intro p; show _ = _; congr 1
        exact wireValue_remapWire c input _
      have h_fold : ∀ p : Nat, (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn) →
          (mkChainGate (by omega : 0 < N + G' c) (c.outputs ⟨j', hj'⟩).op
            (c.outputs ⟨j', hj'⟩).fanIn
            (fun i => remapWire c ((c.outputs ⟨j', hj'⟩).inputs i)) (c.outputs ⟨j', hj'⟩).negated
            (N + oOffset c j') p hp (by omega)).eval
            ((compileFn c).wireValue input) = partialFold (c.outputs ⟨j', hj'⟩).op v (p + 2) := by
        intro p hp
        induction p with
        | zero =>
          rw [mkChainGate_eval_ge2_zero _ (by omega : 2 ≤ _)]
          rw [hv_remap ⟨0, by omega⟩, hv_remap ⟨1, by omega⟩]
          rw [partialFold_two _ v (by omega)]
          rw [AONOp.identity_binOp]
        | succ p' ih =>
          rw [mkChainGate_eval_ge2_succ _ (by omega : 2 ≤ _) _ _
            (by omega) hp (by omega)]
          rw [hv_remap ⟨p' + 2, by rw [hcl] at hp; omega⟩]
          rw [chain_wire p' (by rw [hcl] at hp ⊢; omega),
              ih (by rw [hcl] at hp ⊢; omega)]
          rw [partialFold_succ _ v (p' + 2) (by rw [hcl] at hp; omega)]
      rw [h_fold _ (by omega)]
      have hk_eq : chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1 + 2 = (c.outputs ⟨j', hj'⟩).fanIn :=
        by omega
      rw [hk_eq, partialFold_full]
      simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl]
      rfl

theorem compile_eval (c : Circuit Basis.unboundedAON N M G) :
    (compileFn c).eval = c.eval := by
  funext input j
  -- LHS: (compileFn c).eval input j = (compileOutputs c j).eval ((compileFn c).wireValue input)
  change (compileOutputs c j).eval ((compileFn c).wireValue input) =
       (c.outputs j).eval (c.wireValue input)
  -- The output gate is a passthrough AND(lastWire, lastWire) with no negation
  simp only [compileOutputs, Gate.eval, Basis.andOr2, AONOp.eval_two_and, Bool.and_self,
             Bool.false_xor]
  -- Now we need: wireValue at the last output chain wire = original output gate eval
  exact lastOutputChainValue_eq c input j.val j.isLt

end CompileAON

/-- Fan-in-2 AND/OR is functionally complete. -/
instance : CompleteBasis Basis.andOr2 :=
  CompleteBasis.of_simulation Basis.unboundedAON Basis.andOr2
    fun c => ⟨CompileAON.G' c, CompileAON.compileFn c, CompileAON.compile_eval c⟩

end CircuitComplexity
