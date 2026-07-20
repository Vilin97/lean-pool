/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import LeanPool.CircuitComplexity.Basic

/-! # Internal: Circuit Descriptors and Shannon Counting Bound

This internal module defines the circuit descriptor model used for counting
arguments, and proves the Shannon lower bound for this model. The public
theorem `shannon_lower_bound_circuit` (which speaks in terms of `Circuit`)
is in `Circ.Internal.Bridge`.
-/

namespace CircuitComplexity


/-! ## Gate and Circuit Descriptors -/

/-- A gate in a fan-in-2 circuit over wires `0..W-1`.
    Encodes `(isAnd, (wire1, wire2), (neg1, neg2))`.
    Semantics: if `isAnd` then `(neg1 ⊕ v1) && (neg2 ⊕ v2)`
                          else `(neg1 ⊕ v1) || (neg2 ⊕ v2)` -/
abbrev GateSlot (W : Nat) := Bool × (Fin W × Fin W) × (Bool × Bool)

/-- A circuit descriptor with `N` primary inputs and `s` gates.
    Wires `0..N-1` are primary inputs; wires `N..N+s-1` are gate outputs. -/
abbrev CircDesc (N s : Nat) := Fin s → GateSlot (N + s)

/-! ## Wire and Circuit Evaluation -/

/-- Evaluate wire `w` in a circuit descriptor.
    Primary input wires return the corresponding input bit.
    Gate wires evaluate their gate, with forward references defaulting to `false`. -/
def wireValD {N s : Nat} (d : CircDesc N s) (input : BitString N)
    (w : Fin (N + s)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hi : w.val - N < s := by omega
    let (isAnd, (w1, w2), (n1, n2)) := d ⟨w.val - N, hi⟩
    let v1 := n1.xor (if w1.val < w.val then wireValD d input ⟨w1.val, by omega⟩ else false)
    let v2 := n2.xor (if w2.val < w.val then wireValD d input ⟨w2.val, by omega⟩ else false)
    if isAnd then v1 && v2 else v1 || v2
termination_by w.val

/-- Evaluate a circuit descriptor: the output is the value of the last gate. -/
def evalD {N s : Nat} (hs : 0 < s) (d : CircDesc N s) : BitString N → Bool :=
  fun input => wireValD d input ⟨N + s - 1, by omega⟩

/-! ## Cardinality Lemmas -/

theorem card_gateSlot (W : Nat) : Fintype.card (GateSlot W) = 8 * W ^ 2 := by
  simp [GateSlot, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]; ring

theorem card_circDesc (N s : Nat) :
    Fintype.card (CircDesc N s) = (8 * (N + s) ^ 2) ^ s := by
  simp only [CircDesc, Fintype.card_fun, Fintype.card_fin]; rw [card_gateSlot]

theorem card_bool_fun (N : Nat) :
    Fintype.card (BitString N → Bool) = 2 ^ 2 ^ N := by
  simp [BitString]

/-! ## Arithmetic Lemmas -/

/-- For `N ≥ 6`, the exponential `2^N` dominates `5N`. -/
theorem five_n_le_two_pow (N : Nat) (hN : 6 ≤ N) : 5 * N ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases h : 6 ≤ n
    · have h5 : 5 ≤ 2 ^ n :=
        le_trans (by norm_num : 5 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]; ring
      have ihn := ih h
      omega
    · interval_cases n <;> simp_all

/-- The gate count `s = 2^N / (5N)` is positive for `N ≥ 6`. -/
theorem s_pos (N : Nat) (hN : 6 ≤ N) : 0 < 2 ^ N / (5 * N) :=
  Nat.div_pos (five_n_le_two_pow N hN) (by omega)

/-- The total wire count `N + s` is less than `2^N`. -/
theorem n_plus_s_lt (N : Nat) (hN : 6 ≤ N) :
    N + 2 ^ N / (5 * N) < 2 ^ N := by
  have h5n := five_n_le_two_pow N hN
  have hN5 : N ≤ 2 ^ N / 5 := by
    rwa [Nat.le_div_iff_mul_le (by omega : 0 < 5), Nat.mul_comm]
  have hS5 : 2 ^ N / (5 * N) ≤ 2 ^ N / 5 :=
    Nat.div_le_div_left (by omega : 5 ≤ 5 * N) (by omega : 0 < 5)
  have h4 : 2 * (2 ^ N / 5) < 2 ^ N := by
    have hle := Nat.mul_div_le_mul_div_assoc 2 (2 ^ N) 5
    have hlt : 2 * 2 ^ N / 5 < 2 ^ N := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 5)]
      linarith
    omega
  omega

/-- The exponent `(2N+3) * s` is less than `2^N`, which ensures the
    power-of-two bound in the main arithmetic inequality. -/
theorem mul_s_lt_two_pow (N : Nat) (hN : 6 ≤ N) :
    (2 * N + 3) * (2 ^ N / (5 * N)) < 2 ^ N := by
  calc (2 * N + 3) * (2 ^ N / (5 * N))
      < (5 * N) * (2 ^ N / (5 * N)) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (s_pos N hN)
    _ ≤ 2 ^ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _

/-- **Key arithmetic bound**: the number of circuit descriptors of size
    `s = 2^N/(5N)` is strictly less than the number of Boolean functions on
    N inputs. The proof chains:

    1. `N + s < 2^N`
    2. `8(N+s)² < 2^(2N+3)`
    3. `(2N+3)·s < 2^N`
    4. `(2^(2N+3))^s = 2^((2N+3)·s) < 2^(2^N)` -/
theorem arith_bound (N : Nat) (hN : 6 ≤ N) :
    (8 * (N + 2 ^ N / (5 * N)) ^ 2) ^ (2 ^ N / (5 * N)) < 2 ^ 2 ^ N := by
  set s := 2 ^ N / (5 * N)
  have hspos : 0 < s := s_pos N hN
  have h1 : 8 * (N + s) ^ 2 < 2 ^ (2 * N + 3) := by
    have hns : N + s < 2 ^ N := n_plus_s_lt N hN
    have hsq : (N + s) ^ 2 < (2 ^ N) ^ 2 := Nat.pow_lt_pow_left hns (by omega)
    have : 2 ^ (2 * N + 3) = 8 * (2 ^ N) ^ 2 := by rw [← Nat.pow_mul, Nat.pow_add]; ring_nf
    omega
  have h2 : (2 * N + 3) * s < 2 ^ N := mul_s_lt_two_pow N hN
  calc (8 * (N + s) ^ 2) ^ s
      < (2 ^ (2 * N + 3)) ^ s := Nat.pow_lt_pow_left h1 (by omega)
    _ = 2 ^ ((2 * N + 3) * s) := by rw [← Nat.pow_mul]
    _ < 2 ^ (2 ^ N) := Nat.pow_lt_pow_right (by omega) h2

/-! ## Main Theorem -/

/-- **Shannon counting lower bound**: for `N ≥ 6`, there exists a Boolean
    function on N inputs that cannot be computed by any fan-in-2 circuit
    descriptor with at most `2^N / (5N)` gates.

    This is a formalization of Shannon's 1949 counting argument, which shows
    that most Boolean functions require circuits of size at least `2^N / (5N)`. -/
theorem shannon_lower_bound (N : Nat) (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ (d : CircDesc N (2 ^ N / (5 * N))),
        evalD (s_pos N hN) d ≠ f := by
  let s := 2 ^ N / (5 * N)
  let hs := s_pos N hN
  -- The image of evalD has strictly fewer elements than the function space
  have h_lt : ((Finset.univ : Finset (CircDesc N s)).image (evalD (N := N) (s := s) hs)).card
      < (Finset.univ : Finset (BitString N → Bool)).card := by
    calc ((Finset.univ : Finset (CircDesc N s)).image (evalD hs)).card
        ≤ (Finset.univ : Finset (CircDesc N s)).card := Finset.card_image_le
      _ = Fintype.card (CircDesc N s) := Finset.card_univ
      _ = (8 * (N + s) ^ 2) ^ s := card_circDesc N s
      _ < 2 ^ 2 ^ N := arith_bound N hN
      _ = Fintype.card (BitString N → Bool) := (card_bool_fun N).symm
      _ = (Finset.univ : Finset (BitString N → Bool)).card := (Finset.card_univ).symm
  -- By pigeonhole, some function is not in the image of evalD
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt
  exact ⟨f, fun d hd => hf (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩)⟩

end CircuitComplexity
