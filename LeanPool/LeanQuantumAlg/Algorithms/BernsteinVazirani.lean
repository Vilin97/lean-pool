/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.WalshHadamard
public import LeanPool.LeanQuantumAlg.Core.Cost

/-!
# Bernstein-Vazirani algorithm

The Bernstein-Vazirani problem gives oracle access to the inner-product
function `x ↦ x · s mod 2` of an unknown string `s`, and asks to find `s`
[dW19, qcnotes.tex:1282-1283]. The original problem is due to Bernstein and
Vazirani (1997).

The circuit is exactly the Deutsch-Jozsa circuit [dW19, qcnotes.tex:1288]:
after one query, the input register holds the phase pattern
`(1/√N) ∑_x (-1)^{x·s} |x⟩` [dW19, qcnotes.tex:1293-1294], and the second
Hadamard layer maps it exactly to the classical state `|s⟩`
[dW19, qcnotes.tex:1296]. One query therefore
recovers the whole hidden string.

This module reuses the shared Walsh-Hadamard pipeline
(`WalshHadamard.finalJointState` applied to the inner-product oracle): the
query is the actual XOR-oracle gate, bridged by phase kickback. The new
mathematical content is Walsh-character orthogonality, proved by a
pair-cancellation involution (flip a bit on which the two characters
disagree).

## Conventions

- Bit order: `WalshHadamard.bit x k = x.val.testBit k.val`, as in the
  `WalshHadamard` primitive. The recovered string is expressed in the same
  convention used by the oracle, so the statement is convention-consistent.
- Big-endian basis labelling as in `Core/State.lean`.

## Main results

- `LeanPool.LeanQuantumAlg.BernsteinVazirani.oracle` — the inner-product oracle of a
  hidden string, as a `WalshHadamard` Boolean oracle.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.sum_walshSign_mul_walshSign` —
  Walsh-character orthogonality via the bit-flip involution.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.finalState_oracle` — the final input
  register is exactly `|s⟩`.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.main` — the joint register after the
  circuit is exactly `|s⟩ ⊗ |−⟩`: one query recovers the hidden string.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

namespace BernsteinVazirani

open WalshHadamard

/-- The Bernstein-Vazirani oracle for hidden string `s`: the inner-product
function `x ↦ x · s mod 2` [dW19, qcnotes.tex:1283], queried through
`Gate.xorOracle` like any Deutsch-Jozsa oracle. -/
def oracle (s : Fin (2 ^ n)) : WalshHadamard.Oracle n := fun x => dotParity x s

/-! ### Walsh-sign algebra -/

/-- The bitwise inner-product parity is symmetric. -/
theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold WalshHadamard.dotParity
  rw [hset]

/-- The Walsh sign is symmetric. -/
theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold WalshHadamard.walshSign
  rw [dotParity_comm]

/-- A Walsh sign squares to `1`. -/
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold WalshHadamard.walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Bit-flip involution -/

/-- Flip bit `k` of a basis label. -/
def flipBit (x : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ k.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right one_lt_two k.isLt)⟩

theorem bit_flipBit (x : Fin (2 ^ n)) (k k' : Fin n) :
    bit (flipBit x k) k' = (bit x k' ^^ decide (k = k')) := by
  change (x.val ^^^ 2 ^ k.val).testBit k'.val = (bit x k' ^^ decide (k = k'))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact Fin.val_inj

theorem flipBit_flipBit (x : Fin (2 ^ n)) (k : Fin n) :
    flipBit (flipBit x k) k = x := by
  unfold flipBit
  ext
  simp [Nat.xor_assoc]

theorem flipBit_ne (x : Fin (2 ^ n)) (k : Fin n) : flipBit x k ≠ x := by
  intro h
  have hb := congrArg (fun y : Fin (2 ^ n) => bit y k) h
  simp [bit_flipBit] at hb

/-- Flipping bit `k` of `x` toggles the parity `x · z` exactly when bit `k`
of `z` is set. -/
theorem dotParity_flipBit (x z : Fin (2 ^ n)) (k : Fin n) :
    dotParity (flipBit x k) z = (dotParity x z ^^ bit z k) := by
  unfold WalshHadamard.dotParity
  cases hz : bit z k
  · rw [Bool.xor_false]
    have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
        = Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
      apply Finset.filter_congr
      intro k' _
      rcases eq_or_ne k k' with rfl | hk
      · simp [bit_flipBit, hz]
      · simp [bit_flipBit, hk]
    rw [hset]
  · rw [Bool.xor_true]
    by_cases hx : bit x k
    · -- `k` is in the original index set; flipping removes it.
      have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx, hz]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k').erase k := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, ← decide_not, decide_eq_decide,
        ← Finset.card_erase_add_one hmem, Nat.odd_add_one, not_not]
    · -- `k` is not in the original index set; flipping inserts it.
      have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = insert k (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k') := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx, hz]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, Finset.card_insert_of_notMem hnot, ← decide_not,
        decide_eq_decide, Nat.odd_add_one]

/-- Two distinct labels differ at some bit. -/
theorem exists_bit_ne {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∃ k : Fin n, bit y k ≠ bit s k := by
  by_contra hall
  push Not at hall
  refine h (Fin.val_injective (Nat.eq_of_testBit_eq fun i => ?_))
  by_cases hi : i < n
  · exact hall ⟨i, hi⟩
  · push Not at hi
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    have hs : s.val < 2 ^ i := lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hy, Nat.testBit_lt_two_pow hs]

private theorem if_xor_true (a : Bool) :
    (if (a ^^ true) = true then (-1 : ℂ) else 1) = -(if a = true then -1 else 1) := by
  cases a <;> simp

/-- Flipping a bit on which `y` and `s` disagree negates the product of their
Walsh signs. -/
theorem walshSign_mul_walshSign_flipBit {y s : Fin (2 ^ n)} {k : Fin n}
    (hk : bit y k ≠ bit s k) (x : Fin (2 ^ n)) :
    walshSign y (flipBit x k) * walshSign s (flipBit x k)
      = -(walshSign y x * walshSign s x) := by
  unfold WalshHadamard.walshSign
  simp only [dotParity_comm y (flipBit x k), dotParity_comm s (flipBit x k),
    dotParity_flipBit, dotParity_comm x y, dotParity_comm x s]
  cases hy : bit y k <;> cases hs : bit s k
  · exact absurd (hy.trans hs.symm) hk
  · rw [Bool.xor_false, if_xor_true]
    ring
  · rw [Bool.xor_false, if_xor_true]
    ring
  · exact absurd (hy.trans hs.symm) hk

/-- Walsh-character orthogonality: for `y ≠ s` the signed sum over all basis
labels cancels in pairs under the bit-flip involution. -/
theorem sum_walshSign_mul_walshSign {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∑ x, walshSign y x * walshSign s x = 0 := by
  obtain ⟨k, hk⟩ := exists_bit_ne h
  refine Finset.sum_involution (fun x _ => flipBit x k)
    (fun x _ => ?_) (fun x _ _ => flipBit_ne x k)
    (fun x _ => Finset.mem_univ _) (fun x _ => flipBit_flipBit x k)
  rw [walshSign_mul_walshSign_flipBit hk x]
  ring

/-! ### Circuit correctness -/

/-- Querying the inner-product oracle phases each basis label by its Walsh
sign with the hidden string [dW19, qcnotes.tex:1293]. -/
theorem phaseSign_oracle (s x : Fin (2 ^ n)) :
    phaseSign (oracle s) x = walshSign s x := by
  unfold WalshHadamard.phaseSign WalshHadamard.walshSign oracle
  rw [dotParity_comm]

/-- The second Hadamard layer maps the Bernstein-Vazirani phase pattern
exactly to the classical state `|s⟩` [dW19, qcnotes.tex:1296]. -/
theorem finalState_oracle (s : Fin (2 ^ n)) :
    finalState (oracle s) = ket s := by
  ext y
  rw [WalshHadamard.finalState, Gate.apply_apply, ket_apply]
  have hterm : ∀ j, hadamardLayer n y j * afterPhaseQuery (oracle s) j
      = ((2 ^ n : ℕ) : ℂ)⁻¹ * (walshSign y j * walshSign s j) := fun j => by
    change (invSqrtCard n * walshSign y j)
        * (invSqrtCard n * phaseSign (oracle s) j) = _
    rw [phaseSign_oracle, mul_mul_mul_comm, invSqrtCard_mul_self]
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hys : y = s
  · subst hys
    rw [if_pos rfl]
    simp only [walshSign_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)
  · rw [if_neg hys, sum_walshSign_mul_walshSign hys, mul_zero]

/-- The final Bernstein-Vazirani joint state, annotated with one oracle query. -/
def timedFinalJointState (s : Fin (2 ^ n)) : Timed (PureState (n + 1)) :=
  Timed.trusted 1 (WalshHadamard.finalJointState (oracle s))

@[simp]
theorem timedFinalJointState_ret (s : Fin (2 ^ n)) :
    (timedFinalJointState s).ret = WalshHadamard.finalJointState (oracle s) := rfl

@[simp]
theorem timedFinalJointState_time (s : Fin (2 ^ n)) :
    (timedFinalJointState s).time = 1 := rfl

/-- Public resource profile for the Bernstein-Vazirani circuit:
one oracle query and two `n`-qubit Hadamard layers plus the target Hadamard. -/
def resourceProfile (n : ℕ) : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 2 * n + 1
  elementaryGates := 2 * n + 1
  classicalOps := 0

@[simp]
theorem resourceProfile_oracleQueries (n : ℕ) :
    (resourceProfile n).oracleQueries = 1 := rfl

@[simp]
theorem resourceProfile_hadamardGates (n : ℕ) :
    (resourceProfile n).hadamardGates = 2 * n + 1 := rfl

@[simp]
theorem resourceProfile_elementaryGates (n : ℕ) :
    (resourceProfile n).elementaryGates = 2 * n + 1 := rfl

theorem resourceProfile_exact (n : ℕ) :
    ResourceProfile.HasExactCounts (resourceProfile n) 1 (2 * n + 1) (2 * n + 1) 0 := by
  simp [ResourceProfile.HasExactCounts, resourceProfile]

/-- The final Bernstein-Vazirani joint state with its public resource profile. -/
def profiledFinalJointState (s : Fin (2 ^ n)) : Profiled (PureState (n + 1)) :=
  Profiled.trusted (resourceProfile n) (WalshHadamard.finalJointState (oracle s))

@[simp]
theorem profiledFinalJointState_ret (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).ret = WalshHadamard.finalJointState (oracle s) := rfl

@[simp]
theorem profiledFinalJointState_resources (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).resources = resourceProfile n := rfl

/-- **Bernstein-Vazirani correctness**: running the Deutsch-Jozsa circuit
with the inner-product oracle of hidden string `s` leaves the joint register
in exactly `|s⟩ ⊗ |−⟩` [dW19, qcnotes.tex:1296], so a single query recovers
the hidden string (Bernstein and Vazirani 1997). -/
theorem main (s : Fin (2 ^ n)) :
    WalshHadamard.finalJointState (oracle s)
      = (ket s).tensor ketMinus := by
  rw [WalshHadamard.finalJointState_eq_finalState_tensor,
    finalState_oracle]

/-- Bernstein-Vazirani correctness, phrased through the TimeM return value. -/
theorem timedFinalJointState_correct (s : Fin (2 ^ n)) :
    (timedFinalJointState s).ret = (ket s).tensor ketMinus := by
  exact main s

/-- Bernstein-Vazirani supporting theorem for the public statement: the profiled
circuit returns `|s⟩ ⊗ |-⟩` and records the accepted exact resource counts. -/
theorem main_with_resources (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).ret = (ket s).tensor ketMinus ∧
      ResourceProfile.HasExactCounts (profiledFinalJointState s).resources
        1 (2 * n + 1) (2 * n + 1) 0 := by
  constructor
  · exact main s
  · simp [resourceProfile_exact n]

end BernsteinVazirani

end

end QuantumAlg
