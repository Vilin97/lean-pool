/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Oracle
public import LeanPool.LeanQuantumAlg.Core.Components.Kets

/-!
# Walsh-Hadamard transform and the XOR phase-query pipeline

The reusable machinery shared by the single-query Hadamard-oracle-Hadamard
algorithms (Deutsch-Jozsa, Bernstein-Vazirani): the `n`-qubit Hadamard layer
in Walsh-Hadamard closed form [dW19, qcnotes.tex:1005-1006], and the
XOR-oracle phase-query pipeline that runs a Boolean oracle on the uniform
input register with a `|−⟩` target.

The central bridge `postOracleState_eq_afterPhaseQuery_tensor` rewrites the
actual XOR-oracle query as the phase pattern `(√(2^n))⁻¹ ∑ x (-1)^{f x}|x⟩`
tensored with the unchanged `|−⟩` target, so a single query followed by the
second Hadamard layer (`finalJointState`) factors through the input-register
`finalState`.

These pieces sit in a `Primitives` module so the Deutsch-Jozsa and
Bernstein-Vazirani algorithms can both build on them without importing one
another; each algorithm keeps only its target-specific content (the
constant/balanced promise and amplitude test for Deutsch-Jozsa; Walsh-character
orthogonality and string recovery for Bernstein-Vazirani).

## Main definitions

- `LeanPool.LeanQuantumAlg.WalshHadamard.Oracle n` — a Boolean function on `2^n` labels,
  queried through `Gate.xorOracle`.
- `LeanPool.LeanQuantumAlg.WalshHadamard.walshSign` — the Walsh-Hadamard sign `(-1)^{x·y}`,
  and `hadamardLayer` its closed-form `n`-qubit gate.
- `LeanPool.LeanQuantumAlg.WalshHadamard.uniformState` — the uniform superposition.
- `LeanPool.LeanQuantumAlg.WalshHadamard.finalJointState` — the post-circuit joint state,
  with `finalJointState_eq_finalState_tensor` factoring off the `|−⟩` target.
-/

@[expose] public section

namespace QuantumAlg

namespace WalshHadamard

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- A Boolean oracle on `2^n` input labels. It is queried through
`Gate.xorOracle`, not through a separate oracle type. -/
abbrev Oracle (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- The standard XOR query gate for a Boolean oracle. -/
abbrev oracleGate (f : Oracle n) : Gate (n + 1) := Gate.xorOracle f

/-- The phase `(-1)^{f x}`, written as a complex scalar. -/
def phaseSign (f : Oracle n) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-! ### The Walsh-Hadamard transform -/

/-- The bit of a basis label used in the Walsh-Hadamard character. The bit
order only affects nonzero rows; the zero row used by Deutsch-Jozsa is
independent of it. -/
def bit (x : Fin (2 ^ n)) (k : Fin n) : Bool := x.val.testBit k.val

/-- Parity of the bitwise inner product of two basis labels. -/
def dotParity (x y : Fin (2 ^ n)) : Bool :=
  Odd ((Finset.univ.filter fun k : Fin n => bit x k && bit y k).card)

/-- The Walsh-Hadamard sign `(-1)^{x · y}`. -/
def walshSign (x y : Fin (2 ^ n)) : ℂ := if dotParity x y then -1 else 1

/-- `(√(2^n))⁻¹`, the normalization scalar of the `n`-qubit Hadamard layer. -/
def invSqrtCard (n : ℕ) : ℂ := (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹

@[simp]
theorem star_invSqrtCard (n : ℕ) : star (invSqrtCard n) = invSqrtCard n := by
  rw [invSqrtCard, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem norm_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ = (Real.sqrt ((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [invSqrtCard, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_sq_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ ^ 2 = (((2 ^ n : ℕ) : ℝ)⁻¹) := by
  rw [norm_invSqrtCard, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]

@[simp]
theorem walshSign_zero_left (x : Fin (2 ^ n)) :
    walshSign (0 : Fin (2 ^ n)) x = 1 := by
  unfold walshSign dotParity bit
  simp

@[simp]
theorem walshSign_zero_right (x : Fin (2 ^ n)) :
    walshSign x (0 : Fin (2 ^ n)) = 1 := by
  unfold walshSign dotParity bit
  simp

theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold dotParity
  rw [hset]

theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold walshSign
  rw [dotParity_comm]

@[simp]
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem star_walshSign (x y : Fin (2 ^ n)) :
    star (walshSign x y) = walshSign x y := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem norm_walshSign (x y : Fin (2 ^ n)) : ‖walshSign x y‖ = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Walsh-character orthogonality -/

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
  unfold dotParity
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
    · have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
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
    · have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
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
  unfold walshSign
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

theorem sum_walshSign_mul_walshSign_eq (y s : Fin (2 ^ n)) :
    ∑ x, walshSign y x * walshSign s x =
      if y = s then ((2 ^ n : ℕ) : ℂ) else 0 := by
  by_cases hys : y = s
  · subst hys
    rw [if_pos rfl]
    simp only [walshSign_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hys, sum_walshSign_mul_walshSign hys]

@[simp]
theorem invSqrtCard_mul_self (n : ℕ) :
    invSqrtCard n * invSqrtCard n = (((2 ^ n : ℕ) : ℂ)⁻¹) := by
  rw [invSqrtCard, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  norm_num

/-- A Boolean phase has unit norm. -/
@[simp]
theorem norm_phaseSign (f : Oracle n) (x : Fin (2 ^ n)) :
    ‖phaseSign f x‖ = 1 := by
  unfold phaseSign
  by_cases h : f x <;> simp [h]

/-- Raw `n`-qubit Hadamard layer in Walsh-Hadamard closed form. -/
def hadamardLayerOp (n : ℕ) : HilbertOperator n :=
  fun y x => invSqrtCard n * walshSign y x

/-- The Walsh-Hadamard closed-form matrix is unitary. -/
theorem hadamardLayerOp_mem_unitaryGroup (n : ℕ) :
    hadamardLayerOp n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y s
  rw [Matrix.mul_apply]
  calc
    ∑ x, hadamardLayerOp n y x * star (hadamardLayerOp n) x s
        = ∑ x, (invSqrtCard n * invSqrtCard n)
            * (walshSign y x * walshSign s x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hadamardLayerOp, Matrix.star_apply]
          rw [star_mul, star_invSqrtCard, star_walshSign]
          ring
    _ = (invSqrtCard n * invSqrtCard n)
          * ∑ x, walshSign y x * walshSign s x := by
          rw [Finset.mul_sum]
    _ = (((2 ^ n : ℕ) : ℂ)⁻¹)
          * (if y = s then ((2 ^ n : ℕ) : ℂ) else 0) := by
          rw [invSqrtCard_mul_self, sum_walshSign_mul_walshSign_eq]
    _ = (1 : HilbertOperator n) y s := by
          by_cases hys : y = s
          · subst s
            rw [if_pos rfl, Matrix.one_apply_eq]
            exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero))
          · rw [if_neg hys, Matrix.one_apply_ne hys, mul_zero]

/-- The `n`-qubit Hadamard layer as a unitary gate. -/
def hadamardLayer (n : ℕ) : Gate n :=
  Gate.ofUnitary (hadamardLayerOp n) (hadamardLayerOp_mem_unitaryGroup n)

/-- Raw uniform input-register vector produced by the first Hadamard layer. -/
def uniformStateVec (n : ℕ) : StateVector n :=
  WithLp.toLp 2 fun _ => invSqrtCard n

/-- The uniform input-register vector has unit norm. -/
theorem norm_uniformStateVec (n : ℕ) : ‖uniformStateVec n‖ = 1 := by
  rw [uniformStateVec, EuclideanSpace.norm_eq]
  have hsum :
      ∑ i : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      norm_sq_invSqrtCard]
    norm_num
  rw [hsum, Real.sqrt_one]

/-- The uniform input-register state produced by the first Hadamard layer. -/
def uniformState (n : ℕ) : PureState n :=
  PureState.ofVec (uniformStateVec n) (norm_uniformStateVec n)

@[simp]
theorem uniformState_apply (x : Fin (2 ^ n)) : uniformState n x = invSqrtCard n :=
  rfl

/-- The first Hadamard layer sends `|0^n⟩` to the uniform superposition. -/
theorem hadamardLayer_apply_zero :
    (hadamardLayer n).apply (ket (0 : Fin (2 ^ n))) = uniformState n := by
  ext i
  rw [Gate.apply_ket]
  simp [hadamardLayer, hadamardLayerOp]

/-! ### The XOR phase-query pipeline -/

/-- The pre-Hadamard joint basis state `|0^n⟩ ⊗ |−⟩`. -/
def initialBasisState (n : ℕ) : PureState (n + 1) :=
  (ket (0 : Fin (2 ^ n))).tensor ketMinus

/-- The joint state queried by the XOR oracle, obtained by applying the first
Hadamard layer to the input register and leaving the `|−⟩` target alone. -/
def initialState (n : ℕ) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (initialBasisState n)

/-- The queried state is the uniform input register tensored with `|−⟩`. -/
theorem initialState_eq_uniform_tensor :
    initialState n = (uniformState n).tensor ketMinus := by
  rw [initialState, initialBasisState, Gate.tensor_apply_tensor,
    hadamardLayer_apply_zero, Gate.one_apply]

/-- The actual post-query joint state, using the XOR oracle gate. -/
def postOracleState (f : Oracle n) : PureState (n + 1) :=
  (oracleGate f).apply (initialState n)

/-- The input-register state after rewriting the oracle query by phase
kickback: `(√(2^n))⁻¹ ∑ x, (-1)^{f x}|x⟩`. -/
def afterPhaseQueryVec (f : Oracle n) : StateVector n :=
  WithLp.toLp 2 fun x => invSqrtCard n * phaseSign f x

/-- The phase-query vector has unit norm. -/
theorem norm_afterPhaseQueryVec (f : Oracle n) : ‖afterPhaseQueryVec f‖ = 1 := by
  rw [afterPhaseQueryVec, EuclideanSpace.norm_eq]
  have hsum :
      ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2 = 1 := by
    calc
      ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2
          = ∑ _x : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [norm_mul, norm_phaseSign, mul_one]
      _ = 1 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, norm_sq_invSqrtCard]
              norm_num
  rw [hsum, Real.sqrt_one]

/-- The input register after the XOR oracle has been converted into a phase query. -/
def afterPhaseQuery (f : Oracle n) : PureState n :=
  PureState.ofVec (afterPhaseQueryVec f) (norm_afterPhaseQueryVec f)

/-- The actual XOR-oracle query on the uniform input register and `|−⟩`
target is exactly the phase-query state tensored with the unchanged target. -/
theorem postOracleState_eq_afterPhaseQuery_tensor (f : Oracle n) :
    postOracleState f = (afterPhaseQuery f).tensor ketMinus := by
  ext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨x, b⟩, rfl⟩
  rw [postOracleState, initialState_eq_uniform_tensor, oracleGate,
    Gate.xorOracle_apply, PureState.tensor_apply_prod, afterPhaseQuery]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases h : f x
  · fin_cases b <;> simp [uniformState, uniformStateVec, afterPhaseQueryVec,
      h, phaseSign, ketMinus_apply]
  · simp [uniformState, uniformStateVec, afterPhaseQueryVec, h, phaseSign]

/-- The final input-register state after the second Hadamard layer, in the
phase-query view. -/
def finalState (f : Oracle n) : PureState n :=
  (hadamardLayer n).apply (afterPhaseQuery f)

/-- The actual final joint state: apply the second Hadamard layer to the
input register and leave the target qubit alone. -/
def finalJointState (f : Oracle n) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (postOracleState f)

/-- The actual final joint state factors as the final input-register state
and the unchanged `|−⟩` target. -/
theorem finalJointState_eq_finalState_tensor (f : Oracle n) :
    finalJointState f = (finalState f).tensor ketMinus := by
  rw [finalJointState, postOracleState_eq_afterPhaseQuery_tensor,
    Gate.tensor_apply_tensor, Gate.one_apply, finalState]

end

end WalshHadamard

end QuantumAlg
