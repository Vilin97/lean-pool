/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Cost
public import LeanPool.LeanQuantumAlg.Core.Gate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Quantum Fourier Transform

The quantum Fourier transform (QFT) on `n` qubits is the `2^n × 2^n` unitary
matrix mapping computational basis states to Fourier basis states
[dW19, qcnotes.tex:1692; Lin22, phaseestimation.tex:351]:

  `QFT |x⟩ = (1/√N) Σ_{y=0}^{N-1} ω^{xy} |y⟩`

where `N = 2^n` and `ω = e^{2πi/N}` is the primitive `N`-th root of unity.

## Conventions

- **Sign**: forward transform uses `ω = e^{+2πi/N}` (standard physics sign
  convention, matching [dW19, qcnotes.tex:1690] and
  [Lin22, phaseestimation.tex:349]).
- **Normalization**: `1/√N` prefactor makes the transform unitary.
- **Endianness**: big-endian, matching `LeanPool.LeanQuantumAlg.PureState`.

## Main definitions

- `LeanPool.LeanQuantumAlg.omega n` — primitive `2^n`-th root of unity `e^{2πi/2^n}`.
- `LeanPool.LeanQuantumAlg.invSqrtN n` — normalization factor `1/√(2^n)`.
- `LeanPool.LeanQuantumAlg.QFT n` — the QFT gate on `n` qubits.

## Main results

- `LeanPool.LeanQuantumAlg.omega_pow_eq_one` — `ω^(2^n) = 1`.
- `LeanPool.LeanQuantumAlg.norm_omega` — `‖ω‖ = 1`.
- `LeanPool.LeanQuantumAlg.QFT_apply_ket` — component formula for `QFT |x⟩`.
- `LeanPool.LeanQuantumAlg.sum_omega_zpow_eq_zero` — full-period geometric sums of
  nontrivial powers of `ω` vanish (column orthogonality).
- `LeanPool.LeanQuantumAlg.QuantumFourierTransform.main` — the QFT is unitary.

Pinned Mathlib API: `Complex.exp`, `Complex.exp_nat_mul`, `Complex.exp_eq_one_iff`,
`Complex.norm_exp_ofReal_mul_I`, `Complex.isPrimitiveRoot_exp`,
`Matrix.of_apply`, `Real.mul_self_sqrt`, `RCLike.inv_eq_conj`,
`IsPrimitiveRoot.zpow_eq_one_iff_dvd`, `geom_sum_eq`,
`Fin.sum_univ_eq_sum_range`, `Int.eq_zero_of_abs_lt_dvd`,
`Int.abs_sub_lt_of_lt_lt`, `Matrix.mem_unitaryGroup_iff'`.
-/

@[expose] public section

namespace QuantumAlg

open PureState

noncomputable section

/-! ### Root of unity -/

/-- Primitive `2^n`-th root of unity: `ω_n = e^{2πi/2^n}`
[dW19, qcnotes.tex:1690].
Forward-transform sign convention (`+2πi`, not `−2πi`). -/
def omega (n : ℕ) : ℂ :=
  Complex.exp (↑(2 * Real.pi / (2 : ℝ) ^ n) * Complex.I)
-- [dW19, qcnotes.tex:1690]: ω_N = e^{2πi/N}

/-- `ω_n ^ (2^n) = 1`: the root has exact period `2^n`. -/
theorem omega_pow_eq_one (n : ℕ) : omega n ^ (2 ^ n) = 1 := by
  rw [omega, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨1, ?_⟩
  push_cast
  have h : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos two_pos n)
  field_simp

/-- `‖ω_n‖ = 1`: roots of unity lie on the unit circle. -/
@[simp]
theorem norm_omega (n : ℕ) : ‖omega n‖ = 1 := by
  rw [omega]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `omega n` equals the form used by Mathlib's `isPrimitiveRoot_exp`. -/
private theorem omega_eq_exp_div (n : ℕ) :
    omega n = Complex.exp (2 * ↑Real.pi * Complex.I / ↑(2 ^ n : ℕ)) := by
  simp only [omega]; congr 1; push_cast; ring

/-- `omega n` is a primitive `2^n`-th root of unity. -/
theorem omega_isPrimitiveRoot (n : ℕ) : IsPrimitiveRoot (omega n) (2 ^ n) := by
  rw [omega_eq_exp_div]
  exact Complex.isPrimitiveRoot_exp (2 ^ n) (by positivity)

/-! ### Normalization -/

/-- QFT normalization factor: `1/√(2^n)`, generalizing `PureState.invSqrt2`. -/
def invSqrtN (n : ℕ) : ℂ := (↑(Real.sqrt ((2 : ℝ) ^ n)))⁻¹

@[simp]
theorem star_invSqrtN (n : ℕ) : star (invSqrtN n) = invSqrtN n := by
  rw [invSqrtN, star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem invSqrtN_ne_zero (n : ℕ) : invSqrtN n ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (pow_pos two_pos n)

@[simp]
theorem invSqrtN_mul_self (n : ℕ) :
    invSqrtN n * invSqrtN n = (↑((2 : ℝ) ^ n))⁻¹ := by
  rw [invSqrtN, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (le_of_lt (pow_pos two_pos n))]

/-! ### QFT gate -/

/-- The quantum Fourier transform on `n` qubits
[dW19, qcnotes.tex:1692].
Entry `(j, k) = invSqrtN n * ω_n^{j·k}`. -/
def QFTMatrix (n : ℕ) : HilbertOperator n :=
  Matrix.of fun (j k : Fin (2 ^ n)) =>
    invSqrtN n * omega n ^ (j.val * k.val)

@[simp]
theorem QFT_entry (n : ℕ) (j k : Fin (2 ^ n)) :
    QFTMatrix n j k = invSqrtN n * omega n ^ (j.val * k.val) := by
  simp [QFTMatrix]

/-! ### Action on basis kets -/

/-- Component formula for the QFT acting on a basis ket:
`(QFT |x⟩)ᵢ = (1/√N) · ω^{i·x}` [dW19, qcnotes.tex:1692]. -/
theorem QFTMatrix_apply_ket_column (n : ℕ) (x i : Fin (2 ^ n)) :
    QFTMatrix n i x = invSqrtN n * omega n ^ (i.val * x.val) := by
  rw [QFT_entry]

/-! ### Unitarity -/

theorem omega_ne_zero (n : ℕ) : omega n ≠ 0 :=
  Complex.exp_ne_zero _

/-- `star ω_n = ω_n⁻¹`: conjugation inverts a point on the unit circle. -/
@[simp]
theorem star_omega (n : ℕ) : star (omega n) = (omega n)⁻¹ := by
  rw [Complex.star_def, ← RCLike.inv_eq_conj (norm_omega n)]

/-- Integer-power version of periodicity: `ω_n ^ d = 1` iff `2^n ∣ d`. -/
theorem omega_zpow_eq_one_iff (n : ℕ) (d : ℤ) :
    omega n ^ d = 1 ↔ ((2 ^ n : ℕ) : ℤ) ∣ d :=
  (omega_isPrimitiveRoot n).zpow_eq_one_iff_dvd d

/-- Column orthogonality [dW19, qcnotes.tex:1698]: the full-period geometric
sum `∑_{l<2^n} ω^{l·d}` vanishes when `2^n ∤ d`. -/
theorem sum_omega_zpow_eq_zero (n : ℕ) {d : ℤ}
    (hd : ¬ ((2 ^ n : ℕ) : ℤ) ∣ d) :
    ∑ l : Fin (2 ^ n), omega n ^ ((l.val : ℤ) * d) = 0 := by
  have hsum : ∀ l : Fin (2 ^ n),
      omega n ^ ((l.val : ℤ) * d) = (omega n ^ d) ^ l.val := fun l => by
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp only [hsum]
  rw [Fin.sum_univ_eq_sum_range fun i => (omega n ^ d) ^ i]
  have hne1 : omega n ^ d ≠ 1 := fun h => hd ((omega_zpow_eq_one_iff n d).mp h)
  have hN : (omega n ^ d) ^ (2 ^ n) = 1 := by
    rw [← zpow_natCast (omega n ^ d) (2 ^ n), ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, omega_pow_eq_one, one_zpow]
  rw [geom_sum_eq hne1, hN, sub_self, zero_div]

/-- The QFT is unitary [dW19, qcnotes.tex:1696]: columns are normalized and
pairwise orthogonal. Entry-by-entry, `star (QFT n) * QFT n` at `(j, k)` is
`invSqrtN² · ∑_l ω^{l·(k−j)}`, which `sum_omega_zpow_eq_zero` collapses to
`if j = k then 1 else 0`. -/
theorem QFT_mem_unitaryGroup (n : ℕ) :
    QFTMatrix n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have hterm : ∀ l : Fin (2 ^ n),
      star (QFTMatrix n) j l * QFTMatrix n l k =
        (↑((2 : ℝ) ^ n))⁻¹ *
          omega n ^ ((l.val : ℤ) * ((k.val : ℤ) - (j.val : ℤ))) := by
    intro l
    simp only [Matrix.star_apply, QFT_entry, star_mul', star_pow, star_omega,
      star_invSqrtN]
    rw [mul_mul_mul_comm, invSqrtN_mul_self]
    congr 1
    rw [inv_pow, ← zpow_natCast (omega n) (l.val * j.val),
      ← zpow_natCast (omega n) (l.val * k.val), ← zpow_neg,
      ← zpow_add₀ (omega_ne_zero n)]
    congr 1
    push_cast
    ring
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have h0 : ∀ l : Fin (2 ^ n),
        omega n ^ ((l.val : ℤ) * ((j.val : ℤ) - (j.val : ℤ))) = (1 : ℂ) :=
      fun l => by rw [sub_self, mul_zero, zpow_zero]
    simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)
  · rw [if_neg hjk]
    have hd : ¬ ((2 ^ n : ℕ) : ℤ) ∣ ((k.val : ℤ) - (j.val : ℤ)) := by
      intro hdvd
      have h0 : (k.val : ℤ) - (j.val : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (Int.abs_sub_lt_of_lt_lt j.isLt k.isLt)
      exact hjk (Fin.val_injective
        (by exact_mod_cast sub_eq_zero.mp h0 : k.val = j.val)).symm
    rw [sum_omega_zpow_eq_zero n hd, mul_zero]

/-- The quantum Fourier transform on `n` qubits as a unitary gate. -/
def QFT (n : ℕ) : Gate n := Gate.ofUnitary (QFTMatrix n) (QFT_mem_unitaryGroup n)

@[simp]
theorem QFT_coe (n : ℕ) : ((QFT n : Gate n) : HilbertOperator n) = QFTMatrix n := rfl

/-! ### Action on basis kets -/

/-- Component formula for the QFT acting on a basis ket:
`(QFT |x⟩)_i = (1/√N) · ω^{i·x}` [dW19, qcnotes.tex:1692]. -/
theorem QFT_apply_ket (n : ℕ) (x i : Fin (2 ^ n)) :
    (QFT n).apply (ket x) i = invSqrtN n * omega n ^ (i.val * x.val) := by
  simp [QFT, QFTMatrix]

/-- Fixed-circuit gate profile for the standard QFT decomposition: `n`
Hadamard gates, `n(n-1)/2` controlled-phase gates, and `n/2` final register
swaps in this natural-number convention. -/
def QFTCircuitProfile (n : ℕ) : CircuitGateProfile where
  hadamardGates := n
  controlledPhaseGates := n * (n - 1) / 2
  swapGates := n / 2

theorem QFTCircuitProfile_exact (n : ℕ) :
    CircuitGateProfile.HasExactCounts
      (QFTCircuitProfile n) n (n * (n - 1) / 2) (n / 2) := by
  simp [CircuitGateProfile.HasExactCounts, QFTCircuitProfile]

/-- QFT basis action paired with the fixed-circuit gate counts used by the
standard decomposition. -/
theorem QuantumFourierTransform.main (n : ℕ) (x : Fin (2 ^ n)) :
    (∀ i : Fin (2 ^ n),
      (QFT n).apply (ket x) i = invSqrtN n * omega n ^ (i.val * x.val)) ∧
      CircuitGateProfile.HasExactCounts
        (QFTCircuitProfile n) n (n * (n - 1) / 2) (n / 2) := by
  constructor
  · intro i
    exact QFT_apply_ket n x i
  · exact QFTCircuitProfile_exact n


end

end QuantumAlg
