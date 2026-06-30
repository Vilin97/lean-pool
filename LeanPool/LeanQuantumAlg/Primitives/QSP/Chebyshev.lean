/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates
public import LeanPool.LeanQuantumAlg.Util.Complex
public import LeanPool.LeanQuantumAlg.Util.Polynomial

/-!
# Quantum signal processing (single qubit) — Chebyshev basis

The Chebyshev-basis single-qubit QSP characterizations: the reflection-derived
**O-convention** of [Lin22, hermfunc.tex:1103] and the **Wx-convention (XZX
form)** of [GSLW19, BlockHam.tex:295]. Both interleave a fixed one-parameter
signal rotation with tunable `e^{iφZ}` processing rotations (in
`Core.Components.Gates`) and characterize exactly which `SU(2)`-valued
polynomial transforms of the signal `x ∈ [-1,1]` are achievable.

O-convention: the signal operator is `O(x) = [[x, -√(1-x²)], [√(1-x²), x]]`
and the QSP sequence with phase factors `(φ₀, …, φ_d)` is
`U_Φ(x) = e^{iφ₀Z} · ∏_{j=1}^d (O(x) e^{iφ_j Z})`.

`LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main` [Lin22,
hermfunc.tex:1118]: `U_Φ(x)` takes the form
`[[P(x), -Q(x)√(1-x²)], [Q*(x)√(1-x²), P*(x)]]` for all `x ∈ [-1,1]` for some
phase factors **iff** `(P, Q)` is an `IsQSPPair d`, i.e.

1. `deg P ≤ d` and `Q.degree < d`,
2. `P` has parity `d mod 2` and `Q` has parity `(d-1) mod 2`,
3. `P·P* + (1-X²)·Q·Q* = 1` (`*` conjugates the coefficients; `conjP`).

Condition 3 is equivalent to the pointwise `|P(x)|² + (1-x²)|Q(x)|² = 1` on the
infinite set `[-1,1]` (`LeanPool.LeanQuantumAlg.qsp_normalization_iff`).

The **Wx-convention** replaces `O(x)` by `W(x) = e^{i·arccos(x)·X}`; the fixed
conjugation `W(x) = e^{-i(π/4)Z}·O(x)·e^{i(π/4)Z}` [Lin22, hermfunc.tex:1279]
transports the characterization
(`LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main_wx`) with
the same pair conditions `IsQSPPair`.

This module is one half of the single-qubit QSP development; the Fourier-basis
(trigonometric YZY/YZZYZ) forms live in `LeanPool.LeanQuantumAlg.Primitives.QSP.Fourier`,
and `LeanPool.LeanQuantumAlg.Primitives.QSP` re-exports both.

## Main results

- `LeanPool.LeanQuantumAlg.qspO_mem_unitaryGroup` — `U_Φ(x)` is unitary for
  `x ∈ [-1,1]`.
- `LeanPool.LeanQuantumAlg.qspO_forward` /
  `LeanPool.LeanQuantumAlg.qspO_converse` — soundness and completeness of the
  O-convention.
- `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main` — the
  O-convention characterization (registered target entry point).
- `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main_wx` —
  the Wx-convention (XZX) characterization.

Pinned Mathlib API: `Polynomial.coeff_X_mul`, `Polynomial.coeff_mul`,
`Polynomial.degree_le_iff_coeff_zero`, `Polynomial.degree_lt_iff_coeff_zero`,
`Polynomial.eq_of_infinite_eval_eq`, `Complex.exp_mul_I`, `Complex.mul_conj`,
`Set.Icc.infinite`, `List.reverseRecOn`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

/-! ### Signal operator (the processing rotation `rotZ` is in
`Core.Components.Gates`) -/

/-- The signal rotation `O(x) = [[x, -√(1-x²)], [√(1-x²), x]]`
[Lin22, hermfunc.tex:1103]; equals `U_A(x)·Z` for the reflection `U_A(x)` of
[GSLW19, BlockHam.tex:488]. -/
def signalO (x : ℝ) : HilbertOperator 1 :=
  !![(x : ℂ), -(Real.sqrt (1 - x ^ 2) : ℂ);
     (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- The QSP sequence `U_Φ(x) = e^{iφ₀Z} ∏_j (O(x) e^{iφ_jZ})` with phase
factors `Φ = (φ₀, φs)` [Lin22, hermfunc.tex:1121]. -/
def qspO (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) : HilbertOperator 1 :=
  φs.foldl (fun U φ => U * (signalO x * rotZ φ)) (rotZ φ₀ : HilbertOperator 1)

@[simp]
theorem qspO_nil (φ₀ : ℝ) (x : ℝ) : qspO φ₀ [] x = rotZ φ₀ := rfl

theorem qspO_concat (φ₀ : ℝ) (φs : List ℝ) (φ : ℝ) (x : ℝ) :
    qspO φ₀ (φs ++ [φ]) x = qspO φ₀ φs x * (signalO x * rotZ φ) := by
  simp [qspO, List.foldl_append]

theorem signalO_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    signalO x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have hs := sq_sqrt_one_sub_sq hx
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs

theorem qspO_mem_unitaryGroup (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspO φ₀ φs x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  induction φs using List.reverseRecOn with
  | nil => exact rotZ_mem_unitaryGroup φ₀
  | append_singleton φs φ ih =>
      rw [qspO_concat]
      exact mul_mem ih (mul_mem (signalO_mem_unitaryGroup hx)
        (rotZ_mem_unitaryGroup φ))

/-! ### The QSP form and its one-step recurrence -/

/-- The target matrix form `[[P(x), -Q(x)s], [Q*(x)s, P*(x)]]`, `s = √(1-x²)`
[Lin22, hermfunc.tex:1121]. -/
def qspMat (P Q : ℂ[X]) (x : ℝ) : HilbertOperator 1 :=
  !![P.eval (x : ℂ), -Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
     starRingEnd ℂ (Q.eval (x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ),
     starRingEnd ℂ (P.eval (x : ℂ))]

/-- `rotZ φ₀` is the `d = 0` instance of the QSP form. -/
private theorem rotZ_eq_qspMat (c : ℂ) (φ₀ : ℝ) (x : ℝ)
    (hc : Complex.exp (φ₀ * Complex.I) = c) :
    (rotZ φ₀ : HilbertOperator 1) = qspMat (C c) 0 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotZOp, qspMat, ← hc, conj_exp_I]

/-- One-step recurrence [Lin22, hermfunc.tex:1148]: appending a signal-phase
pair `O(x)·e^{iφZ}` maps the form `(P, Q)` to the form
`(e^{iφ}(X·P - (1-X²)·Q), e^{-iφ}(P + X·Q))`. -/
private theorem qspMat_step (P Q : ℂ[X]) (φ : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspMat P Q x * (signalO x * rotZ φ) =
      qspMat (C (Complex.exp (φ * Complex.I)) * (X * P - (1 - X ^ 2) * Q))
        (C (Complex.exp (-(φ * Complex.I))) * (P + X * Q)) x := by
  have hs := sq_sqrt_one_sub_sq hx
  ext i j
  fin_cases i <;> fin_cases j
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    linear_combination (-(Complex.exp ((φ : ℂ) * Complex.I) *
      Q.eval (x : ℂ))) * hs
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    ring
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    ring
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    linear_combination (-(Complex.exp (-((φ : ℂ) * Complex.I)) *
      starRingEnd ℂ (Q.eval (x : ℂ)))) * hs

/-! ### The QSP pair conditions -/

/-- Conditions (1)–(3) of the QSP theorem [Lin22, hermfunc.tex:1127] for
degree budget `d`: degree bounds (`Q.degree < d` encodes `deg Q ≤ d-1`,
with `Q = 0` forced when `d = 0`), parities, and the polynomial normalization
identity (`*` = coefficient conjugation `conjP`). -/
structure IsQSPPair (d : ℕ) (P Q : ℂ[X]) : Prop where
  degP : P.degree ≤ d
  degQ : Q.degree < d
  parP : HasParity P d
  parQ : HasParity Q (d + 1)
  norm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1

theorem IsQSPPair.coeff_P_eq_zero {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q)
    {m : ℕ} (hm : d < m) : P.coeff m = 0 := by
  refine (Polynomial.degree_le_iff_coeff_zero P d).mp h.degP m ?_
  exact_mod_cast hm

theorem IsQSPPair.coeff_Q_eq_zero {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q)
    {m : ℕ} (hm : d ≤ m) : Q.coeff m = 0 :=
  (Polynomial.degree_lt_iff_coeff_zero Q d).mp h.degQ m (by exact_mod_cast hm)

/-- Build the degree conditions from coefficient bounds. -/
theorem isQSPPair_of_coeff {d : ℕ} {P Q : ℂ[X]}
    (hP : ∀ m, d < m → P.coeff m = 0) (hQ : ∀ m, d ≤ m → Q.coeff m = 0)
    (parP : HasParity P d) (parQ : HasParity Q (d + 1))
    (norm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1) :
    IsQSPPair d P Q := by
  refine ⟨?_, ?_, parP, parQ, norm⟩
  · refine (Polynomial.degree_le_iff_coeff_zero P d).mpr fun m hm => hP m ?_
    exact_mod_cast hm
  · exact (Polynomial.degree_lt_iff_coeff_zero Q d).mpr fun m hm =>
      hQ m (by exact_mod_cast hm)

/-- The normalization identity is preserved by the one-step recurrence: a pure
ring identity once the unit-modulus factor `v·w = v·v* = 1` cancels. -/
private theorem qsp_norm_step (P Q : ℂ[X]) (v w : ℂ) (hv : starRingEnd ℂ v = w)
    (hvw : v * w = 1)
    (hnorm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1) :
    (C v * (X * P - (1 - X ^ 2) * Q)) *
        conjP (C v * (X * P - (1 - X ^ 2) * Q))
      + (1 - X ^ 2) *
        ((C w * (P + X * Q)) * conjP (C w * (P + X * Q))) = 1 := by
  have hw : starRingEnd ℂ w = v := by rw [← hv, Complex.conj_conj]
  have hCvw : (C v * C w : ℂ[X]) = 1 := by rw [← C_mul, hvw, map_one]
  simp only [conjP_mul, conjP_sub, conjP_add, conjP_C, conjP_X, conjP_one,
    conjP_pow, hv, hw]
  linear_combination (C v * C w : ℂ[X]) * hnorm + hCvw

/-- One-step closure of the QSP pair conditions, matching `qspMat_step`. -/
private theorem IsQSPPair.step {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q) (φ : ℝ) :
    IsQSPPair (d + 1)
      (C (Complex.exp (φ * Complex.I)) * (X * P - (1 - X ^ 2) * Q))
      (C (Complex.exp (-(φ * Complex.I))) * (P + X * Q)) := by
  refine isQSPPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_ ?_ ?_
  · have h1 : P.coeff (m - 1) = 0 := h.coeff_P_eq_zero (by omega)
    have h2 : Q.coeff m = 0 := h.coeff_Q_eq_zero (by omega)
    have h3 : Q.coeff (m - 2) = 0 := h.coeff_Q_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    have hm2 : ¬ m < 2 := by omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_sub, sub_mul, one_mul,
      coeff_X_mul', coeff_X_sq_mul, h1, h2, h3, hm0, hm2]
  · have h1 : P.coeff m = 0 := h.coeff_P_eq_zero (by omega)
    have h2 : Q.coeff (m - 1) = 0 := h.coeff_Q_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_add, coeff_X_mul', h1, h2,
      hm0]
  · exact ((h.parP.X_mul).sub (h.parQ.one_sub_X_sq_mul.congr (by omega))).C_mul _
  · exact ((h.parP.congr (by omega)).add (h.parQ.X_mul)).C_mul _
  · exact qsp_norm_step P Q _ _ (conj_exp_I φ) (exp_I_mul_exp_neg_I φ) h.norm

/-! ### Soundness (forward direction) -/

/-- Soundness of QSP [Lin22, hermfunc.tex:1139]: every QSP product
`U_Φ(x)` takes the form `qspMat P Q x` on `[-1,1]` for a pair `(P, Q)`
satisfying the degree, parity, and normalization conditions. -/
theorem qspO_forward (φ₀ : ℝ) (φs : List ℝ) :
    ∃ P Q : ℂ[X], IsQSPPair φs.length P Q ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspO φ₀ φs x = qspMat P Q x := by
  induction φs using List.reverseRecOn with
  | nil =>
      refine ⟨C (Complex.exp (φ₀ * Complex.I)), 0, ⟨?_, ?_, ?_, ?_, ?_⟩,
        fun x _ => rotZ_eq_qspMat _ φ₀ x rfl⟩
      · simp
      · simp
      · exact hasParity_C _ rfl
      · exact hasParity_zero _
      · have hC : (C (Complex.exp (φ₀ * Complex.I)) *
            C (Complex.exp (-(φ₀ * Complex.I))) : ℂ[X]) = 1 := by
          rw [← C_mul, exp_I_mul_exp_neg_I, map_one]
        simpa [conj_exp_I] using hC
  | append_singleton φs φ ih =>
      obtain ⟨P, Q, hpair, hmat⟩ := ih
      refine ⟨_, _, by simpa using hpair.step φ, fun x hx => ?_⟩
      rw [qspO_concat, hmat x hx, qspMat_step P Q φ hx]

/-! ### Completeness (converse direction)

Degree-reduction induction [Lin22, hermfunc.tex:1212]: given an `IsQSPPair`
pair with `deg P = d ≥ 1`, a phase `φ` with `e^{2iφ} q_{d-1} = p_d` makes the
*inverse* recurrence drop the degree by one; if instead both leading
coefficients vanish, the pair already satisfies the conditions two levels
down and the sequence is padded with the no-op pair
`O(x)e^{i(π/2)Z} · O(x)e^{-i(π/2)Z} = 1`. -/

/-- Leading-coefficient relation from the normalization identity
[Lin22, hermfunc.tex:1219]: `|p_{d+1}|² = |q_d|²` (as `p·p* = q·q*`). -/
private theorem IsQSPPair.leading_coeff_rel {d : ℕ} {P Q : ℂ[X]}
    (h : IsQSPPair (d + 1) P Q) :
    P.coeff (d + 1) * starRingEnd ℂ (P.coeff (d + 1))
      = Q.coeff d * starRingEnd ℂ (Q.coeff d) := by
  have hPb : ∀ m, d + 1 < m → P.coeff m = 0 := fun m hm =>
    h.coeff_P_eq_zero hm
  have hPb' : ∀ m, d + 1 < m → (conjP P).coeff m = 0 := fun m hm => by
    simp [h.coeff_P_eq_zero hm]
  have hQb : ∀ m, d < m → Q.coeff m = 0 := fun m hm =>
    h.coeff_Q_eq_zero (by omega)
  have hQb' : ∀ m, d < m → (conjP Q).coeff m = 0 := fun m hm => by
    simp [h.coeff_Q_eq_zero (m := m) (by omega)]
  have hkey := congrArg (fun R : ℂ[X] => R.coeff (2 * d + 2)) h.norm
  simp only [Polynomial.coeff_add, Polynomial.coeff_one] at hkey
  have e1 : (P * conjP P).coeff (2 * d + 2)
      = P.coeff (d + 1) * starRingEnd ℂ (P.coeff (d + 1)) := by
    rw [coeff_mul_at_bound_add (a := d + 1) (b := d + 1) (by omega) hPb hPb',
      conjP_coeff]
  have e2 : ((1 - X ^ 2) * (Q * conjP Q)).coeff (2 * d + 2)
      = -(Q.coeff d * starRingEnd ℂ (Q.coeff d)) := by
    rw [show ((1 - X ^ 2) * (Q * conjP Q) : ℂ[X])
        = Q * conjP Q - X ^ 2 * (Q * conjP Q) by ring,
      Polynomial.coeff_sub, coeff_X_sq_mul,
      coeff_mul_eq_zero_of_bound_add (a := d) (b := d) (by omega) hQb hQb',
      if_neg (by omega : ¬ (2 * d + 2 < 2)),
      coeff_mul_at_bound_add (a := d) (b := d) (by omega) hQb hQb',
      conjP_coeff]
    ring
  rw [e1, e2, if_neg (by omega : ¬ (2 * d + 2 = 0))] at hkey
  linear_combination hkey

/-- First inverse-recurrence polynomial `e^{-iφ}·X·P + e^{iφ}·(1-X²)·Q`
(with `v = e^{iφ}`, `w = e^{-iφ}`). -/
private def unstepP (v w : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C w * (X * P) + C v * ((1 - X ^ 2) * Q)

/-- Second inverse-recurrence polynomial `e^{iφ}·X·Q - e^{-iφ}·P`. -/
private def unstepQ (v w : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C v * (X * Q) - C w * P

/-- The inverse recurrence inverts `qspMat_step`: applying the step to
`(unstepP, unstepQ)` recovers `P`. -/
private theorem unstep_recover_P (P Q : ℂ[X]) {v w : ℂ} (hvw : v * w = 1) :
    C v * (X * unstepP v w P Q - (1 - X ^ 2) * unstepQ v w P Q) = P := by
  have hCvw : (C v * C w : ℂ[X]) = 1 := by rw [← C_mul, hvw, map_one]
  simp only [unstepP, unstepQ]
  linear_combination (P : ℂ[X]) * hCvw

/-- The inverse recurrence inverts `qspMat_step`: applying the step to
`(unstepP, unstepQ)` recovers `Q`. -/
private theorem unstep_recover_Q (P Q : ℂ[X]) {v w : ℂ} (hvw : v * w = 1) :
    C w * (unstepP v w P Q + X * unstepQ v w P Q) = Q := by
  have hCvw : (C v * C w : ℂ[X]) = 1 := by rw [← C_mul, hvw, map_one]
  simp only [unstepP, unstepQ]
  linear_combination (Q : ℂ[X]) * hCvw

/-- The normalization identity is preserved by the inverse recurrence. -/
private theorem qsp_norm_unstep (P Q : ℂ[X]) (v w : ℂ) (hv : starRingEnd ℂ v = w)
    (hvw : v * w = 1)
    (hnorm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1) :
    unstepP v w P Q * conjP (unstepP v w P Q)
      + (1 - X ^ 2) * (unstepQ v w P Q * conjP (unstepQ v w P Q)) = 1 := by
  have hw : starRingEnd ℂ w = v := by rw [← hv, Complex.conj_conj]
  have hCvw : (C v * C w : ℂ[X]) = 1 := by rw [← C_mul, hvw, map_one]
  simp only [unstepP, unstepQ, conjP_mul, conjP_sub, conjP_add, conjP_C,
    conjP_X, conjP_one, conjP_pow, hv, hw]
  linear_combination (C v * C w : ℂ[X]) * hnorm + hCvw

/-- Degree reduction [Lin22, hermfunc.tex:1226]: if `e^{2iφ} q_d = p_{d+1}`,
the inverse recurrence drops an `IsQSPPair (d+1)` pair to an
`IsQSPPair d` pair. -/
private theorem isQSPPair_unstep {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair (d + 1) P Q)
    {v w : ℂ} (hv : starRingEnd ℂ v = w) (hvw : v * w = 1)
    (hpq : v ^ 2 * Q.coeff d = P.coeff (d + 1)) :
    IsQSPPair d (unstepP v w P Q) (unstepQ v w P Q) := by
  refine isQSPPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_ ?_
    (qsp_norm_unstep P Q v w hv hvw h.norm)
  · rw [unstepP, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, coeff_X_mul',
      show ((1 - X ^ 2) * Q : ℂ[X]) = Q - X ^ 2 * Q by ring,
      Polynomial.coeff_sub, coeff_X_sq_mul]
    rcases Nat.lt_or_ge m (d + 2) with hm2 | hm2
    · have hmeq : m = d + 1 := by omega
      subst hmeq
      have h1 : P.coeff d = 0 := h.parP.coeff_eq_zero (by omega)
      have h2 : Q.coeff (d + 1) = 0 := h.coeff_Q_eq_zero (by omega)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [h1, h2]
      · have h3 : Q.coeff (d - 1) = 0 := h.parQ.coeff_eq_zero (by omega)
        have hlt : ¬ (d + 1 < 2) := by omega
        simp [h1, h2, h3, hlt]
    · rcases Nat.lt_or_ge m (d + 3) with hm3 | hm3
      · have hmeq : m = d + 2 := by omega
        subst hmeq
        have h2 : Q.coeff (d + 2) = 0 := h.coeff_Q_eq_zero (by omega)
        rw [if_neg (by omega : ¬ (d + 2 = 0)),
          if_neg (by omega : ¬ (d + 2 < 2)), h2,
          show d + 2 - 1 = d + 1 by omega, show d + 2 - 2 = d by omega,
          ← hpq]
        linear_combination (v * Q.coeff d) * hvw
      · have h1 : P.coeff (m - 1) = 0 := h.coeff_P_eq_zero (by omega)
        have h2 : Q.coeff m = 0 := h.coeff_Q_eq_zero (by omega)
        have h3 : Q.coeff (m - 2) = 0 := h.coeff_Q_eq_zero (by omega)
        have hlt : ¬ (m < 2) := by omega
        simp [h1, h2, h3, hlt]
  · rw [unstepQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, coeff_X_mul']
    rcases Nat.lt_or_ge m (d + 1) with hm1 | hm1
    · have hmeq : m = d := by omega
      subst hmeq
      rcases Nat.eq_zero_or_pos m with rfl | hd
      · have h1 : P.coeff 0 = 0 := h.parP.coeff_eq_zero (by omega)
        simp [h1]
      · have h1 : P.coeff m = 0 := h.parP.coeff_eq_zero (by omega)
        have h2 : Q.coeff (m - 1) = 0 := h.parQ.coeff_eq_zero (by omega)
        have hne : ¬ (m = 0) := by omega
        simp [h1, h2, hne]
    · rcases Nat.lt_or_ge m (d + 2) with hm2 | hm2
      · have hmeq : m = d + 1 := by omega
        subst hmeq
        rw [if_neg (by omega : ¬ (d + 1 = 0)),
          show d + 1 - 1 = d by omega, ← hpq]
        linear_combination (-(v * Q.coeff d)) * hvw
      · have h1 : P.coeff m = 0 := h.coeff_P_eq_zero (by omega)
        have h2 : Q.coeff (m - 1) = 0 := h.coeff_Q_eq_zero (by omega)
        have hne : ¬ (m = 0) := by omega
        simp [h1, h2, hne]
  · exact ((h.parP.X_mul.congr (by omega)).C_mul w).add
      (((h.parQ.one_sub_X_sq_mul).congr (by omega)).C_mul v)
  · exact ((h.parQ.X_mul.congr (by omega)).C_mul v).sub (h.parP.C_mul w)

/-! ### Padding with a no-op pair -/

private theorem signalO_zmat_sq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (signalO x * !![(1 : ℂ), 0; 0, -1]) * (signalO x * !![(1 : ℂ), 0; 0, -1])
      = 1 := by
  have hs := sq_sqrt_one_sub_sq hx
  ext i j
  fin_cases i <;> fin_cases j
  · simp [signalO, Matrix.mul_apply]
    linear_combination hs
  · simp [signalO, Matrix.mul_apply]
    ring
  · simp [signalO, Matrix.mul_apply]
    ring
  · simp [signalO, Matrix.mul_apply]
    linear_combination hs

private theorem rotZ_pi_div_two :
    (rotZ (Real.pi / 2) : HilbertOperator 1) =
      Complex.I • !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotZOp, exp_neg_pi_div_two_mul_I]

private theorem rotZ_neg_pi_div_two :
    (rotZ (-(Real.pi / 2)) : HilbertOperator 1) =
      (-Complex.I) • !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotZOp, exp_neg_pi_div_two_mul_I]

/-- The signal-phase pairs at `φ = ±π/2` cancel:
`O(x)e^{i(π/2)Z} · O(x)e^{-i(π/2)Z} = 1`. -/
private theorem signalO_rotZ_pair {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (signalO x * rotZ (Real.pi / 2)) * (signalO x * rotZ (-(Real.pi / 2)))
      = 1 := by
  rw [rotZ_pi_div_two, rotZ_neg_pi_div_two, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, signalO_zmat_sq hx]
  simp [Complex.I_mul_I]

/-- Padding a QSP sequence with the no-op pair `(π/2, -π/2)` preserves the
product. -/
private theorem qspO_pad (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspO φ₀ (Real.pi / 2 :: -(Real.pi / 2) :: φs) x = qspO φ₀ φs x := by
  unfold qspO
  rw [List.foldl_cons, List.foldl_cons]
  congr 1
  rw [mul_assoc, signalO_rotZ_pair hx, mul_one]

/-! ### Completeness and the characterization -/

/-- Completeness of QSP [Lin22, hermfunc.tex:1212]: every pair satisfying the
degree, parity, and normalization conditions is realized by a QSP sequence
with exactly `d` signal operators. -/
theorem qspO_converse (d : ℕ) (P Q : ℂ[X]) (h : IsQSPPair d P Q) :
    ∃ (φ₀ : ℝ) (φs : List ℝ), φs.length = d ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspO φ₀ φs x = qspMat P Q x := by
  induction d using Nat.strong_induction_on generalizing P Q with
  | _ d ih =>
  rcases d with - | n
  · -- `d = 0`: `Q = 0` and `P` is a unimodular constant.
    have hQ : Q = 0 := by
      ext k
      rw [Polynomial.coeff_zero]
      exact h.coeff_Q_eq_zero (Nat.zero_le k)
    have hP : P = C (P.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (by exact_mod_cast h.degP)
    have hc : P.coeff 0 * starRingEnd ℂ (P.coeff 0) = 1 := by
      have hnorm := h.norm
      rw [hQ, hP] at hnorm
      simpa using congrArg (fun R : ℂ[X] => R.coeff 0) hnorm
    have hcn : ‖P.coeff 0‖ = 1 := by
      have h1 : ‖P.coeff 0‖ * ‖P.coeff 0‖ = 1 := by
        have := congrArg norm hc
        simpa [norm_mul, Complex.norm_conj] using this
      nlinarith [norm_nonneg (P.coeff 0)]
    refine ⟨(P.coeff 0).arg, [], rfl, fun x _ => ?_⟩
    rw [qspO_nil, hP, hQ]
    refine rotZ_eq_qspMat _ _ x ?_
    have h := Complex.norm_mul_exp_arg_mul_I (P.coeff 0)
    rw [hcn] at h
    simpa using h
  · by_cases hq : Q.coeff n = 0
    · -- Both leading coefficients vanish: drop two levels and pad.
      have hp : P.coeff (n + 1) = 0 := by
        have hrel := h.leading_coeff_rel
        rw [hq] at hrel
        simp only [zero_mul] at hrel
        rcases mul_eq_zero.mp hrel with h' | h'
        · exact h'
        · simpa using congrArg (starRingEnd ℂ) h'
      rcases n with - | m
      · -- `d = 1` with vanishing leading coefficients is impossible.
        exfalso
        have hQ0 : Q = 0 := by
          ext k
          rw [Polynomial.coeff_zero]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · exact hq
          · exact h.coeff_Q_eq_zero (by omega)
        have hP0 : P = 0 := by
          ext k
          rw [Polynomial.coeff_zero]
          match k with
          | 0 => exact h.parP.coeff_eq_zero (by omega)
          | 1 => exact hp
          | (k' + 2) => exact h.coeff_P_eq_zero (by omega)
        have hnorm := h.norm
        rw [hP0, hQ0] at hnorm
        simp at hnorm
      · -- `IsQSPPair (m+2) → IsQSPPair m`, then pad with `(π/2, -π/2)`.
        have hpair : IsQSPPair m P Q := by
          refine isQSPPair_of_coeff (fun k hk => ?_) (fun k hk => ?_)
            (h.parP.congr (by omega)) (h.parQ.congr (by omega)) h.norm
          · rcases Nat.lt_or_ge k (m + 2) with hk2 | hk2
            · exact h.parP.coeff_eq_zero (by omega)
            · rcases Nat.lt_or_ge k (m + 3) with hk3 | hk3
              · have : k = m + 2 := by omega
                subst this
                exact hp
              · exact h.coeff_P_eq_zero (by omega)
          · rcases Nat.lt_or_ge k (m + 1) with hk1 | hk1
            · have : k = m := by omega
              subst this
              exact h.parQ.coeff_eq_zero (by omega)
            · rcases Nat.lt_or_ge k (m + 2) with hk2 | hk2
              · have : k = m + 1 := by omega
                subst this
                exact hq
              · exact h.coeff_Q_eq_zero (by omega)
        obtain ⟨φ₀, φs, hlen, hmat⟩ := ih m (by omega) P Q hpair
        refine ⟨φ₀, Real.pi / 2 :: -(Real.pi / 2) :: φs, by simp [hlen],
          fun x hx => ?_⟩
        rw [qspO_pad φ₀ φs hx, hmat x hx]
    · -- Nonzero leading coefficient: reduce the degree by one step.
      obtain ⟨φ, hφ⟩ := exists_exp_sq_eq hq h.leading_coeff_rel
      have hpair' := isQSPPair_unstep h (conj_exp_I φ)
        (exp_I_mul_exp_neg_I φ) hφ
      obtain ⟨φ₀, φs, hlen, hmat⟩ := ih n (by omega) _ _ hpair'
      refine ⟨φ₀, φs ++ [φ], by simp [hlen], fun x hx => ?_⟩
      rw [qspO_concat, hmat x hx, qspMat_step _ _ φ hx,
        unstep_recover_P P Q (exp_I_mul_exp_neg_I φ),
        unstep_recover_Q P Q (exp_I_mul_exp_neg_I φ)]

/-- Two QSP forms agreeing on `[-1,1]` have equal polynomial pairs
(`[-1,1]` is infinite and `√(1-x²) ≠ 0` on the interior). -/
private theorem qspMat_inj {P Q P' Q' : ℂ[X]}
    (hmat : ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspMat P Q x = qspMat P' Q' x) :
    P = P' ∧ Q = Q' := by
  constructor
  · refine Polynomial.eq_of_infinite_eval_eq P P' ?_
    refine (((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn).mono ?_)
    rintro z ⟨x, hx, rfl⟩
    have h := congrArg (fun M : HilbertOperator 1 => M 0 0) (hmat x hx)
    simpa [qspMat] using h
  · refine Polynomial.eq_of_infinite_eval_eq Q Q' ?_
    refine (((Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn).mono ?_)
    rintro z ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hs : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      refine Real.sqrt_ne_zero'.mpr ?_
      nlinarith [hx.1, hx.2]
    have h := congrArg (fun M : HilbertOperator 1 => M 0 1) (hmat x hx')
    simp only [qspMat] at h
    have h' : Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ)
        = Q'.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ) := by
      have := h
      simp only [neg_mul] at this
      exact neg_injective this
    exact mul_right_cancel₀ hs h'

/-- The polynomial normalization identity is equivalent to the pointwise
normalization `|P(x)|² + (1-x²)|Q(x)|² = 1` on `[-1,1]`
[Lin22, hermfunc.tex:1134]. -/
theorem qsp_normalization_iff (P Q : ℂ[X]) :
    P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1 ↔
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        P.eval (x : ℂ) * starRingEnd ℂ (P.eval (x : ℂ))
          + (1 - (x : ℂ) ^ 2) *
            (Q.eval (x : ℂ) * starRingEnd ℂ (Q.eval (x : ℂ))) = 1 := by
  constructor
  · intro hid x hx
    have h := congrArg (Polynomial.eval (x : ℂ)) hid
    simpa [conjP_eval_ofReal] using h
  · intro hpt
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine (((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn).mono ?_)
    rintro z ⟨x, hx, rfl⟩
    have h := hpt x hx
    simp only [Set.mem_setOf_eq]
    simpa [conjP_eval_ofReal] using h

/-- **Quantum signal processing, reflection convention**
[Lin22, hermfunc.tex:1118] ([GSLW19, BlockHam.tex:313] in the `W`-convention):
a pair `(P, Q)` satisfies the degree, parity, and normalization conditions
`IsQSPPair d` **iff** some phase factors `(φ₀, φs)` with `d` signal operators
realize the matrix form
`[[P(x), -Q(x)√(1-x²)], [Q*(x)√(1-x²), P*(x)]]` on `[-1,1]`. -/
theorem ReflectionBasedQuantumSignalProcessing.main (d : ℕ) (P Q : ℂ[X]) :
    IsQSPPair d P Q ↔
      ∃ (φ₀ : ℝ) (φs : List ℝ), φs.length = d ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspO φ₀ φs x = qspMat P Q x := by
  constructor
  · exact qspO_converse d P Q
  · rintro ⟨φ₀, φs, rfl, hmat⟩
    obtain ⟨P', Q', hpair, hmat'⟩ := qspO_forward φ₀ φs
    have hPQ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspMat P Q x = qspMat P' Q' x :=
      fun x hx => by rw [← hmat x hx, hmat' x hx]
    obtain ⟨hP, hQ⟩ := qspMat_inj hPQ
    rw [hP, hQ]
    exact hpair

/-! ### The Wx-convention (XZX form)

The `Wx`-convention of [GSLW19, BlockHam.tex:295] uses the signal rotation
`W(x) = e^{i·arccos(x)·X}` in place of `O(x)`. The two are related by the
fixed conjugation `W(x) = e^{-i(π/4)Z} · O(x) · e^{i(π/4)Z}`
[Lin22, hermfunc.tex:1279], so the characterization
[GSLW19, BlockHam.tex:313] (`thm:basicCharacterisation`) transports verbatim
from `qsp_reflection_iff` with the *same* pair conditions `IsQSPPair`. -/

/-- The `Wx` signal rotation
`W(x) = [[x, i√(1-x²)], [i√(1-x²), x]] = e^{i·arccos(x)·X}`
[GSLW19, BlockHam.tex:295]. -/
def signalW (x : ℝ) : HilbertOperator 1 :=
  !![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ);
     Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- The Wx-convention QSP sequence `e^{iφ₀Z} ∏_j (W(x) e^{iφ_jZ})`
[GSLW19, BlockHam.tex:317]. -/
def qspW (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) : HilbertOperator 1 :=
  φs.foldl (fun U φ => U * (signalW x * rotZ φ)) (rotZ φ₀ : HilbertOperator 1)

@[simp]
theorem qspW_nil (φ₀ : ℝ) (x : ℝ) : qspW φ₀ [] x = rotZ φ₀ := rfl

theorem qspW_concat (φ₀ : ℝ) (φs : List ℝ) (φ : ℝ) (x : ℝ) :
    qspW φ₀ (φs ++ [φ]) x = qspW φ₀ φs x * (signalW x * rotZ φ) := by
  simp [qspW, List.foldl_append]

private theorem rotZ_comm_op (a b : ℝ) :
    (rotZ a : HilbertOperator 1) * (rotZ b : HilbertOperator 1) =
      (rotZ b : HilbertOperator 1) * (rotZ a : HilbertOperator 1) := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_comm a b)

private theorem rotZ_neg_mul_rotZ_op (φ : ℝ) :
    (rotZ (-φ) : HilbertOperator 1) * (rotZ φ : HilbertOperator 1) = 1 := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_neg_mul_rotZ φ)

private theorem rotZ_mul_rotZ_neg_op (φ : ℝ) :
    (rotZ φ : HilbertOperator 1) * (rotZ (-φ) : HilbertOperator 1) = 1 := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_mul_rotZ_neg φ)

/-- The Wx target form `[[P(x), iQ(x)s], [iQ*(x)s, P*(x)]]`, `s = √(1-x²)`
[GSLW19, BlockHam.tex:313]. -/
def qspMatW (P Q : ℂ[X]) (x : ℝ) : HilbertOperator 1 :=
  !![P.eval (x : ℂ),
     Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
     Complex.I * starRingEnd ℂ (Q.eval (x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ),
     starRingEnd ℂ (P.eval (x : ℂ))]

/-- The fixed conjugation relating the two signal operators,
`e^{i(π/4)Z} · W(x) = O(x) · e^{i(π/4)Z}` [Lin22, hermfunc.tex:1279]. -/
private theorem rotZ_mul_signalW (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * signalW x =
      signalO x * rotZ (Real.pi / 4) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    ring
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    linear_combination ((Real.sqrt (1 - x ^ 2) : ℂ)) * exp_pi_div_four_mul_I
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    linear_combination ((Real.sqrt (1 - x ^ 2) : ℂ)) *
      exp_neg_pi_div_four_mul_I
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    ring

/-- The conjugation transports the Wx target form to the reflection form. -/
private theorem rotZ_mul_qspMatW (P Q : ℂ[X]) (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * qspMatW P Q x =
      qspMat P Q x * rotZ (Real.pi / 4) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    ring
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    linear_combination (Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ)) *
      exp_pi_div_four_mul_I
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    linear_combination (starRingEnd ℂ (Q.eval (x : ℂ)) *
      (Real.sqrt (1 - x ^ 2) : ℂ)) * exp_neg_pi_div_four_mul_I
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    ring

/-- The conjugation intertwines the full QSP sequences:
`e^{i(π/4)Z} · U^W_Φ(x) = U^O_Φ(x) · e^{i(π/4)Z}`. -/
private theorem rotZ_mul_qspW (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * qspW φ₀ φs x =
      qspO φ₀ φs x * rotZ (Real.pi / 4) := by
  induction φs using List.reverseRecOn with
  | nil => simpa using rotZ_comm_op (Real.pi / 4) φ₀
  | append_singleton φs φ ih =>
      rw [qspW_concat, qspO_concat, ← mul_assoc, ih, mul_assoc,
        ← mul_assoc (rotZ (Real.pi / 4) : HilbertOperator 1) (signalW x)
          (rotZ φ : HilbertOperator 1),
        rotZ_mul_signalW, mul_assoc (signalO x)
          (rotZ (Real.pi / 4) : HilbertOperator 1) (rotZ φ : HilbertOperator 1),
        rotZ_comm_op (Real.pi / 4) φ,
        ← mul_assoc (signalO x) (rotZ φ : HilbertOperator 1)
          (rotZ (Real.pi / 4) : HilbertOperator 1),
        ← mul_assoc]

theorem signalW_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    signalW x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have h : signalW x = (rotZ (-(Real.pi / 4)) : HilbertOperator 1) *
      (signalO x * rotZ (Real.pi / 4)) := by
    rw [← rotZ_mul_signalW, ← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]
  rw [h]
  exact mul_mem (rotZ_mem_unitaryGroup _)
    (mul_mem (signalO_mem_unitaryGroup hx) (rotZ_mem_unitaryGroup _))

theorem qspW_mem_unitaryGroup (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspW φ₀ φs x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  induction φs using List.reverseRecOn with
  | nil => exact rotZ_mem_unitaryGroup φ₀
  | append_singleton φs φ ih =>
      rw [qspW_concat]
      exact mul_mem ih (mul_mem (signalW_mem_unitaryGroup hx)
        (rotZ_mem_unitaryGroup φ))

/-- Pointwise, the Wx form holds iff the reflection form holds (conjugation
by the unit `e^{i(π/4)Z}`). -/
theorem qspW_form_iff (φ₀ : ℝ) (φs : List ℝ) (P Q : ℂ[X]) (x : ℝ) :
    qspW φ₀ φs x = qspMatW P Q x ↔ qspO φ₀ φs x = qspMat P Q x := by
  constructor
  · intro h
    calc qspO φ₀ φs x
        = (rotZ (Real.pi / 4) * qspW φ₀ φs x) * rotZ (-(Real.pi / 4)) := by
          rw [rotZ_mul_qspW, mul_assoc, rotZ_mul_rotZ_neg_op, mul_one]
      _ = (rotZ (Real.pi / 4) * qspMatW P Q x) * rotZ (-(Real.pi / 4)) := by
          rw [h]
      _ = qspMat P Q x := by
          rw [rotZ_mul_qspMatW, mul_assoc, rotZ_mul_rotZ_neg_op, mul_one]
  · intro h
    calc qspW φ₀ φs x
        = rotZ (-(Real.pi / 4)) * (rotZ (Real.pi / 4) * qspW φ₀ φs x) := by
          rw [← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]
      _ = rotZ (-(Real.pi / 4)) * (qspMat P Q x * rotZ (Real.pi / 4)) := by
          rw [rotZ_mul_qspW, h]
      _ = rotZ (-(Real.pi / 4)) * (rotZ (Real.pi / 4) * qspMatW P Q x) := by
          rw [rotZ_mul_qspMatW]
      _ = qspMatW P Q x := by
          rw [← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]

/-- **Quantum signal processing, Wx-convention (XZX form)**
[GSLW19, BlockHam.tex:313] (`thm:basicCharacterisation`): a pair `(P, Q)`
satisfies `IsQSPPair d` **iff** some phase factors `(φ₀, φs)` with `d` signal
operators realize the matrix form
`[[P(x), iQ(x)√(1-x²)], [iQ*(x)√(1-x²), P*(x)]]` on `[-1,1]`. -/
theorem ReflectionBasedQuantumSignalProcessing.main_wx (d : ℕ) (P Q : ℂ[X]) :
    IsQSPPair d P Q ↔
      ∃ (φ₀ : ℝ) (φs : List ℝ), φs.length = d ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspW φ₀ φs x = qspMatW P Q x := by
  rw [ReflectionBasedQuantumSignalProcessing.main]
  constructor
  · rintro ⟨φ₀, φs, hlen, hmat⟩
    exact ⟨φ₀, φs, hlen,
      fun x hx => (qspW_form_iff φ₀ φs P Q x).mpr (hmat x hx)⟩
  · rintro ⟨φ₀, φs, hlen, hmat⟩
    exact ⟨φ₀, φs, hlen,
      fun x hx => (qspW_form_iff φ₀ φs P Q x).mp (hmat x hx)⟩

end

end QuantumAlg
