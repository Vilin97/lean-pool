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
# Quantum signal processing (single qubit) — Fourier basis (trigonometric)

The Fourier-basis single-qubit QSP characterizations: the **YZY** and
**YZZYZ (W-Z-W)** quantum-neural-network forms of [YYLW22,
neurips_2022.tex:283] and [YYLW22, neurips_2022.tex:333]. These use the
encoding rotation `R_Z(x) = e^{-ixZ/2}` and trainable `R_Y`/`R_Z` gates (all in
`Core.Components.Gates`), and produce *Laurent* polynomials in `e^{ix/2}`.

A Laurent polynomial of degree `≤ L` and parity `L mod 2` is exactly
`e^{-iLx/2}·A(e^{ix})` for a unique ordinary `A : ℂ[X]` with `deg A ≤ L`,
encoded here by `lEval L A x`. Under this encoding, conjugation on the unit
circle is the conjugate-reflection `A ↦ reflect L (conjP A)` (`conj_lEval`),
and the pointwise normalization becomes the polynomial identity
`A·reflect L (conjP A) + B·reflect L (conjP B) = X^L`
(`qspYZ_normalization_iff`).

`LeanPool.LeanQuantumAlg.qsp_yzy_iff` and
`LeanPool.LeanQuantumAlg.qsp_yzzyz_iff` are the YZY and YZZYZ
characterizations, with pair conditions `IsYZYPair`/`IsYZPair` and a
Laurent-side induction (this is the single-qubit precursor of the
controlled-unitary / QET-QPP transformations). The polynomial normalization
matches the pointwise `|P|² + |Q|² = 1` via
`LeanPool.LeanQuantumAlg.qspYZ_normalization_iff`.

This module is one half of the single-qubit QSP development; the Chebyshev-basis
(reflection + Wx) forms live in
`LeanPool.LeanQuantumAlg.Primitives.QSP.Chebyshev`, and
`LeanPool.LeanQuantumAlg.Primitives.QSP` re-exports both.

## Main results

- `LeanPool.LeanQuantumAlg.qspYZY_mem_unitaryGroup`,
  `LeanPool.LeanQuantumAlg.qspYZZYZ_mem_unitaryGroup`
  — the QNN products are unitary.
- `LeanPool.LeanQuantumAlg.qspYZZYZ_forward` /
  `LeanPool.LeanQuantumAlg.qspYZZYZ_converse` and
  `LeanPool.LeanQuantumAlg.qspYZY_forward` /
  `LeanPool.LeanQuantumAlg.qspYZY_converse` — soundness and completeness via
  Laurent-encoded induction.
- `LeanPool.LeanQuantumAlg.qsp_yzzyz_iff`,
  `LeanPool.LeanQuantumAlg.qsp_yzy_iff` — the trigonometric characterizations
  (registered targets).

Pinned Mathlib API: `Polynomial.reflect`, `Polynomial.divX`,
`Complex.exp_mul_I`, `Complex.norm_mul_exp_arg_mul_I`,
`Complex.exp_eq_exp_iff_exists_int`, `Complex.cos_arg`, `Complex.sin_arg`,
`Set.Ioo.infinite`, `List.reverseRecOn`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

/-! ### Trigonometric QSP: the YZY and YZZYZ (W-Z-W) forms

[YYLW22, neurips_2022.tex:283] and [YYLW22, neurips_2022.tex:333]
characterize the single-qubit QNNs `R_Y(θ₀)·∏_j R_Z(x)R_Y(θ_j)` and
`R_Z(φ)·W(θ₀,φ₀)·∏_j R_Z(x)W(θ_j,φ_j)` (with `W(θ,φ) = R_Y(θ)R_Z(φ)` and
encoding gate `R_Z(x) = e^{-ixZ/2}`) through *Laurent* polynomials
`P, Q ∈ ℂ[e^{ix/2}, e^{-ix/2}]` with degree `≤ L`, parity `L mod 2`, and
`|P(x)|² + |Q(x)|² = 1` on `ℝ`.

A Laurent polynomial of degree `≤ L` and parity `L mod 2` has exponent
support in `{-L, -L+2, …, L}`, so it is exactly `e^{-iLx/2}·A(e^{ix})` for a
unique ordinary `A : ℂ[X]` with `deg A ≤ L` (`lEval` below). Under this
encoding, conjugation on the unit circle becomes the conjugate-reflection
`A ↦ reflect L (conjP A)` (`conj_lEval`), and the pointwise normalization
becomes the polynomial identity
`A·reflect L (conjP A) + B·reflect L (conjP B) = X^L`
(`qspYZ_normalization_iff`). -/

/-- `e^{-iLx/2}·F(e^{ix})`: the value at `z = e^{ix/2}` of the Laurent
polynomial `z^{-L}·F(z²)` encoded by `F : ℂ[X]`. -/
def lEval (L : ℕ) (F : ℂ[X]) (x : ℝ) : ℂ :=
  Complex.exp (-((L * x / 2 : ℝ) * Complex.I)) *
    F.eval (Complex.exp ((x : ℂ) * Complex.I))

theorem lEval_C_mul (L : ℕ) (c : ℂ) (F : ℂ[X]) (x : ℝ) :
    lEval L (C c * F) x = c * lEval L F x := by
  rw [lEval, lEval, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem lEval_add (L : ℕ) (F G : ℂ[X]) (x : ℝ) :
    lEval L (F + G) x = lEval L F x + lEval L G x := by
  rw [lEval, lEval, lEval, Polynomial.eval_add]
  ring

theorem lEval_sub (L : ℕ) (F G : ℂ[X]) (x : ℝ) :
    lEval L (F - G) x = lEval L F x - lEval L G x := by
  rw [lEval, lEval, lEval, Polynomial.eval_sub]
  ring

/-- Raising the parity budget multiplies the encoded value by `e^{-ix/2}`. -/
theorem lEval_succ (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    lEval (L + 1) F x
      = Complex.exp (-(((x / 2 : ℝ) : ℂ) * Complex.I)) * lEval L F x := by
  rw [lEval, lEval, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Raising the budget while multiplying by `X` multiplies by `e^{ix/2}`. -/
theorem lEval_succ_X_mul (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    lEval (L + 1) (X * F) x
      = Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * lEval L F x := by
  rw [lEval, lEval, Polynomial.eval_mul, Polynomial.eval_X, ← mul_assoc,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The encoded value of a constant at budget `0`. -/
theorem lEval_zero_C (c : ℂ) (x : ℝ) : lEval 0 (C c) x = c := by
  rw [lEval, Polynomial.eval_C]
  norm_num

/-- Conjugating the encoded value reflects the conjugated coefficients. -/
theorem conj_lEval {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) (x : ℝ) :
    starRingEnd ℂ (lEval L F x) = lEval L ((conjP F).reflect L) x := by
  have hw : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hFc : (conjP F).natDegree ≤ L :=
    le_trans (Polynomial.natDegree_map_le) hF
  have h1 : (conjP F).eval (Complex.exp (-((x : ℂ) * Complex.I)))
      = starRingEnd ℂ (F.eval (Complex.exp ((x : ℂ) * Complex.I))) := by
    rw [← conj_exp_I, conjP, Polynomial.eval_map, Polynomial.eval₂_hom]
  rw [lEval, map_mul, conj_exp_neg_I, ← h1, lEval, eval_reflect hFc hw,
    ← Complex.exp_neg, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! #### Gates and products -/

/-- The YZY QNN `U^{YZY}_{θ,L}(x) = R_Y(θ₀)·∏_{j=1}^L R_Z(x)·R_Y(θ_j)`
[YYLW22, neurips_2022.tex:266]. -/
def qspYZY (θ₀ : ℝ) (θs : List ℝ) (x : ℝ) : Gate 1 :=
  θs.foldl (fun U θ => U * (rotZStd x * rotY θ)) (rotY θ₀)

@[simp]
theorem qspYZY_nil (θ₀ : ℝ) (x : ℝ) : qspYZY θ₀ [] x = rotY θ₀ := rfl

theorem qspYZY_concat (θ₀ : ℝ) (θs : List ℝ) (θ : ℝ) (x : ℝ) :
    qspYZY θ₀ (θs ++ [θ]) x = qspYZY θ₀ θs x * (rotZStd x * rotY θ) := by
  simp [qspYZY, List.foldl_append]

/-- The YZZYZ (W-Z-W) QNN
`U^{WZW}_{θ,φ,L}(x) = R_Z(φ)·W(θ₀,φ₀)·∏_{j=1}^L R_Z(x)·W(θ_j,φ_j)` with
trainable blocks `W(θ,φ) = R_Y(θ)·R_Z(φ)` [YYLW22, neurips_2022.tex:316]. -/
def qspYZZYZ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (x : ℝ) : Gate 1 :=
  ps.foldl (fun U p => U * (rotZStd x * (rotY p.1 * rotZStd p.2)))
    (rotZStd φ * (rotY θ₀ * rotZStd φ₀))

@[simp]
theorem qspYZZYZ_nil (φ θ₀ φ₀ : ℝ) (x : ℝ) :
    qspYZZYZ φ θ₀ φ₀ [] x = rotZStd φ * (rotY θ₀ * rotZStd φ₀) := rfl

theorem qspYZZYZ_concat (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (p : ℝ × ℝ)
    (x : ℝ) :
    qspYZZYZ φ θ₀ φ₀ (ps ++ [p]) x
      = qspYZZYZ φ θ₀ φ₀ ps x * (rotZStd x * (rotY p.1 * rotZStd p.2)) := by
  simp [qspYZZYZ, List.foldl_append]

/-- The YZY product is the `φ = φ₀ = 0` special case of the YZZYZ product: it
sets every `R_Z` processing angle in the trainable blocks to `0`. This is the
gate-level form of "YZZYZ subsumes YZY" — the encoding/normalization theory of
the trigonometric family is shared, and the two characterizations differ only
in their completeness arguments (one real angle per block vs. three SU(2)
angles). -/
theorem qspYZY_eq_qspYZZYZ (θ₀ : ℝ) (θs : List ℝ) (x : ℝ) :
    qspYZY θ₀ θs x = qspYZZYZ 0 θ₀ 0 (θs.map (fun t => (t, (0 : ℝ)))) x := by
  induction θs using List.reverseRecOn with
  | nil =>
      rw [List.map_nil, qspYZY_nil, qspYZZYZ_nil, rotZStd_zero, one_mul, mul_one]
  | append_singleton θs θ ih =>
      rw [qspYZY_concat, ih,
        show (θs ++ [θ]).map (fun t => (t, (0 : ℝ)))
            = θs.map (fun t => (t, (0 : ℝ))) ++ [(θ, 0)] by simp,
        qspYZZYZ_concat, rotZStd_zero, mul_one]

/-- The trigonometric QSP target form `[[P, -Q], [Q*, P*]]` with
`P = e^{-iLx/2}·A(e^{ix})` and `Q = e^{-iLx/2}·B(e^{ix})`
[YYLW22, neurips_2022.tex:286]. -/
def qspMatYZ (L : ℕ) (A B : ℂ[X]) (x : ℝ) : HilbertOperator 1 :=
  !![lEval L A x, -lEval L B x;
     starRingEnd ℂ (lEval L B x), starRingEnd ℂ (lEval L A x)]

/-! #### The pair conditions and the one-step recurrence -/

/-- Conditions of [YYLW22, neurips_2022.tex:333] in the encoded form: degree
bounds and the circle normalization
`A·reflect L (conjP A) + B·reflect L (conjP B) = X^L`, the polynomial form of
`|P(x)|² + |Q(x)|² = 1` on `ℝ` (`qspYZ_normalization_iff`). Degree `≤ L` and
parity `L mod 2` of the Laurent pair are built into the encoding. -/
structure IsYZPair (L : ℕ) (A B : ℂ[X]) : Prop where
  degA : A.degree ≤ L
  degB : B.degree ≤ L
  norm : A * (conjP A).reflect L + B * (conjP B).reflect L = X ^ L

/-- The YZY pair conditions [YYLW22, neurips_2022.tex:283]: an `IsYZPair`
with real coefficients. -/
structure IsYZYPair (L : ℕ) (A B : ℂ[X]) : Prop extends IsYZPair L A B where
  realA : conjP A = A
  realB : conjP B = B

theorem IsYZPair.coeff_A_eq_zero {L : ℕ} {A B : ℂ[X]} (h : IsYZPair L A B)
    {m : ℕ} (hm : L < m) : A.coeff m = 0 :=
  (Polynomial.degree_le_iff_coeff_zero A L).mp h.degA m (by exact_mod_cast hm)

theorem IsYZPair.coeff_B_eq_zero {L : ℕ} {A B : ℂ[X]} (h : IsYZPair L A B)
    {m : ℕ} (hm : L < m) : B.coeff m = 0 :=
  (Polynomial.degree_le_iff_coeff_zero B L).mp h.degB m (by exact_mod_cast hm)

theorem IsYZPair.natDegA {L : ℕ} {A B : ℂ[X]} (h : IsYZPair L A B) :
    A.natDegree ≤ L := Polynomial.natDegree_le_iff_degree_le.mpr h.degA

theorem IsYZPair.natDegB {L : ℕ} {A B : ℂ[X]} (h : IsYZPair L A B) :
    B.natDegree ≤ L := Polynomial.natDegree_le_iff_degree_le.mpr h.degB

/-- Build the degree conditions from coefficient bounds. -/
theorem isYZPair_of_coeff {L : ℕ} {A B : ℂ[X]}
    (hA : ∀ m, L < m → A.coeff m = 0) (hB : ∀ m, L < m → B.coeff m = 0)
    (norm : A * (conjP A).reflect L + B * (conjP B).reflect L = X ^ L) :
    IsYZPair L A B := by
  refine ⟨?_, ?_, norm⟩
  · exact (Polynomial.degree_le_iff_coeff_zero A L).mpr fun m hm =>
      hA m (by exact_mod_cast hm)
  · exact (Polynomial.degree_le_iff_coeff_zero B L).mpr fun m hm =>
      hB m (by exact_mod_cast hm)

/-- The reflected conjugate of the stepped pair, in closed form. -/
private theorem reflect_conjP_step {L : ℕ} {F G : ℂ[X]} (hF : F.natDegree ≤ L)
    (hG : G.natDegree ≤ L) (v w : ℂ) :
    (conjP (C (starRingEnd ℂ v) * F + C w * (X * G))).reflect (L + 1)
      = C v * (X * (conjP F).reflect L) + C (starRingEnd ℂ w)
          * (conjP G).reflect L := by
  have hFc : (conjP F).natDegree ≤ L := le_trans Polynomial.natDegree_map_le hF
  have hGc : (conjP G).natDegree ≤ L := le_trans Polynomial.natDegree_map_le hG
  rw [conjP_add, conjP_mul, conjP_mul, conjP_C, conjP_C, Complex.conj_conj,
    conjP_mul, conjP_X, reflect_add', Polynomial.reflect_C_mul,
    Polynomial.reflect_C_mul, reflect_succ hFc, reflect_X_mul hGc]

/-- The normalization combination transforms by a factor
`(v·v* + w·w*)·X` under one recurrence step: a pure ring identity. -/
private theorem yz_norm_step {L : ℕ} {A B : ℂ[X]} (hA : A.natDegree ≤ L)
    (hB : B.natDegree ≤ L) (v w : ℂ) :
    (C (starRingEnd ℂ v) * A - C w * (X * B))
        * (conjP (C (starRingEnd ℂ v) * A - C w * (X * B))).reflect (L + 1)
      + (C (starRingEnd ℂ w) * A + C v * (X * B))
        * (conjP (C (starRingEnd ℂ w) * A + C v * (X * B))).reflect (L + 1)
      = (C v * C (starRingEnd ℂ v) + C w * C (starRingEnd ℂ w))
        * (X * (A * (conjP A).reflect L + B * (conjP B).reflect L)) := by
  have h1 : (C (starRingEnd ℂ v) * A - C w * (X * B) : ℂ[X])
      = C (starRingEnd ℂ v) * A + C (-w) * (X * B) := by
    rw [map_neg]; ring
  rw [h1, reflect_conjP_step hA hB v (-w), reflect_conjP_step hA hB w v]
  simp only [map_neg]
  ring

/-- One-step closure of the YZ pair conditions under the recurrence
`(A, B) ↦ (v*·A - w·X·B, w*·A + v·X·B)` for a unit pair `(v, w)`. -/
private theorem IsYZPair.step {L : ℕ} {A B : ℂ[X]} (h : IsYZPair L A B) (v w : ℂ)
    (hvw : v * starRingEnd ℂ v + w * starRingEnd ℂ w = 1) :
    IsYZPair (L + 1) (C (starRingEnd ℂ v) * A - C w * (X * B))
      (C (starRingEnd ℂ w) * A + C v * (X * B)) := by
  have hC : (C v * C (starRingEnd ℂ v) + C w * C (starRingEnd ℂ w) : ℂ[X])
      = 1 := by
    rw [← C_mul, ← C_mul, ← C_add, hvw, map_one]
  refine isYZPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_
  · have h1 : A.coeff m = 0 := h.coeff_A_eq_zero (by omega)
    have h2 : B.coeff (m - 1) = 0 := h.coeff_B_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    simp [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_X_mul', h1, h2,
      hm0]
  · have h1 : A.coeff m = 0 := h.coeff_A_eq_zero (by omega)
    have h2 : B.coeff (m - 1) = 0 := h.coeff_B_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_X_mul', h1, h2,
      hm0]
  · rw [yz_norm_step h.natDegA h.natDegB v w, h.norm, hC]
    ring

/-- One trainable+encoding block in the encoded form: right-multiplying by
`R_Z(x)·R_Y(θ)·R_Z(φ)` maps the form `(A, B)` to
`(v*·A - w·X·B, w*·A + v·X·B)` where `v = cos(θ/2)·e^{iφ/2}` and
`w = sin(θ/2)·e^{-iφ/2}` [YYLW22, neurips_2022.tex:806]. -/
private theorem qspMatYZ_step (L : ℕ) (A B : ℂ[X]) (θ φ : ℝ) (x : ℝ) {v w : ℂ}
    (hv : (Real.cos (θ / 2) : ℂ)
      * Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) = v)
    (hw : (Real.sin (θ / 2) : ℂ)
      * Complex.exp (-(((φ / 2 : ℝ) : ℂ) * Complex.I)) = w) :
    qspMatYZ L A B x * (rotZStd x * (rotY θ * rotZStd φ) : Gate 1)
      = qspMatYZ (L + 1) (C (starRingEnd ℂ v) * A - C w * (X * B))
          (C (starRingEnd ℂ w) * A + C v * (X * B)) x := by
  have hcv : (Real.cos (θ / 2) : ℂ)
      * Complex.exp (-(((φ / 2 : ℝ) : ℂ) * Complex.I)) = starRingEnd ℂ v := by
    rw [← hv, map_mul, Complex.conj_ofReal, conj_exp_I]
  have hcw : (Real.sin (θ / 2) : ℂ)
      * Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) = starRingEnd ℂ w := by
    rw [← hw, map_mul, Complex.conj_ofReal, conj_exp_neg_I]
  have hA' : lEval (L + 1) (C (starRingEnd ℂ v) * A - C w * (X * B)) x
      = starRingEnd ℂ v
          * (Complex.exp (-(((x / 2 : ℝ) : ℂ) * Complex.I)) * lEval L A x)
        - w * (Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * lEval L B x) := by
    rw [lEval_sub, lEval_C_mul, lEval_C_mul, lEval_succ, lEval_succ_X_mul]
  have hB' : lEval (L + 1) (C (starRingEnd ℂ w) * A + C v * (X * B)) x
      = starRingEnd ℂ w
          * (Complex.exp (-(((x / 2 : ℝ) : ℂ) * Complex.I)) * lEval L A x)
        + v * (Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * lEval L B x) := by
    rw [lEval_add, lEval_C_mul, lEval_C_mul, lEval_succ, lEval_succ_X_mul]
  have hcA' := congrArg (starRingEnd ℂ) hA'
  have hcB' := congrArg (starRingEnd ℂ) hB'
  simp only [map_sub, map_add, map_mul, conj_exp_I, conj_exp_neg_I,
    Complex.conj_conj] at hcA' hcB'
  unfold qspMatYZ rotZStd rotZ rotY
  rw [hcA', hcB', hA', hB', ← hcv, ← hcw, ← hv, ← hw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, rotZOp, rotYOp]
      ring

/-- The initial block `R_Z(φ)·R_Y(θ₀)·R_Z(φ₀)` is the `L = 0` instance of
the form, with constants `a = cos(θ₀/2)e^{-i(φ+φ₀)/2}` and
`b = sin(θ₀/2)e^{-i(φ-φ₀)/2}` [YYLW22, neurips_2022.tex:804]. -/
private theorem rotYZ_base_eq_qspMatYZ (φ θ₀ φ₀ : ℝ) (a b : ℂ) (x : ℝ)
    (ha : (Real.cos (θ₀ / 2) : ℂ)
      * Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)) = a)
    (hb : (Real.sin (θ₀ / 2) : ℂ)
      * Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I)) = b) :
    (rotZStd φ * (rotY θ₀ * rotZStd φ₀) : Gate 1) =
      qspMatYZ 0 (C a) (C b) x := by
  have hca : (Real.cos (θ₀ / 2) : ℂ)
      * Complex.exp ((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)
        = starRingEnd ℂ a := by
    rw [← ha, map_mul, Complex.conj_ofReal, conj_exp_neg_I]
  have hcb : (Real.sin (θ₀ / 2) : ℂ)
      * Complex.exp ((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I)
        = starRingEnd ℂ b := by
    rw [← hb, map_mul, Complex.conj_ofReal, conj_exp_neg_I]
  have hadd : Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-(((φ / 2 : ℝ) : ℂ) * Complex.I))
        * Complex.exp (-(((φ₀ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hsub : Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-(((φ / 2 : ℝ) : ℂ) * Complex.I))
        * Complex.exp ((((φ₀ / 2 : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hadd' : Complex.exp ((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((φ / 2 : ℝ) : ℂ)) * Complex.I)
        * Complex.exp ((((φ₀ / 2 : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hsub' : Complex.exp ((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((φ / 2 : ℝ) : ℂ)) * Complex.I)
        * Complex.exp (-(((φ₀ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  unfold qspMatYZ rotZStd rotZ rotY
  rw [lEval_zero_C, lEval_zero_C, ← hca, ← hcb, ← ha, ← hb, hadd, hsub, hadd',
    hsub']
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, rotZOp, rotYOp]
      ring

/-! #### Soundness of the YZY and YZZYZ forms -/

/-- Soundness for the YZZYZ form: every `qspYZZYZ` product realizes the
target form for a pair satisfying the conditions
[YYLW22, neurips_2022.tex:333, forward direction]. -/
theorem qspYZZYZ_forward (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    ∃ A B : ℂ[X], IsYZPair ps.length A B ∧
      ∀ x : ℝ, qspYZZYZ φ θ₀ φ₀ ps x = qspMatYZ ps.length A B x := by
  induction ps using List.reverseRecOn with
  | nil =>
      simp only [List.length_nil]
      have habs : ((Real.cos (θ₀ / 2) : ℂ)
            * Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)))
            * starRingEnd ℂ ((Real.cos (θ₀ / 2) : ℂ)
              * Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)))
          + ((Real.sin (θ₀ / 2) : ℂ)
            * Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I)))
            * starRingEnd ℂ ((Real.sin (θ₀ / 2) : ℂ)
              * Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I))) = 1 := by
        simp only [map_mul, Complex.conj_ofReal, conj_exp_neg_I]
        linear_combination
          (Real.cos (θ₀ / 2) : ℂ) * (Real.cos (θ₀ / 2) : ℂ)
              * exp_neg_I_mul_exp_I ((φ + φ₀) / 2)
            + (Real.sin (θ₀ / 2) : ℂ) * (Real.sin (θ₀ / 2) : ℂ)
              * exp_neg_I_mul_exp_I ((φ - φ₀) / 2)
            + ofReal_sin_sq_add_cos_sq (θ₀ / 2)
      refine ⟨C ((Real.cos (θ₀ / 2) : ℂ)
          * Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I))),
        C ((Real.sin (θ₀ / 2) : ℂ)
          * Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I))),
        ?_, fun x => ?_⟩
      · refine isYZPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_
        · rw [Polynomial.coeff_C, if_neg (by omega)]
        · rw [Polynomial.coeff_C, if_neg (by omega)]
        · rw [conjP_C, conjP_C, reflect_zero_C, reflect_zero_C, pow_zero,
            ← C_mul, ← C_mul, ← C_add, habs, map_one]
      · rw [qspYZZYZ_nil]
        exact rotYZ_base_eq_qspMatYZ φ θ₀ φ₀ _ _ x rfl rfl
  | append_singleton ps p ih =>
      obtain ⟨θ, ψ⟩ := p
      obtain ⟨A, B, hpair, hmat⟩ := ih
      set v : ℂ := (Real.cos (θ / 2) : ℂ)
        * Complex.exp (((ψ / 2 : ℝ) : ℂ) * Complex.I) with hv
      set w : ℂ := (Real.sin (θ / 2) : ℂ)
        * Complex.exp (-(((ψ / 2 : ℝ) : ℂ) * Complex.I)) with hw
      have hvw : v * starRingEnd ℂ v + w * starRingEnd ℂ w = 1 := by
        rw [hv, hw]
        simp only [map_mul, Complex.conj_ofReal, conj_exp_I, conj_exp_neg_I]
        linear_combination
          (Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)
              * exp_I_mul_exp_neg_I (ψ / 2)
            + (Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)
              * exp_neg_I_mul_exp_I (ψ / 2)
            + ofReal_sin_sq_add_cos_sq (θ / 2)
      refine ⟨C (starRingEnd ℂ v) * A - C w * (X * B),
        C (starRingEnd ℂ w) * A + C v * (X * B), ?_, fun x => ?_⟩
      · simpa using hpair.step v w hvw
      · rw [show (ps ++ [(θ, ψ)]).length = ps.length + 1 by simp,
          qspYZZYZ_concat]
        change (qspYZZYZ φ θ₀ φ₀ ps x : HilbertOperator 1) *
            (rotZStd x * (rotY θ * rotZStd ψ) : Gate 1) =
          qspMatYZ (ps.length + 1)
            (C (starRingEnd ℂ v) * A - C w * (X * B))
            (C (starRingEnd ℂ w) * A + C v * (X * B)) x
        rw [hmat x, qspMatYZ_step ps.length A B θ ψ x hv.symm hw.symm]

/-- The YZY one-step matrix recurrence: the `φ = 0` case of
`qspMatYZ_step`. -/
private theorem qspMatYZ_step_yzy (L : ℕ) (A B : ℂ[X]) (θ : ℝ) (x : ℝ) :
    qspMatYZ L A B x * (rotZStd x * rotY θ : Gate 1)
      = qspMatYZ (L + 1)
          (C ((Real.cos (θ / 2) : ℂ)) * A
            - C ((Real.sin (θ / 2) : ℂ)) * (X * B))
          (C ((Real.sin (θ / 2) : ℂ)) * A
            + C ((Real.cos (θ / 2) : ℂ)) * (X * B)) x := by
  have hv0 : (Real.cos (θ / 2) : ℂ)
      * Complex.exp (((0 / 2 : ℝ) : ℂ) * Complex.I)
        = (Real.cos (θ / 2) : ℂ) := by norm_num
  have hw0 : (Real.sin (θ / 2) : ℂ)
      * Complex.exp (-(((0 / 2 : ℝ) : ℂ) * Complex.I))
        = (Real.sin (θ / 2) : ℂ) := by norm_num
  have h := qspMatYZ_step L A B θ 0 x hv0 hw0
  rw [rotZStd_zero, mul_one] at h
  simpa only [Complex.conj_ofReal] using h

/-- The `R_Y(θ₀)` gate is the `L = 0` instance of the target form. -/
private theorem rotY_eq_qspMatYZ (θ₀ : ℝ) (x : ℝ) :
    (rotY θ₀ : Gate 1) = qspMatYZ 0 (C ((Real.cos (θ₀ / 2) : ℂ)))
      (C ((Real.sin (θ₀ / 2) : ℂ))) x := by
  have h := rotYZ_base_eq_qspMatYZ 0 θ₀ 0 (Real.cos (θ₀ / 2) : ℂ)
    (Real.sin (θ₀ / 2) : ℂ) x (by norm_num) (by norm_num)
  rwa [rotZStd_zero, one_mul, mul_one] at h

/-- One-step closure of the YZY pair conditions (real coefficients). -/
private theorem IsYZYPair.step {L : ℕ} {A B : ℂ[X]} (h : IsYZYPair L A B) (θ : ℝ) :
    IsYZYPair (L + 1)
      (C ((Real.cos (θ / 2) : ℂ)) * A - C ((Real.sin (θ / 2) : ℂ)) * (X * B))
      (C ((Real.sin (θ / 2) : ℂ)) * A
        + C ((Real.cos (θ / 2) : ℂ)) * (X * B)) := by
  have hvw : (Real.cos (θ / 2) : ℂ) * starRingEnd ℂ (Real.cos (θ / 2) : ℂ)
      + (Real.sin (θ / 2) : ℂ) * starRingEnd ℂ (Real.sin (θ / 2) : ℂ) = 1 := by
    simp only [Complex.conj_ofReal]
    linear_combination ofReal_sin_sq_add_cos_sq (θ / 2)
  have hyz := h.toIsYZPair.step _ _ hvw
  rw [Complex.conj_ofReal, Complex.conj_ofReal] at hyz
  refine ⟨hyz, ?_, ?_⟩
  · rw [conjP_sub, conjP_mul, conjP_mul, conjP_C, conjP_C, conjP_mul, conjP_X,
      Complex.conj_ofReal, Complex.conj_ofReal, h.realA, h.realB]
  · rw [conjP_add, conjP_mul, conjP_mul, conjP_C, conjP_C, conjP_mul, conjP_X,
      Complex.conj_ofReal, Complex.conj_ofReal, h.realA, h.realB]

/-- Soundness for the YZY form: every `qspYZY` product realizes the target
form for a real pair satisfying the conditions
[YYLW22, neurips_2022.tex:283, forward direction]. -/
theorem qspYZY_forward (θ₀ : ℝ) (θs : List ℝ) :
    ∃ A B : ℂ[X], IsYZYPair θs.length A B ∧
      ∀ x : ℝ, qspYZY θ₀ θs x = qspMatYZ θs.length A B x := by
  induction θs using List.reverseRecOn with
  | nil =>
      simp only [List.length_nil]
      refine ⟨C ((Real.cos (θ₀ / 2) : ℂ)), C ((Real.sin (θ₀ / 2) : ℂ)),
        ⟨?_, ?_, ?_⟩, fun x => ?_⟩
      · refine isYZPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_
        · rw [Polynomial.coeff_C, if_neg (by omega)]
        · rw [Polynomial.coeff_C, if_neg (by omega)]
        · rw [conjP_C, conjP_C, reflect_zero_C, reflect_zero_C, pow_zero,
            ← C_mul, ← C_mul, ← C_add, Complex.conj_ofReal,
            Complex.conj_ofReal]
          rw [show (Real.cos (θ₀ / 2) : ℂ) * (Real.cos (θ₀ / 2) : ℂ)
              + (Real.sin (θ₀ / 2) : ℂ) * (Real.sin (θ₀ / 2) : ℂ) = 1 by
            linear_combination ofReal_sin_sq_add_cos_sq (θ₀ / 2), map_one]
      · rw [conjP_C, Complex.conj_ofReal]
      · rw [conjP_C, Complex.conj_ofReal]
      · rw [qspYZY_nil]
        exact rotY_eq_qspMatYZ θ₀ x
  | append_singleton θs θ ih =>
      obtain ⟨A, B, hpair, hmat⟩ := ih
      refine ⟨C ((Real.cos (θ / 2) : ℂ)) * A
          - C ((Real.sin (θ / 2) : ℂ)) * (X * B),
        C ((Real.sin (θ / 2) : ℂ)) * A
          + C ((Real.cos (θ / 2) : ℂ)) * (X * B), ?_, fun x => ?_⟩
      · simpa using hpair.step θ
      · rw [show (θs ++ [θ]).length = θs.length + 1 by simp, qspYZY_concat]
        change (qspYZY θ₀ θs x : HilbertOperator 1) *
            (rotZStd x * rotY θ : Gate 1) =
          qspMatYZ (θs.length + 1)
            (C ((Real.cos (θ / 2) : ℂ)) * A
              - C ((Real.sin (θ / 2) : ℂ)) * (X * B))
            (C ((Real.sin (θ / 2) : ℂ)) * A
              + C ((Real.cos (θ / 2) : ℂ)) * (X * B)) x
        rw [hmat x, qspMatYZ_step_yzy θs.length A B θ x]

/-! #### Normalization on the circle -/

/-- The conjugate-pair product under `lEval`, as a single polynomial
evaluation on the circle. -/
private theorem lEval_mul_conj {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) (x : ℝ) :
    lEval L F x * starRingEnd ℂ (lEval L F x)
      = Complex.exp (-((L * x : ℝ) * Complex.I))
        * (F * (conjP F).reflect L).eval
            (Complex.exp ((x : ℂ) * Complex.I)) := by
  rw [conj_lEval hF, Polynomial.eval_mul]
  simp only [lEval]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The polynomial normalization identity is equivalent to the pointwise
circle normalization `|P(x)|² + |Q(x)|² = 1` on `ℝ`
[YYLW22, neurips_2022.tex:288]. -/
theorem qspYZ_normalization_iff {L : ℕ} {A B : ℂ[X]} (hA : A.natDegree ≤ L)
    (hB : B.natDegree ≤ L) :
    A * (conjP A).reflect L + B * (conjP B).reflect L = X ^ L ↔
      ∀ x : ℝ, lEval L A x * starRingEnd ℂ (lEval L A x)
        + lEval L B x * starRingEnd ℂ (lEval L B x) = 1 := by
  have hzero : ∀ x : ℝ, -((L * x : ℝ) * Complex.I)
      + (L : ℂ) * ((x : ℂ) * Complex.I) = 0 := by
    intro x
    push_cast
    ring
  constructor
  · intro hnorm x
    rw [lEval_mul_conj hA x, lEval_mul_conj hB x, ← mul_add,
      ← Polynomial.eval_add, hnorm, Polynomial.eval_pow, Polynomial.eval_X,
      ← Complex.exp_nat_mul, ← Complex.exp_add, hzero x, Complex.exp_zero]
  · intro hpt
    refine eq_of_circle_eval_eq fun x => ?_
    have h := hpt x
    rw [lEval_mul_conj hA x, lEval_mul_conj hB x, ← mul_add,
      ← Polynomial.eval_add] at h
    rw [Polynomial.eval_pow, Polynomial.eval_X, ← Complex.exp_nat_mul]
    apply mul_left_cancel₀
      (Complex.exp_ne_zero (-((L * x : ℝ) * Complex.I)))
    rw [h, ← Complex.exp_add, hzero x, Complex.exp_zero]

/-- Two target forms agreeing for all `x : ℝ` have equal polynomial pairs. -/
private theorem qspMatYZ_inj {L : ℕ} {A B A' B' : ℂ[X]}
    (hmat : ∀ x : ℝ, qspMatYZ L A B x = qspMatYZ L A' B' x) :
    A = A' ∧ B = B' := by
  constructor
  · refine eq_of_circle_eval_eq fun x => ?_
    have h00 := congrArg (fun M : HilbertOperator 1 => M 0 0) (hmat x)
    have h : lEval L A x = lEval L A' x := by
      simpa [qspMatYZ, Matrix.cons_val_zero] using h00
    simp only [lEval] at h
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h
  · refine eq_of_circle_eval_eq fun x => ?_
    have h01 := congrArg (fun M : HilbertOperator 1 => M 0 1) (hmat x)
    have h : lEval L B x = lEval L B' x := by
      simpa [qspMatYZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        using h01
    simp only [lEval] at h
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h

/-! #### Completeness (converse direction)

Degree-reduction induction following [YYLW22, neurips_2022.tex:848]: the
norm identity forces the edge-coefficient relation
`a₀·a*_{L+1} + b₀·b*_{L+1} = 0` (`IsYZPair.edge_rel`), so some unit pair
`(v, w)` with real product kills both the top coefficient of `v·A + w·B`
and the bottom coefficient of `v*·B - w*·A` (`exists_unstep_vw`); the
inverse recurrence then factors the pair through one trainable block
(`isYZPair_unstep`), which is realized by angles via
`exists_rotYZ_angles`. -/

/-- Any unit pair `(v, w)` with real product `v·w` is realized by a
`R_Y`/`R_Z` angle pair: `v = cos(θ/2)e^{iψ/2}`, `w = sin(θ/2)e^{-iψ/2}`. -/
private theorem exists_rotYZ_angles {v w : ℂ}
    (hvw : v * starRingEnd ℂ v + w * starRingEnd ℂ w = 1)
    (him : (v * w).im = 0) :
    ∃ θ ψ : ℝ,
      (Real.cos (θ / 2) : ℂ)
        * Complex.exp (((ψ / 2 : ℝ) : ℂ) * Complex.I) = v ∧
      (Real.sin (θ / 2) : ℂ)
        * Complex.exp (-(((ψ / 2 : ℝ) : ℂ) * Complex.I)) = w := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- `v = 0`: then `|w| = 1`; take `θ = π`, `ψ = -2·arg w`.
    have hw1' : w * starRingEnd ℂ w = 1 := by simpa [hv0] using hvw
    have hnw : ‖w‖ = 1 := by
      have h1 := mul_conj_eq_norm_sq w
      rw [hw1'] at h1
      have h2 : ‖w‖ ^ 2 = 1 := by exact_mod_cast h1.symm
      have h4 : (‖w‖ - 1) * (‖w‖ + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h4 with h5 | h5
      · linarith
      · exfalso; linarith [norm_nonneg w]
    have hw1 : Complex.exp ((w.arg : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rwa [hnw, Complex.ofReal_one, one_mul] at h
    refine ⟨Real.pi, -(2 * w.arg), ?_, ?_⟩
    · rw [Real.cos_pi_div_two]
      simp [hv0]
    · rw [show (-(2 * w.arg) / 2 : ℝ) = -w.arg by ring,
        Real.sin_pi_div_two,
        show -(((-w.arg : ℝ) : ℂ) * Complex.I)
          = (w.arg : ℂ) * Complex.I by push_cast; ring,
        hw1, Complex.ofReal_one, one_mul]
  · -- `v ≠ 0`: then `w = t·e^{-i·arg v}` with `t := (vw).re/‖v‖` real.
    have hr : v * w = (((v * w).re : ℝ) : ℂ) :=
      (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr him)).symm
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    set t : ℝ := (v * w).re / ‖v‖ with htdef
    have hts : t * ‖v‖ = (v * w).re := div_mul_cancel₀ _ hvn
    have hpolar := Complex.norm_mul_exp_arg_mul_I v
    have hcast : ((t : ℝ) : ℂ) * ((‖v‖ : ℝ) : ℂ)
        = (((v * w).re : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun u : ℝ => (u : ℂ)) hts
    have hw' : w = ((t : ℝ) : ℂ)
        * Complex.exp (-((v.arg : ℂ) * Complex.I)) := by
      apply mul_left_cancel₀ hv0
      rw [hr]
      linear_combination (((t : ℝ) : ℂ)
            * Complex.exp (-((v.arg : ℂ) * Complex.I))) * hpolar
          - ((t : ℝ) : ℂ) * ((‖v‖ : ℝ) : ℂ) * exp_I_mul_exp_neg_I v.arg
          - hcast
    have hww : w * starRingEnd ℂ w = ((t : ℝ) : ℂ) ^ 2 := by
      rw [hw', map_mul, Complex.conj_ofReal, conj_exp_neg_I]
      linear_combination ((t : ℂ) * (t : ℂ)) * exp_neg_I_mul_exp_I v.arg
    have ht2 : ‖v‖ ^ 2 + t ^ 2 = 1 := by
      have h1 := hvw
      rw [mul_conj_eq_norm_sq, hww] at h1
      exact_mod_cast h1
    have htb : -1 ≤ t ∧ t ≤ 1 := by
      constructor <;>
        nlinarith [sq_nonneg ‖v‖, sq_nonneg (t - 1), sq_nonneg (t + 1)]
    refine ⟨2 * Real.arcsin t, 2 * v.arg, ?_, ?_⟩
    · rw [show (2 * Real.arcsin t) / 2 = Real.arcsin t by ring,
        show (2 * v.arg / 2 : ℝ) = v.arg by ring, Real.cos_arcsin,
        show 1 - t ^ 2 = ‖v‖ ^ 2 by linarith,
        Real.sqrt_sq (norm_nonneg v)]
      exact hpolar
    · rw [show (2 * Real.arcsin t) / 2 = Real.arcsin t by ring,
        show (2 * v.arg / 2 : ℝ) = v.arg by ring,
        Real.sin_arcsin htb.1 htb.2]
      exact hw'.symm

/-- The three base angles realize any unit pair `(a, b)` as the `L = 0`
form constants [YYLW22, neurips_2022.tex:804]. -/
private theorem exists_rotYZ_base {a b : ℂ}
    (hab : a * starRingEnd ℂ a + b * starRingEnd ℂ b = 1) :
    ∃ φ θ₀ φ₀ : ℝ,
      (Real.cos (θ₀ / 2) : ℂ)
        * Complex.exp (-((((φ + φ₀) / 2 : ℝ) : ℂ) * Complex.I)) = a ∧
      (Real.sin (θ₀ / 2) : ℂ)
        * Complex.exp (-((((φ - φ₀) / 2 : ℝ) : ℂ) * Complex.I)) = b := by
  have hab' : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    have h1 := hab
    rw [mul_conj_eq_norm_sq, mul_conj_eq_norm_sq] at h1
    exact_mod_cast h1
  have hb1 : ‖b‖ ≤ 1 := by
    nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg ‖a‖,
      sq_nonneg (‖b‖ - 1)]
  refine ⟨-(a.arg + b.arg), 2 * Real.arcsin ‖b‖, b.arg - a.arg, ?_, ?_⟩
  · rw [show (2 * Real.arcsin ‖b‖) / 2 = Real.arcsin ‖b‖ by ring,
      Real.cos_arcsin, show 1 - ‖b‖ ^ 2 = ‖a‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg a),
      show ((-(a.arg + b.arg) + (b.arg - a.arg)) / 2 : ℝ) = -a.arg by ring,
      show -(((-a.arg : ℝ) : ℂ) * Complex.I)
        = (a.arg : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_mul_exp_arg_mul_I a
  · rw [show (2 * Real.arcsin ‖b‖) / 2 = Real.arcsin ‖b‖ by ring,
      Real.sin_arcsin (by linarith [norm_nonneg b]) hb1,
      show ((-(a.arg + b.arg) - (b.arg - a.arg)) / 2 : ℝ) = -b.arg by ring,
      show -(((-b.arg : ℝ) : ℂ) * Complex.I)
        = (b.arg : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_mul_exp_arg_mul_I b

/-- Edge-coefficient relation forced by the norm identity at coefficient
`0` [YYLW22, neurips_2022.tex:848]. -/
private theorem IsYZPair.edge_rel {L : ℕ} {A B : ℂ[X]} (h : IsYZPair (L + 1) A B) :
    A.coeff 0 * starRingEnd ℂ (A.coeff (L + 1))
      + B.coeff 0 * starRingEnd ℂ (B.coeff (L + 1)) = 0 := by
  have hn := congrArg (fun p : ℂ[X] => p.coeff 0) h.norm
  simpa [Polynomial.mul_coeff_zero,
    coeff_reflect_of_le (Nat.zero_le (L + 1)), Polynomial.coeff_X_pow]
    using hn

/-- Some unit pair `(v, w)` with real product satisfies both unstep edge
conditions; three cases on the vanishing of the edge coefficients
[YYLW22, neurips_2022.tex:848]. -/
private theorem exists_unstep_vw {L : ℕ} {A B : ℂ[X]} (h : IsYZPair (L + 1) A B) :
    ∃ v w : ℂ, v * starRingEnd ℂ v + w * starRingEnd ℂ w = 1 ∧
      (v * w).im = 0 ∧ v * A.coeff (L + 1) + w * B.coeff (L + 1) = 0 ∧
      starRingEnd ℂ v * B.coeff 0 - starRingEnd ℂ w * A.coeff 0 = 0 := by
  rcases Classical.em (A.coeff 0 = 0 ∧ B.coeff 0 = 0) with h0 | h0
  · rcases Classical.em (A.coeff (L + 1) = 0 ∧ B.coeff (L + 1) = 0)
      with hT | hT
    · exact ⟨1, 0, by simp, by simp, by simp [hT.1, hT.2],
        by simp [h0.1, h0.2]⟩
    · have hne : ¬(-B.coeff (L + 1) = 0 ∧ A.coeff (L + 1) = 0) := by
        rintro ⟨hb', ha'⟩
        exact hT ⟨ha', by simpa using hb'⟩
      obtain ⟨c, hunit, him⟩ := exists_unit_mul hne
      refine ⟨c * -B.coeff (L + 1), c * A.coeff (L + 1), hunit, him,
        by ring, ?_⟩
      rw [h0.1, h0.2]
      ring
  · have hne : ¬(starRingEnd ℂ (A.coeff 0) = 0
        ∧ starRingEnd ℂ (B.coeff 0) = 0) := by
      rintro ⟨h1, h2⟩
      refine h0 ⟨?_, ?_⟩
      · simpa using congrArg (starRingEnd ℂ) h1
      · simpa using congrArg (starRingEnd ℂ) h2
    obtain ⟨c, hunit, him⟩ := exists_unit_mul hne
    have hRc : starRingEnd ℂ (A.coeff 0) * A.coeff (L + 1)
        + starRingEnd ℂ (B.coeff 0) * B.coeff (L + 1) = 0 := by
      have h1 := congrArg (starRingEnd ℂ) h.edge_rel
      simpa using h1
    refine ⟨c * starRingEnd ℂ (A.coeff 0), c * starRingEnd ℂ (B.coeff 0),
      hunit, him, ?_, ?_⟩
    · linear_combination c * hRc
    · simp only [map_mul, Complex.conj_conj]
      ring

/-- Inverse one-step recurrence [YYLW22, neurips_2022.tex:875]: an
`IsYZPair (L+1)` pair whose edge coefficients are compatible with a unit
pair `(v, w)` factors through the recurrence step. -/
private theorem isYZPair_unstep {L : ℕ} {A B : ℂ[X]} (h : IsYZPair (L + 1) A B)
    {v w : ℂ} (hvw : v * starRingEnd ℂ v + w * starRingEnd ℂ w = 1)
    (h1 : v * A.coeff (L + 1) + w * B.coeff (L + 1) = 0)
    (h2 : starRingEnd ℂ v * B.coeff 0 - starRingEnd ℂ w * A.coeff 0 = 0) :
    ∃ A' B' : ℂ[X], IsYZPair L A' B' ∧
      A = C (starRingEnd ℂ v) * A' - C w * (X * B') ∧
      B = C (starRingEnd ℂ w) * A' + C v * (X * B') := by
  have hC : (C v * C (starRingEnd ℂ v) + C w * C (starRingEnd ℂ w) : ℂ[X])
      = 1 := by
    rw [← C_mul, ← C_mul, ← C_add, hvw, map_one]
  set A' : ℂ[X] := C v * A + C w * B with hA'def
  set B'' : ℂ[X] := C (starRingEnd ℂ v) * B - C (starRingEnd ℂ w) * A
    with hB''def
  have hB''0 : B''.coeff 0 = 0 := by
    simp only [hB''def, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    linear_combination h2
  have hXdiv : X * B''.divX = B'' := by
    have hh := Polynomial.X_mul_divX_add B''
    rwa [hB''0, map_zero, add_zero] at hh
  have hA'c : ∀ m, L < m → A'.coeff m = 0 := by
    intro m hm
    rcases Nat.lt_or_ge (L + 1) m with hgt | hle
    · simp [hA'def, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        h.coeff_A_eq_zero hgt, h.coeff_B_eq_zero hgt]
    · have hme : m = L + 1 := by omega
      subst hme
      simp only [hA'def, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      linear_combination h1
  have hB'c : ∀ m, L < m → B''.divX.coeff m = 0 := by
    intro m hm
    rw [Polynomial.coeff_divX]
    simp [hB''def, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      h.coeff_A_eq_zero (show L + 1 < m + 1 by omega),
      h.coeff_B_eq_zero (show L + 1 < m + 1 by omega)]
  have hA'nd : A'.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr
      ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
        hA'c m (by exact_mod_cast hm))
  have hB'nd : B''.divX.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr
      ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
        hB'c m (by exact_mod_cast hm))
  have hAeq : A = C (starRingEnd ℂ v) * A' - C w * (X * B''.divX) := by
    rw [hXdiv, hA'def, hB''def]
    linear_combination (-A : ℂ[X]) * hC
  have hBeq : B = C (starRingEnd ℂ w) * A' + C v * (X * B''.divX) := by
    rw [hXdiv, hA'def, hB''def]
    linear_combination (-B : ℂ[X]) * hC
  have hnorm' : A' * (conjP A').reflect L
      + B''.divX * (conjP B''.divX).reflect L = X ^ L := by
    have hstep := yz_norm_step hA'nd hB'nd v w
    rw [← hAeq, ← hBeq, h.norm, hC, one_mul] at hstep
    have hXX : (X : ℂ[X]) ^ (L + 1) = X * X ^ L := by
      rw [pow_succ, mul_comm]
    rw [hXX] at hstep
    exact mul_left_cancel₀ Polynomial.X_ne_zero hstep.symm
  exact ⟨A', B''.divX, isYZPair_of_coeff hA'c hB'c hnorm', hAeq, hBeq⟩

/-- Completeness for the YZZYZ form [YYLW22, neurips_2022.tex:848, converse
direction]: every `IsYZPair` pair is realized by some angle sequence with
exactly `L` encoding blocks. -/
theorem qspYZZYZ_converse :
    ∀ (L : ℕ) (A B : ℂ[X]), IsYZPair L A B →
      ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
        ∀ x : ℝ, qspYZZYZ φ θ₀ φ₀ ps x = qspMatYZ L A B x := by
  intro L
  induction L with
  | zero =>
      intro A B h
      have hA : A = C (A.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (by exact_mod_cast h.degA)
      have hB : B = C (B.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (by exact_mod_cast h.degB)
      have hab : A.coeff 0 * starRingEnd ℂ (A.coeff 0)
          + B.coeff 0 * starRingEnd ℂ (B.coeff 0) = 1 := by
        have hn := congrArg (fun p : ℂ[X] => p.coeff 0) h.norm
        simpa [Polynomial.mul_coeff_zero,
          coeff_reflect_of_le (Nat.le_refl 0)] using hn
      obtain ⟨φ, θ₀, φ₀, ha, hb⟩ := exists_rotYZ_base hab
      refine ⟨φ, θ₀, φ₀, [], rfl, fun x => ?_⟩
      rw [qspYZZYZ_nil,
        rotYZ_base_eq_qspMatYZ φ θ₀ φ₀ (A.coeff 0) (B.coeff 0) x ha hb,
        ← hA, ← hB]
  | succ L ih =>
      intro A B h
      obtain ⟨v, w, hvw, him, h1, h2⟩ := exists_unstep_vw h
      obtain ⟨A', B', hp', hAeq, hBeq⟩ := isYZPair_unstep h hvw h1 h2
      obtain ⟨θ, ψ, hv, hw⟩ := exists_rotYZ_angles hvw him
      obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ := ih A' B' hp'
      refine ⟨φ, θ₀, φ₀, ps ++ [(θ, ψ)], by simp [hlen], fun x => ?_⟩
      rw [qspYZZYZ_concat]
      change (qspYZZYZ φ θ₀ φ₀ ps x : HilbertOperator 1) *
          (rotZStd x * (rotY θ * rotZStd ψ) : Gate 1) =
        qspMatYZ (L + 1) A B x
      rw [hmat x, qspMatYZ_step L A' B' θ ψ x hv hw, ← hAeq, ← hBeq]

private theorem IsYZYPair.conj_coeff_A {L : ℕ} {A B : ℂ[X]} (h : IsYZYPair L A B)
    (k : ℕ) : starRingEnd ℂ (A.coeff k) = A.coeff k := by
  have h1 := congrArg (fun p : ℂ[X] => p.coeff k) h.realA
  simpa using h1

private theorem IsYZYPair.conj_coeff_B {L : ℕ} {A B : ℂ[X]} (h : IsYZYPair L A B)
    (k : ℕ) : starRingEnd ℂ (B.coeff k) = B.coeff k := by
  have h1 := congrArg (fun p : ℂ[X] => p.coeff k) h.realB
  simpa using h1

/-- A real unit pair satisfying the YZY unstep edge conditions
[YYLW22, neurips_2022.tex:702]. -/
private theorem exists_unstep_vw_yzy {L : ℕ} {A B : ℂ[X]}
    (h : IsYZYPair (L + 1) A B) :
    ∃ v w : ℝ, v ^ 2 + w ^ 2 = 1 ∧
      (v : ℂ) * A.coeff (L + 1) + (w : ℂ) * B.coeff (L + 1) = 0 ∧
      (v : ℂ) * B.coeff 0 - (w : ℂ) * A.coeff 0 = 0 := by
  obtain ⟨a0, ha0⟩ : ∃ u : ℝ, A.coeff 0 = (u : ℂ) :=
    ⟨(A.coeff 0).re, (Complex.conj_eq_iff_re.mp (h.conj_coeff_A 0)).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ u : ℝ, B.coeff 0 = (u : ℂ) :=
    ⟨(B.coeff 0).re, (Complex.conj_eq_iff_re.mp (h.conj_coeff_B 0)).symm⟩
  obtain ⟨aT, haT⟩ : ∃ u : ℝ, A.coeff (L + 1) = (u : ℂ) :=
    ⟨(A.coeff (L + 1)).re,
      (Complex.conj_eq_iff_re.mp (h.conj_coeff_A (L + 1))).symm⟩
  obtain ⟨bT, hbT⟩ : ∃ u : ℝ, B.coeff (L + 1) = (u : ℂ) :=
    ⟨(B.coeff (L + 1)).re,
      (Complex.conj_eq_iff_re.mp (h.conj_coeff_B (L + 1))).symm⟩
  have hR := h.toIsYZPair.edge_rel
  rw [ha0, hb0, haT, hbT] at hR
  have hRr : a0 * aT + b0 * bT = 0 := by
    simp only [Complex.conj_ofReal] at hR
    exact_mod_cast hR
  obtain ⟨v, w, hu, hc1, hc2⟩ : ∃ v w : ℝ, v ^ 2 + w ^ 2 = 1
      ∧ v * aT + w * bT = 0 ∧ v * b0 - w * a0 = 0 := by
    rcases Classical.em (a0 = 0 ∧ b0 = 0) with h0 | h0
    · rcases Classical.em (aT = 0 ∧ bT = 0) with hT | hT
      · exact ⟨1, 0, by norm_num, by rw [hT.1, hT.2]; ring,
          by rw [h0.1, h0.2]; ring⟩
      · have hne : ¬(-bT = 0 ∧ aT = 0) := by
          rintro ⟨hb', ha'⟩
          exact hT ⟨ha', by linarith⟩
        obtain ⟨v, w, hu, c, hv, hw⟩ := exists_real_unit hne
        exact ⟨v, w, hu, by rw [hv, hw]; ring,
          by rw [hv, hw, h0.1, h0.2]; ring⟩
    · obtain ⟨v, w, hu, c, hv, hw⟩ := exists_real_unit h0
      exact ⟨v, w, hu, by rw [hv, hw]; linear_combination c * hRr,
        by rw [hv, hw]; ring⟩
  refine ⟨v, w, hu, ?_, ?_⟩
  · rw [haT, hbT]
    exact_mod_cast congrArg (fun u : ℝ => (u : ℂ)) hc1
  · rw [ha0, hb0]
    exact_mod_cast congrArg (fun u : ℝ => (u : ℂ)) hc2

/-- Completeness for the YZY form [YYLW22, neurips_2022.tex:702, converse
direction]. -/
theorem qspYZY_converse :
    ∀ (L : ℕ) (A B : ℂ[X]), IsYZYPair L A B →
      ∃ (θ₀ : ℝ) (θs : List ℝ), θs.length = L ∧
        ∀ x : ℝ, qspYZY θ₀ θs x = qspMatYZ L A B x := by
  intro L
  induction L with
  | zero =>
      intro A B h
      have hA : A = C (A.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (by exact_mod_cast h.degA)
      have hB : B = C (B.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (by exact_mod_cast h.degB)
      obtain ⟨a0, ha0⟩ : ∃ u : ℝ, A.coeff 0 = (u : ℂ) :=
        ⟨(A.coeff 0).re,
          (Complex.conj_eq_iff_re.mp (h.conj_coeff_A 0)).symm⟩
      obtain ⟨b0, hb0⟩ : ∃ u : ℝ, B.coeff 0 = (u : ℂ) :=
        ⟨(B.coeff 0).re,
          (Complex.conj_eq_iff_re.mp (h.conj_coeff_B 0)).symm⟩
      have hab : A.coeff 0 * starRingEnd ℂ (A.coeff 0)
          + B.coeff 0 * starRingEnd ℂ (B.coeff 0) = 1 := by
        have hn := congrArg (fun p : ℂ[X] => p.coeff 0) h.norm
        simpa [Polynomial.mul_coeff_zero,
          coeff_reflect_of_le (Nat.le_refl 0)] using hn
      have habr : a0 ^ 2 + b0 ^ 2 = 1 := by
        rw [ha0, hb0, Complex.conj_ofReal, Complex.conj_ofReal] at hab
        have h2 : a0 * a0 + b0 * b0 = 1 := by exact_mod_cast hab
        linear_combination h2
      obtain ⟨θ₀, hc, hs⟩ := exists_cos_sin habr
      refine ⟨θ₀, [], rfl, fun x => ?_⟩
      rw [qspYZY_nil, rotY_eq_qspMatYZ θ₀ x, hc, hs, ← ha0, ← hb0,
        ← hA, ← hB]
  | succ L ih =>
      intro A B h
      obtain ⟨v, w, hu, h1, h2⟩ := exists_unstep_vw_yzy h
      have hvwC : (v : ℂ) * starRingEnd ℂ (v : ℂ)
          + (w : ℂ) * starRingEnd ℂ (w : ℂ) = 1 := by
        rw [Complex.conj_ofReal, Complex.conj_ofReal]
        norm_cast
        linear_combination hu
      have h2C : starRingEnd ℂ (v : ℂ) * B.coeff 0
          - starRingEnd ℂ (w : ℂ) * A.coeff 0 = 0 := by
        rw [Complex.conj_ofReal, Complex.conj_ofReal]
        exact h2
      obtain ⟨A', B', hp', hAeq, hBeq⟩ :=
        isYZPair_unstep h.toIsYZPair hvwC h1 h2C
      rw [Complex.conj_ofReal] at hAeq hBeq
      have hCv : ((v : ℂ) * v + (w : ℂ) * w : ℂ) = 1 := by
        norm_cast
        linear_combination hu
      have hCp : (C (v : ℂ) * C (v : ℂ) + C (w : ℂ) * C (w : ℂ) : ℂ[X])
          = 1 := by
        rw [← C_mul, ← C_mul, ← C_add, hCv, map_one]
      have hA'form : A' = C (v : ℂ) * A + C (w : ℂ) * B := by
        rw [hAeq, hBeq]
        linear_combination (-A' : ℂ[X]) * hCp
      have hXB'form : X * B' = C (v : ℂ) * B - C (w : ℂ) * A := by
        rw [hAeq, hBeq]
        linear_combination (-(X * B') : ℂ[X]) * hCp
      have hrA' : conjP A' = A' := by
        rw [hA'form, conjP_add, conjP_mul, conjP_mul, conjP_C, conjP_C,
          Complex.conj_ofReal, Complex.conj_ofReal, h.realA, h.realB]
      have hrB' : conjP B' = B' := by
        have hXr : conjP (X * B') = X * B' := by
          rw [hXB'form, conjP_sub, conjP_mul, conjP_mul, conjP_C, conjP_C,
            Complex.conj_ofReal, Complex.conj_ofReal, h.realA, h.realB]
        rw [conjP_mul, conjP_X] at hXr
        exact mul_left_cancel₀ Polynomial.X_ne_zero hXr
      obtain ⟨θ, hc, hs⟩ := exists_cos_sin hu
      obtain ⟨θ₀, θs, hlen, hmat⟩ := ih A' B' ⟨hp', hrA', hrB'⟩
      refine ⟨θ₀, θs ++ [θ], by simp [hlen], fun x => ?_⟩
      rw [qspYZY_concat]
      change (qspYZY θ₀ θs x : HilbertOperator 1) *
          (rotZStd x * rotY θ : Gate 1) =
        qspMatYZ (L + 1) A B x
      rw [hmat x, qspMatYZ_step_yzy L A' B' θ x, hc, hs, ← hAeq, ← hBeq]

/-! #### The characterization theorems -/

theorem qspYZZYZ_mem_unitaryGroup (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (x : ℝ) :
    (qspYZZYZ φ θ₀ φ₀ ps x : HilbertOperator 1) ∈
      Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  induction ps using List.reverseRecOn with
  | nil =>
      rw [qspYZZYZ_nil]
      exact mul_mem (rotZStd_mem_unitaryGroup φ)
        (mul_mem (rotY_mem_unitaryGroup θ₀) (rotZStd_mem_unitaryGroup φ₀))
  | append_singleton ps p ih =>
      rw [qspYZZYZ_concat]
      exact mul_mem ih (mul_mem (rotZStd_mem_unitaryGroup x)
        (mul_mem (rotY_mem_unitaryGroup p.1) (rotZStd_mem_unitaryGroup p.2)))

theorem qspYZY_mem_unitaryGroup (θ₀ : ℝ) (θs : List ℝ) (x : ℝ) :
    (qspYZY θ₀ θs x : HilbertOperator 1) ∈
      Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [qspYZY_eq_qspYZZYZ]
  exact qspYZZYZ_mem_unitaryGroup 0 θ₀ 0 _ x

/-- **Trigonometric QSP, YZZYZ (W-Z-W) form**
[YYLW22, neurips_2022.tex:333] (`lem:qnn_yzzyz`, encoded form): a pair
`(A, B)` satisfies the degree and normalization conditions `IsYZPair L`
**iff** some angles `(φ, θ₀, φ₀, ps)` with `L` encoding gates realize the
matrix form `[[P, -Q], [Q*, P*]]` with `P = e^{-iLx/2}·A(e^{ix})` and
`Q = e^{-iLx/2}·B(e^{ix})` for all `x : ℝ`. -/
theorem TrigonometricQuantumSignalProcessing.main (L : ℕ) (A B : ℂ[X]) :
    IsYZPair L A B ↔
      ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
        ∀ x : ℝ, qspYZZYZ φ θ₀ φ₀ ps x = qspMatYZ L A B x := by
  constructor
  · exact qspYZZYZ_converse L A B
  · rintro ⟨φ, θ₀, φ₀, ps, rfl, hmat⟩
    obtain ⟨A', B', hpair, hmat'⟩ := qspYZZYZ_forward φ θ₀ φ₀ ps
    obtain ⟨hA, hB⟩ := qspMatYZ_inj fun x => (hmat' x).symm.trans (hmat x)
    rwa [← hA, ← hB]

/-- **Trigonometric QSP, YZY form** [YYLW22, neurips_2022.tex:283]
(`lem:qnn_yzy`, encoded form): real-coefficient pairs `IsYZYPair L` are
exactly those realized by `R_Y` angles `(θ₀, θs)` with `L` encoding
gates. -/
theorem TrigonometricQuantumSignalProcessing.main_yzy (L : ℕ) (A B : ℂ[X]) :
    IsYZYPair L A B ↔
      ∃ (θ₀ : ℝ) (θs : List ℝ), θs.length = L ∧
        ∀ x : ℝ, qspYZY θ₀ θs x = qspMatYZ L A B x := by
  constructor
  · exact qspYZY_converse L A B
  · rintro ⟨θ₀, θs, rfl, hmat⟩
    obtain ⟨A', B', hpair, hmat'⟩ := qspYZY_forward θ₀ θs
    obtain ⟨hA, hB⟩ := qspMatYZ_inj fun x => (hmat' x).symm.trans (hmat x)
    rwa [← hA, ← hB]


end

end QuantumAlg
