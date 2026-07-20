/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.Rationality
import LeanPool.Chudnovsky.SingularModuli.Kronecker
import LeanPool.Chudnovsky.Ramanujan
import LeanPool.Chudnovsky.Estimates

/-!
# Masser's Theorem A1 at `τ₁₆₃`: rationality of `s₂` (Phase C, statement 3)

This file discharges the last remaining `sorry` of the Chudnovsky development,
`s₂_τ₁₆₃_rational`, by formalizing Masser's Appendix A1 argument (LNM 437, Thm. A1),
specialized to the CM point `τ₁₆₃ = (1 + i√163)/2`.  See `PhaseC-PLAN.md` §5.1.
The final result is **unconditional**: `masser_s₂_rational : ∃ r : ℚ, s₂ τ₁₆₃ = r`
(axiom-clean, zero `sorry`).

Masser's function is `ψ(τ) = (3E₄/2E₆)(E₂ − 3/(π Im τ)) = (3/2)·s₂(τ)`.  His theorem
gives `ψ(τ) ∈ ℚ(j(τ))`, and here `ℚ(j(τ₁₆₃)) = ℚ` (statement 2, already proved).

## Structure of Masser's proof (steps 1–5 of the plan)

1. The trace-zero fixing matrix `Λ = !![1, −82; 2, −1]` (det `163`, `Λ • τ₁₆₃ = τ₁₆₃`,
   Möbius derivative `Λ′(τ₁₆₃) = −1`, `Λ''(τ₁₆₃) = 4/(2τ − 1)`).
2. `Λ` is a coset of the modular polynomial `Φ₁₆₃`, so `F(z) := Φ₁₆₃(j(Λz), j(z))`
   vanishes identically on `ℍ`.
3. Second-order Taylor expansion of `F` at `τ₁₆₃` gives Masser's identity (105):
   `2·j''/j′ + Λ'' = −j′·γ`, with `γ = (β₂₀ − β₁₁ + β₀₂)/β₀₁ ∈ ℚ` (a ratio of Taylor
   coefficients of `Φ₁₆₃` at `(j₀, j₀)`, all rational since `j₀ ∈ ℚ`).
4. `β₀₁ ≠ 0` (Masser's Lemma A1): the only degree-`163` integer matrices fixing `τ₁₆₃`
   are `±Λ`, so no other coset value coincides with `j₀`.
5. The Ramanujan identities `deriv_E2/E₄/E₆` turn (105) into Masser's (106):
   `s₂(τ₁₆₃) = 3·j₀·γ + (7j₀ − 6912)/(j₀ − 1728)`, rational since `j₀, γ ∈ ℚ`,
   `j₀ ≠ 1728`.

## What is proved here

Everything, unconditionally:
* all the arithmetic/nonvanishing inputs: `j₀ := 1728·J(τ₁₆₃) ∈ ℚ`, `j₀ ≠ 0`,
  `j₀ ≠ 1728`, `E₄(τ₁₆₃) ≠ 0`, `E₆(τ₁₆₃) ≠ 0`;
* the closed-form modular identity `E₄³/E₆² = j₀/(j₀ − 1728)`;
* the geometric data of steps 1–2 (`Λ` fixes `τ₁₆₃`, `(2τ − 1)² = −163`, the coset
  factorization `Λ = γ · Acol 163 (−82)`, and the identity `j(Λ • z) = f₁₆₃(81) z` on all
  of `ℍ` — one vanishing factor of Masser's `F`);
* the full reduction (step 5): given Masser's post-Ramanujan identity (the analytic
  gate `hMasser`), `s₂(τ₁₆₃)` is rational (`masser_s₂_rational_of`);
* **the analytic gate itself** (`masser_gate`, second half of this file): the chart
  calculus of `F(z) = Φ₁₆₃(j(Λz), j z) ≡ 0` (first- and second-derivative extraction at
  `τ₁₆₃`, `masser_bivariate_derivs`), Masser's Lemma A1 (`β₁₀ ≠ 0`, via the
  `p² − pk + 41k² = 163` fixed-matrix classification), and the Ramanujan substitution
  turning `(105)` into the gate identity with `γ = (β₂₀ − 2β₁₁ + β₀₂)/β₀₁ ∈ ℚ`.

The top-level deliverable is `masser_s₂_rational : ∃ r : ℚ, s₂ τ₁₆₃ = r`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries
open scoped Real Manifold MatrixGroups

instance : NeZero (163 : ℕ) := ⟨by norm_num⟩

/-! ## Step 1 — the trace-zero fixing matrix `Λ = !![1, −82; 2, −1]`

`det Λ = 163`, `Λ • τ₁₆₃ = τ₁₆₃`, and the Möbius square-root data `(2τ − 1)² = −163`.
These are the geometric inputs to Masser's second-order Taylor expansion (step 3). -/

/-- `(2τ₁₆₃ − 1)² = −163`, from `τ₁₆₃² = τ₁₆₃ − 41`.  (So `2τ₁₆₃ − 1 = i√163`, the pure
imaginary generator of the CM order; `(2τ − 1)/2 = i·Im τ₁₆₃`.) -/
lemma two_tau_sub_one_sq : (2 * (τ₁₆₃ : ℂ) - 1) ^ 2 = -163 := by
  linear_combination (4 : ℂ) * τ₁₆₃_sq

/-- `2τ₁₆₃ − 1 ≠ 0` (its square is `−163 ≠ 0`). -/
lemma two_tau_sub_one_ne_zero : 2 * (τ₁₆₃ : ℂ) - 1 ≠ 0 := by
  intro h
  have := two_tau_sub_one_sq
  rw [h] at this
  norm_num at this

/-- The trace-zero fixing matrix `Λ = !![1, −82; 2, −1]` as an element of `GL (Fin 2) ℝ`
(determinant `163 > 0`). -/
def LamGL : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![1, -82; 2, -1] (by rw [Matrix.det_fin_two_of]; norm_num)

@[simp] lemma val_LamGL : (LamGL).val = !![1, -82; 2, -1] := rfl

lemma LamGL_det_pos : 0 < (LamGL).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_LamGL, Matrix.det_fin_two_of]
  norm_num

/-- **`Λ` fixes `τ₁₆₃`** as a Möbius transformation: `(τ − 82)/(2τ − 1) = τ`. -/
lemma LamGL_smul_eq : LamGL • τ₁₆₃ = τ₁₆₃ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos LamGL_det_pos, div_eq_iff (denom_ne_zero LamGL τ₁₆₃)]
  simp only [num, denom, val_LamGL, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  linear_combination (-2 : ℂ) * τ₁₆₃_sq

/-- The `SL(2,ℤ)` cofactor `γ = !![1, 0; 2, 1]` (determinant `1`) of the coset
decomposition `Λ = γ · Acol 163 (−82)`. -/
def LamGamma : SL(2, ℤ) :=
  ⟨!![1, 0; 2, 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- **Coset decomposition** `Λ = γ · Acol 163 (−82)` in `GL (Fin 2) ℝ`. -/
lemma LamGL_factor : LamGL = (LamGamma : GL (Fin 2) ℝ) * Acol 163 (-82) := by
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  fin_cases a <;> fin_cases c <;>
    norm_num [val_LamGL, val_Acol, LamGamma, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Step 2 — coset identification.** For *every* `z : ℍ`, `j(Λ • z)` equals the
`81`-coset orbit value `f 163 (some 81) z` (since `−82 ≡ 81 mod 163`).  Hence one factor of
the orbit product `Φ₁₆₃(·, j z)` vanishes at `X = j(Λz)`, i.e. Masser's `F(z) = 0`. -/
lemma j_LamGL_smul (z : ℍ) : j (LamGL • z) = f 163 (some (81 : ZMod 163)) z := by
  have htrans := j_matrix_transfer LamGamma LamGL (Acol 163 (-82)) z LamGL_factor
  rw [htrans, f_some]
  have hval : ((81 : ZMod 163).val : ℤ) = 81 := by decide
  refine j_Acol_smul_congr ?_ z
  rw [hval]; decide

/-! ## Arithmetic and nonvanishing inputs at `τ₁₆₃` -/

/-- `J(τ₁₆₃) ≠ 0`: it has norm `> 1` (Estimates `one_lt_norm_J`). -/
lemma J_τ₁₆₃_ne_zero : J τ₁₆₃ ≠ 0 := by
  have h := one_lt_norm_J τ₁₆₃_mem_Region
  intro hc
  rw [hc, norm_zero] at h
  linarith

/-- `j₀ := 1728·J(τ₁₆₃) ≠ 0`. -/
lemma j₀_ne_zero : (1728 : ℂ) * J τ₁₆₃ ≠ 0 :=
  mul_ne_zero (by norm_num) J_τ₁₆₃_ne_zero

/-- `j₀ ≠ 1728`: `J(τ₁₆₃) ≠ 1` since `‖J(τ₁₆₃)‖ > 1`. -/
lemma j₀_ne_1728 : (1728 : ℂ) * J τ₁₆₃ ≠ 1728 := by
  intro hc
  have hJ1 : J τ₁₆₃ = 1 :=
    mul_left_cancel₀ (show (1728 : ℂ) ≠ 0 by norm_num) (by rw [hc]; ring)
  have h := one_lt_norm_J τ₁₆₃_mem_Region
  rw [hJ1, norm_one] at h
  linarith

/-- `E₆(τ₁₆₃) ≠ 0` (Estimates `E₆_ne_zero_of_mem_Region`). -/
lemma E₆_τ₁₆₃_ne_zero : E₆ τ₁₆₃ ≠ 0 :=
  E₆_ne_zero_of_mem_Region τ₁₆₃_mem_Region

/-- `E₄(τ₁₆₃) ≠ 0`: else `j₀ = E₄³/Δ = 0`, contradicting `j₀ ≠ 0`. -/
lemma E₄_τ₁₆₃_ne_zero : E₄ τ₁₆₃ ≠ 0 := by
  intro h
  have hjm := j_mul_discriminant τ₁₆₃
  rw [show j τ₁₆₃ = 1728 * J τ₁₆₃ from rfl, h] at hjm
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hjm
  rcases mul_eq_zero.mp hjm with h1 | h1
  · exact j₀_ne_zero h1
  · exact discriminant_ne_zero τ₁₆₃ h1

/-- `j₀ ∈ ℚ` (statement 2). Derived locally from `Kronecker.lean` + `Rationality.lean`
(rather than from the pin file `LeanPool.Chudnovsky.SingularModuli`, which imports THIS file
to fill its `s₂_τ₁₆₃_rational` pin — importing it here would be a cycle). -/
lemma j₀_rational : ∃ r : ℚ, (1728 : ℂ) * J τ₁₆₃ = (r : ℂ) := by
  have hint : IsIntegral ℤ ((1728 : ℂ) * J τ₁₆₃) := by
    haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    haveI : NeZero (41 : ℕ) := ⟨by norm_num⟩
    obtain ⟨PhiZ, hPhi⟩ := exists_PhiZ_closed (m := 41)
    obtain ⟨i, hi⟩ := cm_coset_rel (m := 41) 0 (by norm_num)
    exact isIntegral_j_of_cm hPhi hi.symm
  exact j_τ₁₆₃_rational_of j_surjective hint

/-! ## The closed-form modular identity `E₄³/E₆² = j₀/(j₀ − 1728)` -/

/-- `E₄³ = j₀·Δ` at `τ₁₆₃`. -/
lemma E₄_cube_τ₁₆₃ : (E₄ τ₁₆₃) ^ 3 = (1728 * J τ₁₆₃) * discriminant τ₁₆₃ := by
  have h := mul_J_eq τ₁₆₃
  have hΔ := discriminant_ne_zero τ₁₆₃
  field_simp at h
  linear_combination -h

/-- `E₆² = (j₀ − 1728)·Δ` at `τ₁₆₃`. -/
lemma E₆_sq_τ₁₆₃ : (E₆ τ₁₆₃) ^ 2 = ((1728 * J τ₁₆₃) - 1728) * discriminant τ₁₆₃ := by
  have h := E₄_cube_sub_E₆_sq_eq_discriminant τ₁₆₃
  rw [E₄_cube_τ₁₆₃] at h
  linear_combination -h

/-- **The closed-form identity** `E₄³/E₆² = j₀/(j₀ − 1728)` at `τ₁₆₃`
(the algebraic heart of the `s₂`-formula's non-`γ` term). -/
lemma E₄_cube_div_E₆_sq_τ₁₆₃ :
    (E₄ τ₁₆₃) ^ 3 / (E₆ τ₁₆₃) ^ 2 = (1728 * J τ₁₆₃) / ((1728 * J τ₁₆₃) - 1728) := by
  rw [E₄_cube_τ₁₆₃, E₆_sq_τ₁₆₃]
  exact mul_div_mul_right _ _ (discriminant_ne_zero τ₁₆₃)

/-! ## The gated top-level theorem (step 5 reduction, fully assembled) -/

/-- **Masser's Theorem A1 at `τ₁₆₃`, assembled around the analytic gate.**

`hMasser` is Masser's identity (106) *before* solving for `s₂`: the post-Ramanujan form of
his second-order Taylor identity (105), asserting the existence of a rational `γ` (Masser's
`(β₂₀ − β₁₁ + β₀₂)/β₀₁ ∈ ℚ`) with

`E₂*(τ₁₆₃) = 3·j₀·(E₆/E₄)·γ + 4·(E₆/E₄) + 3·E₄²/E₆`.

Given it, `s₂(τ₁₆₃) = (E₄/E₆)·E₂* = 3·j₀·γ + 4 + 3·E₄³/E₆² = 3·j₀·γ + (7j₀−6912)/(j₀−1728)`
is rational. -/
theorem masser_s₂_rational_of
    (hMasser : ∃ γ : ℚ, E₂star τ₁₆₃
        = 3 * (1728 * J τ₁₆₃) * (E₆ τ₁₆₃ / E₄ τ₁₆₃) * (γ : ℂ)
          + 4 * (E₆ τ₁₆₃ / E₄ τ₁₆₃)
          + 3 * (E₄ τ₁₆₃) ^ 2 / E₆ τ₁₆₃) :
    ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ) := by
  obtain ⟨γ, hγ⟩ := hMasser
  obtain ⟨rj, hrj⟩ := j₀_rational
  have hE4 : E₄ τ₁₆₃ ≠ 0 := E₄_τ₁₆₃_ne_zero
  have hE6 : E₆ τ₁₆₃ ≠ 0 := E₆_τ₁₆₃_ne_zero
  have hne : (1728 : ℂ) * J τ₁₆₃ - 1728 ≠ 0 := sub_ne_zero.mpr j₀_ne_1728
  -- `s₂ = 3·j₀·γ + 4 + 3·E₄³/E₆²`
  have key : s₂ τ₁₆₃
      = 3 * (1728 * J τ₁₆₃) * (γ : ℂ) + 4 + 3 * ((E₄ τ₁₆₃) ^ 3 / (E₆ τ₁₆₃) ^ 2) := by
    rw [s₂, hγ]
    field_simp
  -- substitute the closed-form identity and `j₀ = rj`
  rw [E₄_cube_div_E₆_sq_τ₁₆₃, hrj] at key
  -- the answer as a rational number
  have hrjne : (rj : ℚ) - 1728 ≠ 0 := by
    rw [sub_ne_zero]
    intro hc
    exact j₀_ne_1728 (by rw [hrj, hc]; norm_num)
  refine ⟨3 * rj * γ + 4 + 3 * rj / (rj - 1728), ?_⟩
  rw [key]
  push_cast
  ring

/-! ## Discharging the analytic gate

The remainder of this file proves the gate hypothesis `hMasser` of `masser_s₂_rational_of`
and derives the unconditional `masser_s₂_rational`.  Structure:

* **Chart calculus** (`masserLam`, `cj`, `masserGD`): the Möbius map `λ(z) = (z−82)/(2z−1)`
  of `Λ` and the `j`-function in the `ℂ`-chart, with explicit first derivatives on
  `{0 < Im z}` and the second derivative of `j∘ofComplex` at `τ₁₆₃` via the Ramanujan
  identities.
* **Master second-derivative lemma** (`masser_bivariate_derivs`): for a finite sum
  `F(z) = Σₙ pₙ(v z)·(u z)ⁿ` vanishing on the upper half-plane, the first and second
  derivatives at an interior point, expanded in the five partial-derivative sums
  (the Taylor coefficients `β₁₀, β₀₁, β₂₀, β₁₁, β₀₂` of `Φ₁₆₃` at `(j₀, j₀)`).
* **Vanishing input**: `F(z) = Φ₁₆₃(j(λz), j z) = 0` on `ℍ` from `j_LamGL_smul` (step 2).
* **Masser's Lemma A1** (`masser_lemmaA1`): no coset other than `some 81` takes the value
  `j τ₁₆₃` at `τ₁₆₃` (the `p² − pk + 41k² = 163` classification), whence `β₁₀ ≠ 0`.
* **Assembly**: `β₁₀ = β₀₁`, division by `g′(τ)² β₀₁ ≠ 0`, and the Ramanujan substitution
  produce the gate identity with `γ = (β₂₀ − 2β₁₁ + β₀₂)/β₀₁ ∈ ℚ`. -/

open Polynomial Filter
open scoped Topology

private instance : Fact (Nat.Prime 163) := ⟨by norm_num⟩

/-! ### The Möbius chart map `λ(z) = (z − 82)/(2z − 1)` -/

/-- The Möbius transformation of `Λ` in the `ℂ`-chart: `λ(z) = (z − 82)/(2z − 1)`. -/
private def masserLam (z : ℂ) : ℂ := (z - 82) / (2 * z - 1)

private lemma two_mul_sub_one_ne_zero {z : ℂ} (hz : 0 < z.im) : 2 * z - 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.one_im, Complex.zero_im] at him
  norm_num at him
  nlinarith [him, hz]

/-- `λ` matches the `GL₂`-action: `↑(Λ • ofComplex z) = λ z` for `z` in the upper half-plane. -/
private lemma coe_LamGL_smul_ofComplex {z : ℂ} (hz : 0 < z.im) :
    ((LamGL • ofComplex z : ℍ) : ℂ) = masserLam z := by
  rw [coe_smul_of_det_pos LamGL_det_pos, num, denom, val_LamGL]
  have hcoe : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, hcoe, masserLam]
  push_cast
  ring_nf

/-- `λ` maps the upper half-plane to itself (it is the action of `Λ`, `det Λ > 0`). -/
private lemma masserLam_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (masserLam z).im := by
  rw [← coe_LamGL_smul_ofComplex hz]
  exact (LamGL • ofComplex z).im_pos

/-- In the chart, `ofComplex (λ z) = Λ • ofComplex z`. -/
private lemma ofComplex_masserLam {z : ℂ} (hz : 0 < z.im) :
    ofComplex (masserLam z) = LamGL • ofComplex z := by
  rw [← coe_LamGL_smul_ofComplex hz, ofComplex_apply]

/-- `τ₁₆₃` is the fixed point of `λ`. -/
private lemma masserLam_tau : masserLam (τ₁₆₃ : ℂ) = (τ₁₆₃ : ℂ) := by
  rw [masserLam, div_eq_iff (two_mul_sub_one_ne_zero τ₁₆₃.im_pos)]
  linear_combination (-2 : ℂ) * τ₁₆₃_sq

/-- `λ′(z) = 163/(2z − 1)²`. -/
private lemma hasDerivAt_masserLam {z : ℂ} (hz : 2 * z - 1 ≠ 0) :
    HasDerivAt masserLam (163 / (2 * z - 1) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ ↦ w - 82) 1 z := (hasDerivAt_id z).sub_const 82
  have hden : HasDerivAt (fun w : ℂ ↦ 2 * w - 1) 2 z := by
    simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).sub_const 1
  refine (hnum.fun_div hden hz).congr_deriv ?_
  congr 1
  ring

/-! ### The `j`-function in the `ℂ`-chart and its first two derivatives

`cj = j ∘ ofComplex`, with `cj′ = masserGD` on `{0 < Im z}` (from the Ramanujan
identities `deriv_comp_ofComplex_E₄/E₆`), and the explicit second derivative
`masserG2` at `τ₁₆₃`. -/

/-- `E₄` in the `ℂ`-chart. -/
private def cE₄ : ℂ → ℂ := fun w ↦ E₄ (ofComplex w)

/-- `E₆` in the `ℂ`-chart. -/
private def cE₆ : ℂ → ℂ := fun w ↦ E₆ (ofComplex w)

/-- `j` in the `ℂ`-chart. -/
private def cj : ℂ → ℂ := fun w ↦ j (ofComplex w)

/-- The first derivative of `cj` on the upper half-plane:
`cj′(w) = −2πi·1728·E₄²E₆/(E₄³ − E₆²)` (all evaluated at `ofComplex w`). -/
private def masserGD : ℂ → ℂ := fun w ↦
  -(2 * (π : ℂ) * Complex.I) * (1728 * cE₄ w ^ 2 * cE₆ w) / (cE₄ w ^ 3 - cE₆ w ^ 2)

private lemma hasDerivAt_cE₄ {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE₄ (2 * (π : ℂ) * Complex.I / 3 * (E2 (ofComplex w) * cE₄ w - cE₆ w)) w := by
  have hcoe : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hw]
  have h1 : DifferentiableOn ℂ (⇑E₄ ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo E₄)
  have hd : DifferentiableAt ℂ (⇑E₄ ∘ ofComplex) w :=
    (h1 _ hw).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hw)
  have hval := deriv_comp_ofComplex_E₄ (ofComplex w)
  rw [hcoe] at hval
  exact hd.hasDerivAt.congr_deriv hval

private lemma hasDerivAt_cE₆ {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt cE₆ ((π : ℂ) * Complex.I * (E2 (ofComplex w) * cE₆ w - cE₄ w ^ 2)) w := by
  have hcoe : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hw]
  have h1 : DifferentiableOn ℂ (⇑E₆ ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo E₆)
  have hd : DifferentiableAt ℂ (⇑E₆ ∘ ofComplex) w :=
    (h1 _ hw).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hw)
  have hval := deriv_comp_ofComplex_E₆ (ofComplex w)
  rw [hcoe] at hval
  exact hd.hasDerivAt.congr_deriv hval

private lemma cden_ne_zero (w : ℂ) : cE₄ w ^ 3 - cE₆ w ^ 2 ≠ 0 :=
  E₄_cube_sub_E₆_sq_ne_zero (ofComplex w)

/-- `cj = 1728·E₄³/(E₄³ − E₆²)` in the chart. -/
private lemma cj_eq (w : ℂ) : cj w = 1728 * cE₄ w ^ 3 / (cE₄ w ^ 3 - cE₆ w ^ 2) := by
  simp only [cj, cE₄, cE₆, j_def, J]
  ring

/-- **First derivative of `j` in the chart**: `HasDerivAt cj (masserGD w) w` on `Im w > 0`. -/
private lemma hasDerivAt_cj {w : ℂ} (hw : 0 < w.im) : HasDerivAt cj (masserGD w) w := by
  have h4 := hasDerivAt_cE₄ hw
  have h6 := hasDerivAt_cE₆ hw
  have hq := (((h4.fun_pow 3).const_mul (1728 : ℂ)).fun_div
    ((h4.fun_pow 3).fun_sub (h6.fun_pow 2)) (cden_ne_zero w))
  have hev : cj =ᶠ[𝓝 w] fun z ↦ 1728 * cE₄ z ^ 3 / (cE₄ z ^ 3 - cE₆ z ^ 2) :=
    Filter.Eventually.of_forall fun z ↦ cj_eq z
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hden := cden_ne_zero w
  rw [masserGD, div_eq_div_iff (pow_ne_zero 2 hden) hden]
  ring

/-- The second derivative of `cj` at `τ₁₆₃`:
`cj''(τ) = 2·1728·π²·(E₂E₄²E₆/3 − 4E₄E₆²/3 − E₄⁴)/(E₄³ − E₆²)`. -/
private def masserG2 : ℂ :=
  2 * 1728 * (π : ℂ) ^ 2 *
      (E2 τ₁₆₃ * E₄ τ₁₆₃ ^ 2 * E₆ τ₁₆₃ / 3 - 4 * E₄ τ₁₆₃ * E₆ τ₁₆₃ ^ 2 / 3 - E₄ τ₁₆₃ ^ 4)
    / (E₄ τ₁₆₃ ^ 3 - E₆ τ₁₆₃ ^ 2)

private lemma cE₄_tau : cE₄ (τ₁₆₃ : ℂ) = E₄ τ₁₆₃ := by rw [cE₄, ofComplex_apply]
private lemma cE₆_tau : cE₆ (τ₁₆₃ : ℂ) = E₆ τ₁₆₃ := by rw [cE₆, ofComplex_apply]
private lemma cj_tau : cj (τ₁₆₃ : ℂ) = j τ₁₆₃ := by rw [cj, ofComplex_apply]

/-- The value `masserGD τ₁₆₃` (the chart derivative `g′(τ₁₆₃)`), in Eisenstein terms. -/
private lemma masserGD_tau :
    masserGD (τ₁₆₃ : ℂ) = -(2 * (π : ℂ) * Complex.I) * (1728 * E₄ τ₁₆₃ ^ 2 * E₆ τ₁₆₃)
      / (E₄ τ₁₆₃ ^ 3 - E₆ τ₁₆₃ ^ 2) := by
  rw [masserGD, cE₄_tau, cE₆_tau]

/-- **Second derivative of `j` in the chart at `τ₁₆₃`**: `HasDerivAt masserGD masserG2 τ₁₆₃`. -/
private lemma hasDerivAt_masserGD : HasDerivAt masserGD masserG2 (τ₁₆₃ : ℂ) := by
  have hw : 0 < (τ₁₆₃ : ℂ).im := τ₁₆₃.im_pos
  have h4 := hasDerivAt_cE₄ hw
  have h6 := hasDerivAt_cE₆ hw
  have hnum := (((h4.fun_pow 2).fun_mul h6).const_mul
    (-(2 * (π : ℂ) * Complex.I) * 1728))
  have hq := hnum.fun_div ((h4.fun_pow 3).fun_sub (h6.fun_pow 2)) (cden_ne_zero (τ₁₆₃ : ℂ))
  have hev : masserGD =ᶠ[𝓝 (τ₁₆₃ : ℂ)] fun z ↦
      -(2 * (π : ℂ) * Complex.I) * 1728 * (cE₄ z ^ 2 * cE₆ z) / (cE₄ z ^ 3 - cE₆ z ^ 2) :=
    Filter.Eventually.of_forall fun z ↦ by rw [masserGD]; ring_nf
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hden : cE₄ (τ₁₆₃ : ℂ) ^ 3 - cE₆ (τ₁₆₃ : ℂ) ^ 2 ≠ 0 := cden_ne_zero _
  have hE2 : E2 (ofComplex (τ₁₆₃ : ℂ)) = E2 τ₁₆₃ := by rw [ofComplex_apply]
  rw [hE2, masserG2, ← cE₄_tau, ← cE₆_tau, div_eq_div_iff (pow_ne_zero 2 hden) hden]
  linear_combination (-1152 * (π : ℂ) ^ 2 * cE₄ (τ₁₆₃ : ℂ)
      * (cE₄ (τ₁₆₃ : ℂ) ^ 3 - cE₆ (τ₁₆₃ : ℂ) ^ 2) ^ 2
      * (E2 τ₁₆₃ * cE₄ (τ₁₆₃ : ℂ) * cE₆ (τ₁₆₃ : ℂ) - 3 * cE₄ (τ₁₆₃ : ℂ) ^ 3
        - 4 * cE₆ (τ₁₆₃ : ℂ) ^ 2)) * Complex.I_sq

/-! ### The master second-derivative lemma

For a finite family of polynomials `pₙ ∈ ℂ[X]` and functions `u, v` differentiable on the
upper half-plane such that `F(z) = Σₙ pₙ(v z)·(u z)ⁿ` vanishes identically there, the first
and second derivatives of `F` at an interior point `t` vanish; expanded by the chain rule
they give the two linear relations among the five partial-derivative sums (the `β`'s of
Masser's proof) used below. -/

private lemma hasDerivAt_poly_comp {P : Polynomial ℂ} {v : ℂ → ℂ} {v' z : ℂ}
    (hv : HasDerivAt v v' z) :
    HasDerivAt (fun y ↦ P.eval (v y)) ((P.derivative).eval (v z) * v') z := by
  simpa [Function.comp_def] using (P.hasDerivAt (v z)).comp z hv

private lemma masser_bivariate_derivs
    (s : Finset ℕ) (p : ℕ → Polynomial ℂ) (u v u' v' : ℂ → ℂ) (t u'' v'' : ℂ)
    (ht : 0 < t.im)
    (hu : ∀ z : ℂ, 0 < z.im → HasDerivAt u (u' z) z)
    (hv : ∀ z : ℂ, 0 < z.im → HasDerivAt v (v' z) z)
    (hu' : HasDerivAt u' u'' t) (hv' : HasDerivAt v' v'' t)
    (hF : ∀ z : ℂ, 0 < z.im → ∑ n ∈ s, (p n).eval (v z) * u z ^ n = 0) :
    ((∑ n ∈ s, ((p n).derivative).eval (v t) * u t ^ n) * v' t
        + (∑ n ∈ s, (p n).eval (v t) * ((n : ℂ) * u t ^ (n - 1))) * u' t = 0)
    ∧ ((∑ n ∈ s, ((p n).derivative.derivative).eval (v t) * u t ^ n) * v' t ^ 2
        + (∑ n ∈ s, ((p n).derivative).eval (v t) * u t ^ n) * v''
        + (∑ n ∈ s, ((p n).derivative).eval (v t) * ((n : ℂ) * u t ^ (n - 1)))
            * (2 * v' t * u' t)
        + (∑ n ∈ s, (p n).eval (v t) * ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * u t ^ (n - 1 - 1))))
            * u' t ^ 2
        + (∑ n ∈ s, (p n).eval (v t) * ((n : ℂ) * u t ^ (n - 1))) * u'' = 0) := by
  -- the explicit first-derivative function `A`
  set A : ℂ → ℂ := fun z ↦ ∑ n ∈ s,
    (((p n).derivative).eval (v z) * v' z * u z ^ n
      + (p n).eval (v z) * ((n : ℂ) * u z ^ (n - 1) * u' z)) with hA
  -- `F′ = A` on the upper half-plane
  have hFA : ∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun y ↦ ∑ n ∈ s, (p n).eval (v y) * u y ^ n) (A z) z := by
    intro z hz
    exact HasDerivAt.fun_sum fun n _ ↦
      (hasDerivAt_poly_comp (hv z hz)).fun_mul ((hu z hz).fun_pow n)
  -- `A ≡ 0` on the upper half-plane (as `F ≡ 0` there)
  have hA0 : ∀ z : ℂ, 0 < z.im → A z = 0 := by
    intro z hz
    have h1 : deriv (fun y ↦ ∑ n ∈ s, (p n).eval (v y) * u y ^ n) z = A z := (hFA z hz).deriv
    have h2 : (fun y ↦ ∑ n ∈ s, (p n).eval (v y) * u y ^ n) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) :=
      eventually_of_mem (isOpen_upperHalfPlaneSet.mem_nhds hz) fun y hy ↦ hF y hy
    rw [← h1, h2.deriv_eq, deriv_const]
  constructor
  · -- first-order relation: regroup `A t = 0`
    have h1 := hA0 t ht
    rw [hA] at h1
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← h1]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  · -- second-order relation: differentiate `A` at `t`
    have hut := hu t ht
    have hAd : HasDerivAt A (∑ n ∈ s,
        ((((p n).derivative.derivative).eval (v t) * v' t * v' t
            + ((p n).derivative).eval (v t) * v'') * u t ^ n
          + ((p n).derivative).eval (v t) * v' t * ((n : ℂ) * u t ^ (n - 1) * u' t)
          + (((p n).derivative).eval (v t) * v' t * ((n : ℂ) * u t ^ (n - 1) * u' t)
            + (p n).eval (v t) *
              ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * u t ^ (n - 1 - 1) * u' t) * u' t
                + (n : ℂ) * u t ^ (n - 1) * u'')))) t := by
      rw [hA]
      refine HasDerivAt.fun_sum fun n _ ↦ ?_
      have h1 : HasDerivAt (fun y ↦ ((p n).derivative).eval (v y) * v' y * u y ^ n)
          ((((p n).derivative.derivative).eval (v t) * v' t * v' t
              + ((p n).derivative).eval (v t) * v'') * u t ^ n
            + ((p n).derivative).eval (v t) * v' t * ((n : ℂ) * u t ^ (n - 1) * u' t)) t :=
        ((hasDerivAt_poly_comp (hv t ht)).fun_mul hv').fun_mul (hut.fun_pow n)
      have h2 : HasDerivAt (fun y ↦ (p n).eval (v y) * ((n : ℂ) * u y ^ (n - 1) * u' y))
          (((p n).derivative).eval (v t) * v' t * ((n : ℂ) * u t ^ (n - 1) * u' t)
            + (p n).eval (v t) *
              ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * u t ^ (n - 1 - 1) * u' t) * u' t
                + (n : ℂ) * u t ^ (n - 1) * u'')) t := by
        refine (hasDerivAt_poly_comp (hv t ht)).fun_mul ?_
        exact ((hut.fun_pow (n - 1)).const_mul ((n : ℂ))).fun_mul hu'
      exact h1.fun_add h2
    -- `deriv A t = 0` since `A ≡ 0` near `t`
    have hAzero : deriv A t = 0 := by
      have h2 : A =ᶠ[𝓝 t] fun _ ↦ (0 : ℂ) :=
        eventually_of_mem (isOpen_upperHalfPlaneSet.mem_nhds ht) fun y hy ↦ hA0 y hy
      rw [h2.deriv_eq, deriv_const]
    have hB0 := hAd.deriv.symm.trans hAzero
    -- regroup the vanishing raw second derivative into the five `β`-sums
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← hB0]
    exact Finset.sum_congr rfl fun n _ ↦ by ring

/-! ### Support-sum expansions of the specialized modular polynomial

`Φ₁₆₃ ∈ ℚ[Y][X]` is pinned via `exists_PhiQ_closed`; we expand `Φ₁₆₃(x, Y₀)` and its
`X`-derivative as sums over the (finite) support, the form consumed by the master lemma,
and record the `ℚ`-rationality of all evaluations at `(j₀, j₀)`, `j₀ = j τ₁₆₃ ∈ ℚ`. -/

private lemma aeval_eq_map_eval (Q : Polynomial ℚ) (Y₀ : ℂ) :
    (Polynomial.aeval Y₀) Q = (Q.map (algebraMap ℚ ℂ)).eval Y₀ := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]

/-- Evaluation of `specializeY Y₀ P` at `x` as a support sum. -/
private lemma specializeY_eval_sum (P : Polynomial (Polynomial ℚ)) (Y₀ x : ℂ) :
    (specializeY Y₀ P).eval x
      = ∑ n ∈ P.support, ((P.coeff n).map (algebraMap ℚ ℂ)).eval Y₀ * x ^ n := by
  rw [specializeY, coe_mapRingHom, eval_map, eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_eq_map_eval]

/-- Evaluation of the derivative of a `ℂ`-polynomial as a support sum. -/
private lemma eval_derivative_support_sum (P : Polynomial ℂ) (x : ℂ) :
    (Polynomial.derivative P).eval x = ∑ n ∈ P.support, P.coeff n * ((n : ℂ) * x ^ (n - 1)) := by
  rw [Polynomial.derivative_apply, Polynomial.sum_def, eval_finsetSum]
  exact Finset.sum_congr rfl fun n _ ↦ by
    rw [eval_mul, eval_C, eval_pow, eval_X]; ring

/-- The `β₁₀`-sum is the evaluated `X`-derivative of the specialized polynomial. -/
private lemma sum_eq_eval_derivative (P : Polynomial (Polynomial ℚ)) (Y₀ x : ℂ) :
    ∑ n ∈ P.support, ((P.coeff n).map (algebraMap ℚ ℂ)).eval Y₀ * ((n : ℂ) * x ^ (n - 1))
      = (Polynomial.derivative (specializeY Y₀ P)).eval x := by
  rw [eval_derivative_support_sum, specializeY, coe_mapRingHom]
  refine Eq.trans (Finset.sum_congr rfl fun n _ ↦ ?_)
    (Finset.sum_subset (support_map_subset _ _) fun n _ hn ↦ ?_).symm
  · rw [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_eq_map_eval]
  · rw [notMem_support_iff.mp hn, zero_mul]

/-- Rational evaluation: `P(↑r) = ↑(P(r))` for `P ∈ ℚ[Y]` mapped to `ℂ`. -/
private lemma ratCast_eval (P : Polynomial ℚ) (r : ℚ) :
    ((P.eval r : ℚ) : ℂ) = (P.map (algebraMap ℚ ℂ)).eval (r : ℂ) := by
  rw [show ((r : ℂ)) = algebraMap ℚ ℂ r from (eq_ratCast _ r).symm, eval_map, eval₂_at_apply,
    eq_ratCast]

/-! ### The pinned modular polynomial `Φ₁₆₃` and the rational `β`-data -/

/-- The modular polynomial `Φ₁₆₃ ∈ ℚ[Y][X]` (pinned choice from `exists_PhiQ_closed`). -/
private def masserPhi : Polynomial (Polynomial ℚ) := (exists_PhiQ_closed (m := 163)).choose

private lemma masserPhi_spec : ∀ τ : ℍ, orbitPoly 163 τ = specializeY (j τ) masserPhi :=
  (exists_PhiQ_closed (m := 163)).choose_spec

/-- The `X`-coefficients of `Φ₁₆₃`, mapped to `ℂ[X]`-coefficient polynomials in `Y`. -/
private def masserP (n : ℕ) : Polynomial ℂ := (masserPhi.coeff n).map (algebraMap ℚ ℂ)

/-- The pinned rational value of `j₀ = j τ₁₆₃` (from statement 2). -/
private def masserRj : ℚ := j₀_rational.choose

private lemma masserRj_spec : j τ₁₆₃ = (masserRj : ℂ) := j₀_rational.choose_spec

/-- `β₁₀ = ∂Φ/∂X (j₀, j₀) ∈ ℚ`. -/
private def mβ10 : ℚ :=
  ∑ n ∈ masserPhi.support, (masserPhi.coeff n).eval masserRj * (n * masserRj ^ (n - 1))

/-- `β₀₁ = ∂Φ/∂Y (j₀, j₀) ∈ ℚ`. -/
private def mβ01 : ℚ :=
  ∑ n ∈ masserPhi.support, ((masserPhi.coeff n).derivative).eval masserRj * masserRj ^ n

/-- `β₁₁ = ∂²Φ/∂X∂Y (j₀, j₀) ∈ ℚ`. -/
private def mβ11 : ℚ :=
  ∑ n ∈ masserPhi.support,
    ((masserPhi.coeff n).derivative).eval masserRj * (n * masserRj ^ (n - 1))

/-- `β₂₀ = ∂²Φ/∂X² (j₀, j₀) ∈ ℚ`. -/
private def mβ20 : ℚ :=
  ∑ n ∈ masserPhi.support,
    (masserPhi.coeff n).eval masserRj * (n * ((n - 1 : ℕ) * masserRj ^ (n - 1 - 1)))

/-- `β₀₂ = ∂²Φ/∂Y² (j₀, j₀) ∈ ℚ`. -/
private def mβ02 : ℚ :=
  ∑ n ∈ masserPhi.support,
    ((masserPhi.coeff n).derivative.derivative).eval masserRj * masserRj ^ n

private lemma cast_mβ10 : ((mβ10 : ℚ) : ℂ)
    = ∑ n ∈ masserPhi.support, (masserP n).eval (j τ₁₆₃) * ((n : ℂ) * (j τ₁₆₃) ^ (n - 1)) := by
  rw [masserRj_spec, mβ10]
  push_cast [ratCast_eval]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [masserP]

private lemma cast_mβ01 : ((mβ01 : ℚ) : ℂ)
    = ∑ n ∈ masserPhi.support, ((masserP n).derivative).eval (j τ₁₆₃) * (j τ₁₆₃) ^ n := by
  rw [masserRj_spec, mβ01]
  push_cast [ratCast_eval]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [masserP, derivative_map]

private lemma cast_mβ11 : ((mβ11 : ℚ) : ℂ)
    = ∑ n ∈ masserPhi.support,
      ((masserP n).derivative).eval (j τ₁₆₃) * ((n : ℂ) * (j τ₁₆₃) ^ (n - 1)) := by
  rw [masserRj_spec, mβ11]
  push_cast [ratCast_eval]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [masserP, derivative_map]

private lemma cast_mβ20 : ((mβ20 : ℚ) : ℂ)
    = ∑ n ∈ masserPhi.support,
      (masserP n).eval (j τ₁₆₃) * ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * (j τ₁₆₃) ^ (n - 1 - 1))) := by
  rw [masserRj_spec, mβ20]
  push_cast [ratCast_eval]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [masserP]

private lemma cast_mβ02 : ((mβ02 : ℚ) : ℂ)
    = ∑ n ∈ masserPhi.support,
      ((masserP n).derivative.derivative).eval (j τ₁₆₃) * (j τ₁₆₃) ^ n := by
  rw [masserRj_spec, mβ02]
  push_cast [ratCast_eval]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [masserP, derivative_map, derivative_map]

/-! ### Masser's `F(z) = Φ₁₆₃(j(Λz), j z)` vanishes identically -/

/-- `F(z) = Σₙ Φₙ(j z)·j(Λz)ⁿ = Φ₁₆₃(j(Λz), j z) = 0` on the upper half-plane: `Λ` lies in
the coset `some 81` (step 2, `j_LamGL_smul`), so one factor of the orbit product vanishes. -/
private lemma masser_F_vanishes {z : ℂ} (hz : 0 < z.im) :
    ∑ n ∈ masserPhi.support, (masserP n).eval (cj z) * cj (masserLam z) ^ n = 0 := by
  have h1 : cj (masserLam z) = Chudnovsky.f 163 (some (81 : ZMod 163)) (ofComplex z) := by
    change j (ofComplex (masserLam z)) = _
    rw [ofComplex_masserLam hz, j_LamGL_smul]
  have h2 : ∑ n ∈ masserPhi.support, (masserP n).eval (cj z) * cj (masserLam z) ^ n
      = (specializeY (cj z) masserPhi).eval (cj (masserLam z)) :=
    (specializeY_eval_sum masserPhi (cj z) (cj (masserLam z))).symm
  rw [h2, show cj z = j (ofComplex z) from rfl, ← masserPhi_spec, orbitPoly_eval_eq_prod, h1]
  exact Finset.prod_eq_zero (Finset.mem_univ (some (81 : ZMod 163))) (sub_self _)

/-! ### The two Taylor relations at `τ₁₆₃` -/

private lemma masser_L1 : (163 : ℂ) / (2 * (τ₁₆₃ : ℂ) - 1) ^ 2 = -1 := by
  rw [two_tau_sub_one_sq]
  norm_num

private lemma masserGD_tau_ne_zero : masserGD (τ₁₆₃ : ℂ) ≠ 0 := by
  rw [masserGD_tau]
  refine div_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_pi_I_ne_zero) ?_)
    (E₄_cube_sub_E₆_sq_ne_zero τ₁₆₃)
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 E₄_τ₁₆₃_ne_zero)) E₆_τ₁₆₃_ne_zero

/-- **The first- and second-order Taylor relations** extracted from `F ≡ 0` at `τ₁₆₃`:
`β₁₀ = β₀₁` (using `Λ′(τ) = −1`, `g′(τ) ≠ 0`) and Masser's identity (105) in the raw form
`(β₂₀ − 2β₁₁ + β₀₂)·g′² + β₀₁·(2g'' + g′·Λ'') = 0`, `Λ''(τ) = 4/(2τ−1)`. -/
private lemma masser_relations :
    mβ10 = mβ01
    ∧ ((mβ20 : ℂ) - 2 * (mβ11 : ℂ) + (mβ02 : ℂ)) * masserGD (τ₁₆₃ : ℂ) ^ 2
        + (mβ01 : ℂ) * (2 * masserG2
          + masserGD (τ₁₆₃ : ℂ) * (4 / (2 * (τ₁₆₃ : ℂ) - 1))) = 0 := by
  have htau_ne := two_mul_sub_one_ne_zero τ₁₆₃.im_pos
  -- the ingredients of the master lemma
  have hu : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun z ↦ cj (masserLam z))
      (masserGD (masserLam z) * (163 / (2 * z - 1) ^ 2)) z := by
    intro z hz
    have h1 := hasDerivAt_cj (masserLam_im_pos hz)
    have h2 := hasDerivAt_masserLam (two_mul_sub_one_ne_zero hz)
    simpa [Function.comp_def] using h1.comp z h2
  have hv : ∀ z : ℂ, 0 < z.im → HasDerivAt cj (masserGD z) z := fun z hz ↦ hasDerivAt_cj hz
  have hu' : HasDerivAt (fun z ↦ masserGD (masserLam z) * (163 / (2 * z - 1) ^ 2))
      (masserG2 + masserGD (τ₁₆₃ : ℂ) * (4 / (2 * (τ₁₆₃ : ℂ) - 1))) (τ₁₆₃ : ℂ) := by
    have hgd : HasDerivAt masserGD masserG2 (masserLam (τ₁₆₃ : ℂ)) := by
      rw [masserLam_tau]; exact hasDerivAt_masserGD
    have h1 : HasDerivAt (fun z ↦ masserGD (masserLam z))
        (masserG2 * (163 / (2 * (τ₁₆₃ : ℂ) - 1) ^ 2)) (τ₁₆₃ : ℂ) := by
      simpa [Function.comp_def] using hgd.comp _ (hasDerivAt_masserLam htau_ne)
    have hlin : HasDerivAt (fun w : ℂ ↦ 2 * w - 1) 2 (τ₁₆₃ : ℂ) := by
      simpa using ((hasDerivAt_id ((τ₁₆₃ : ℂ))).const_mul (2 : ℂ)).sub_const 1
    have hdiv := (hasDerivAt_const ((τ₁₆₃ : ℂ)) (163 : ℂ)).fun_div (hlin.fun_pow 2)
      (pow_ne_zero 2 htau_ne)
    refine (h1.fun_mul hdiv).congr_deriv ?_
    rw [masser_L1, masserLam_tau]
    have hL2 : (0 * (2 * (τ₁₆₃ : ℂ) - 1) ^ 2
        - 163 * ((2 : ℕ) * (2 * (τ₁₆₃ : ℂ) - 1) ^ (2 - 1) * 2)) / ((2 * (τ₁₆₃ : ℂ) - 1) ^ 2) ^ 2
        = 4 / (2 * (τ₁₆₃ : ℂ) - 1) := by
      rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 htau_ne)) htau_ne]
      push_cast
      linear_combination (-4 * (2 * (τ₁₆₃ : ℂ) - 1) ^ 2) * two_tau_sub_one_sq
    rw [hL2]
    ring
  have hmaster := masser_bivariate_derivs masserPhi.support masserP
    (fun z ↦ cj (masserLam z)) cj
    (fun z ↦ masserGD (masserLam z) * (163 / (2 * z - 1) ^ 2)) masserGD
    (τ₁₆₃ : ℂ) (masserG2 + masserGD (τ₁₆₃ : ℂ) * (4 / (2 * (τ₁₆₃ : ℂ) - 1))) masserG2
    τ₁₆₃.im_pos hu hv hu' hasDerivAt_masserGD (fun z hz ↦ masser_F_vanishes hz)
  obtain ⟨h1, h2⟩ := hmaster
  rw [masserLam_tau, masser_L1, cj_tau] at h1 h2
  rw [← cast_mβ01, ← cast_mβ10] at h1
  rw [← cast_mβ02, ← cast_mβ01, ← cast_mβ11, ← cast_mβ20, ← cast_mβ10] at h2
  -- first relation: `β₁₀ = β₀₁`
  have hβ : mβ10 = mβ01 := by
    have hc : (((mβ01 : ℚ) : ℂ) - ((mβ10 : ℚ) : ℂ)) * masserGD (τ₁₆₃ : ℂ) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp hc with hc0 | hc0
    · exact_mod_cast (sub_eq_zero.mp hc0).symm
    · exact absurd hc0 masserGD_tau_ne_zero
  refine ⟨hβ, ?_⟩
  -- second relation: substitute `β₁₀ = β₀₁` and regroup
  have h10 : ((mβ10 : ℚ) : ℂ) = ((mβ01 : ℚ) : ℂ) := by exact_mod_cast hβ
  linear_combination h2 - (masserG2 + masserGD (τ₁₆₃ : ℂ) * (4 / (2 * (τ₁₆₃ : ℂ) - 1))) * h10

/-! ### Masser's Lemma A1 at `τ₁₆₃`: `β₁₀ ≠ 0`

`β₁₀ = ∏_{i ≠ some 81} (j₀ − fᵢ(τ₁₆₃))`, and no other coset value equals `j₀`: a coincidence
would produce an integer matrix fixing `τ₁₆₃` of determinant `163`; by the fixed-matrix
classification for the primitive form `(1, −1, 41)` its norm form gives
`p² − pk + 41k² = 163`, whose only solutions are `±(1, 2)`, i.e. the matrix is `±Λ` — and
`±Λ` lies in the coset `some 81`. -/

/-- The only integer solutions of `p² − pk + 41k² = 163` are `±(1, 2)`. -/
private lemma masser_norm_form_solve {p k : ℤ} (h : p * p - p * k + 41 * (k * k) = 163) :
    (p = 1 ∧ k = 2) ∨ (p = -1 ∧ k = -2) := by
  have hk1 : -2 ≤ k := by nlinarith [sq_nonneg (2 * p - k), sq_nonneg (k + 2), sq_nonneg (k - 2)]
  have hk2 : k ≤ 2 := by nlinarith [sq_nonneg (2 * p - k), sq_nonneg (k + 2), sq_nonneg (k - 2)]
  have hp1 : -13 ≤ p := by nlinarith [sq_nonneg (2 * p - k), sq_nonneg k]
  have hp2 : p ≤ 13 := by nlinarith [sq_nonneg (2 * p - k), sq_nonneg k]
  interval_cases k <;> interval_cases p <;> omega

/-- Structured version of `fixes_of_coset` retaining the matrix entries: if `γ ∈ SL(2,ℤ)`
sends the coset point `Aτ = (eτ′ + f)/g` to `τ′`, the integer matrix `γ·[[e,f],[0,g]]`
fixes `τ′` and has determinant `e·g`. -/
private lemma masser_fixes_of_coset {e f g : ℤ} (γ : SL(2, ℤ)) {Aτ τ' : ℍ}
    (hW : (Aτ : ℂ) = ((e : ℂ) * (τ' : ℂ) + (f : ℂ)) / (g : ℂ)) (hg : (g : ℂ) ≠ 0)
    (hfix : γ • Aτ = τ') :
    QF.Fixes (γ 0 0 * e) (γ 0 0 * f + γ 0 1 * g) (γ 1 0 * e) (γ 1 0 * f + γ 1 1 * g) τ'
      ∧ (γ 0 0 * e) * (γ 1 0 * f + γ 1 1 * g)
          - (γ 0 0 * f + γ 0 1 * g) * (γ 1 0 * e) = e * g := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (A := γ)
    rwa [Matrix.det_fin_two] at h
  constructor
  · have hco := coe_specialLinearGroup_apply γ Aτ
    rw [hfix] at hco
    have hden : (algebraMap ℤ ℝ (γ 1 0) : ℂ) * (Aτ : ℂ) + (algebraMap ℤ ℝ (γ 1 1) : ℂ) ≠ 0 := by
      intro h0
      simp only [eq_intCast] at h0
      push_cast at h0
      obtain ⟨hc0, hd0⟩ := QF.int_lin_eq_zero Aτ h0
      rw [hc0, hd0] at hdet
      simp at hdet
    rw [eq_div_iff hden, hW] at hco
    simp only [eq_intCast] at hco
    simp only [QF.Fixes]
    push_cast at hco ⊢
    field_simp at hco
    linear_combination -hco
  · linear_combination (e * g) * hdet

/-- **The `ℚ[Λ]`-classification at `τ₁₆₃`:** an integer matrix fixing `τ₁₆₃` with
determinant `163` is `±Λ = ±[[1, −82],[2, −1]]`. -/
private lemma masser_fixes_pm {p q r s : ℤ} (hfix : QF.Fixes p q r s τ₁₆₃)
    (hdet : p * s - q * r = 163) :
    (p = 1 ∧ q = -82 ∧ r = 2 ∧ s = -1) ∨ (p = -1 ∧ q = 82 ∧ r = -2 ∧ s = 1) := by
  have hroot : QF.IsRoot ⟨1, -1, 41⟩ τ₁₆₃ := by
    simp only [QF.IsRoot]
    push_cast
    linear_combination τ₁₆₃_sq
  have hprim : QF.IsPrimitive ⟨1, -1, 41⟩ := fun d hd _ _ ↦ isUnit_of_dvd_one hd
  have hpd : QF.IsPosDef ⟨1, -1, 41⟩ := ⟨one_pos, by norm_num [QF.disc]⟩
  obtain ⟨k, hr, hsp, hq⟩ := QF.fixes_classification hprim hpd hroot hfix
  dsimp only at hr hsp hq
  have heq : p * p - p * k + 41 * (k * k) = 163 := by
    have hs : s = p - k := by linarith [hsp]
    rw [hs, hr, hq] at hdet
    linear_combination hdet
  rcases masser_norm_form_solve heq with ⟨hp, hk⟩ | ⟨hp, hk⟩
  · exact Or.inl ⟨hp, by omega, by omega, by omega⟩
  · exact Or.inr ⟨hp, by omega, by omega, by omega⟩

/-- **Masser's Lemma A1 at `τ₁₆₃`** (drastically simplified by `163` squarefree): no coset
other than `some 81` takes the value `j τ₁₆₃` at `τ₁₆₃`. -/
private lemma masser_lemmaA1 {i : Option (ZMod 163)} (hi : i ≠ some (81 : ZMod 163)) :
    Chudnovsky.f 163 i τ₁₆₃ ≠ j τ₁₆₃ := by
  intro h
  cases i with
  | none =>
    have hj : j (AInf 163 • τ₁₆₃) = j τ₁₆₃ := by rw [← f_none]; exact h
    obtain ⟨γ, hγ⟩ := j_injective_mod_Γ hj
    obtain ⟨hfix, hdet⟩ := masser_fixes_of_coset (e := 163) (f := 0) (g := 1) γ
      (by rw [coe_AInf_smul]; push_cast; ring) (by norm_num) hγ.symm
    rcases masser_fixes_pm hfix (by linear_combination hdet) with ⟨hp, _, _, _⟩ | ⟨hp, _, _, _⟩
    all_goals omega
  | some b =>
    have hb : b ≠ (81 : ZMod 163) := fun hc ↦ hi (by rw [hc])
    have hj : j (Acol 163 (b.val : ℤ) • τ₁₆₃) = j τ₁₆₃ := by rw [← f_some]; exact h
    obtain ⟨γ, hγ⟩ := j_injective_mod_Γ hj
    obtain ⟨hfix, hdet⟩ := masser_fixes_of_coset (e := 1) (f := (b.val : ℤ)) (g := 163) γ
      (by rw [coe_Acol_smul]; push_cast; ring) (by norm_num) hγ.symm
    have hvlt : (b.val : ℤ) < 163 := by exact_mod_cast ZMod.val_lt b
    have hvnn : (0 : ℤ) ≤ (b.val : ℤ) := Int.natCast_nonneg _
    have hval : (b.val : ℤ) = 81 := by
      rcases masser_fixes_pm hfix (by linear_combination hdet)
        with ⟨hp, hq, _, _⟩ | ⟨hp, hq, _, _⟩
      · have h00 : γ 0 0 = 1 := by omega
        rw [h00, one_mul] at hq
        omega
      · have h00 : γ 0 0 = -1 := by omega
        rw [h00] at hq
        omega
    refine hb ?_
    have hnat : b.val = 81 := by exact_mod_cast hval
    calc b = ((b.val : ℕ) : ZMod 163) := (ZMod.natCast_zmod_val b).symm
      _ = ((81 : ℕ) : ZMod 163) := by rw [hnat]
      _ = (81 : ZMod 163) := by norm_cast

/-- **`β₁₀ ≠ 0`** (Masser's Lemma A1, assembled): the evaluated `X`-derivative of the orbit
product is `∏_{i ≠ some 81} (j₀ − fᵢ τ₁₆₃)`, and every factor is nonzero. -/
private lemma mβ10_ne_zero : mβ10 ≠ 0 := by
  have hf81 : Chudnovsky.f 163 (some (81 : ZMod 163)) τ₁₆₃ = j τ₁₆₃ := by
    rw [← j_LamGL_smul, LamGL_smul_eq]
  have hcast : ((mβ10 : ℚ) : ℂ)
      = (Polynomial.derivative (orbitPoly 163 τ₁₆₃)).eval (j τ₁₆₃) := by
    rw [cast_mβ10]
    simp only [masserP]
    rw [sum_eq_eval_derivative, ← masserPhi_spec]
  have hderiv : (Polynomial.derivative (orbitPoly 163 τ₁₆₃)).eval (j τ₁₆₃)
      = ∏ i ∈ Finset.univ.erase (some (81 : ZMod 163)),
          (j τ₁₆₃ - Chudnovsky.f 163 i τ₁₆₃) := by
    rw [orbitPoly, derivative_prod_finset, eval_finsetSum,
      Finset.sum_eq_single_of_mem (some (81 : ZMod 163)) (Finset.mem_univ _) ?_]
    · rw [derivative_X_sub_C, mul_one, eval_prod]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [eval_sub, eval_X, eval_C]
    · intro i _ hne
      rw [eval_mul]
      apply mul_eq_zero_of_left
      rw [eval_prod]
      refine Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨fun hc ↦ hne hc.symm, Finset.mem_univ _⟩) ?_
      rw [eval_sub, eval_X, eval_C, hf81, sub_self]
  have hne : ((mβ10 : ℚ) : ℂ) ≠ 0 := by
    rw [hcast, hderiv, Finset.prod_ne_zero_iff]
    intro i hi
    exact sub_ne_zero.mpr (Ne.symm (masser_lemmaA1 (Finset.mem_erase.mp hi).1))
  intro h0
  exact hne (by rw [h0]; norm_num)

/-! ### The gate and the unconditional theorem -/

private lemma two_tau_eq : 2 * (τ₁₆₃ : ℂ) - 1 = 2 * Complex.I * ((τ₁₆₃.im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re, show τ₁₆₃.re = 1 / 2 from rfl]
  · simp [Complex.mul_im, UpperHalfPlane.coe_im]

/-- **The analytic gate of `masser_s₂_rational_of`, discharged**: Masser's identity (106)
before solving for `s₂`, with `γ = (β₂₀ − 2β₁₁ + β₀₂)/β₀₁ ∈ ℚ`. -/
theorem masser_gate : ∃ γ : ℚ, E₂star τ₁₆₃
    = 3 * (1728 * J τ₁₆₃) * (E₆ τ₁₆₃ / E₄ τ₁₆₃) * (γ : ℂ)
      + 4 * (E₆ τ₁₆₃ / E₄ τ₁₆₃)
      + 3 * (E₄ τ₁₆₃) ^ 2 / E₆ τ₁₆₃ := by
  obtain ⟨hβeq, hrel⟩ := masser_relations
  have hb01 : mβ01 ≠ 0 := hβeq ▸ mβ10_ne_zero
  refine ⟨(mβ20 - 2 * mβ11 + mβ02) / mβ01, ?_⟩
  have h4 : E₄ τ₁₆₃ ≠ 0 := E₄_τ₁₆₃_ne_zero
  have h6 : E₆ τ₁₆₃ ≠ 0 := E₆_τ₁₆₃_ne_zero
  have hden : E₄ τ₁₆₃ ^ 3 - E₆ τ₁₆₃ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ₁₆₃
  have hb01C : ((mβ01 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hb01
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have him : ((τ₁₆₃.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt τ₁₆₃.im_pos)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [masserGD_tau, two_tau_eq] at hrel
  unfold masserG2 at hrel
  unfold E₂star J
  push_cast
  field_simp at hrel ⊢
  have hpre : ((π : ℝ) : ℂ) * 1728 * E₄ τ₁₆₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hπ (by norm_num)) h4
  have hrel2 : 2 ^ 2 * (((mβ20 : ℚ) : ℂ) - 2 * ((mβ11 : ℚ) : ℂ) + ((mβ02 : ℚ) : ℂ))
        * ((π : ℝ) : ℂ) * Complex.I ^ 2 * 1728 * E₄ τ₁₆₃ ^ 3 * E₆ τ₁₆₃ ^ 2 * 3
        * ((τ₁₆₃.im : ℝ) : ℂ)
      + (E₄ τ₁₆₃ ^ 3 - E₆ τ₁₆₃ ^ 2) * ((mβ01 : ℚ) : ℂ)
        * (2 ^ 2 * ((π : ℝ) : ℂ)
            * (E₆ τ₁₆₃ * (E₄ τ₁₆₃ * E2 τ₁₆₃ - E₆ τ₁₆₃ * 4) - E₄ τ₁₆₃ ^ 3 * 3)
            * ((τ₁₆₃.im : ℝ) : ℂ)
          - E₄ τ₁₆₃ * E₆ τ₁₆₃ * 3 * 4) = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left hpre
    linear_combination hrel
  linear_combination (1 / 4 : ℂ) * hrel2
    + (-5184 * E₄ τ₁₆₃ ^ 3 * E₆ τ₁₆₃ ^ 2 * ((τ₁₆₃.im : ℝ) : ℂ) * ((π : ℝ) : ℂ)
        * (((mβ02 : ℚ) : ℂ) - 2 * ((mβ11 : ℚ) : ℂ) + ((mβ20 : ℚ) : ℂ))) * Complex.I_sq

/-- **Masser's Theorem A1 at `τ₁₆₃`, unconditional** (Phase C, statement 3):
`s₂(τ₁₆₃) ∈ ℚ`.  This discharges the last analytic input of the Chudnovsky formula. -/
theorem masser_s₂_rational : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ) :=
  masser_s₂_rational_of masser_gate

end Chudnovsky
