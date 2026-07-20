/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.ModularPolynomialZ
import LeanPool.Chudnovsky.SingularModuli.CMRelations
import LeanPool.Chudnovsky.SingularModuli.Valence
import Mathlib.Tactic.NormNum.Prime

/-!
# Rationality of `j(τ₁₆₃)`: the three-prime argument (Phase C, §4.2)

This file implements `PhaseC-PLAN.md` §4.2, the "three-prime argument" proving that
`j₀ := j τ₁₆₃` is **rational** (hence, with statement 1, an integer).

The top-level target is

```
theorem j_τ₁₆₃_rational_of (hsurj : Function.Surjective (j : ℍ → ℂ))
    (hint : IsIntegral ℤ (j τ₁₆₃)) : ∃ r : ℚ, j τ₁₆₃ = (r : ℂ)
```

gated on surjectivity of `j` (proved in parallel in `Valence.lean`) and on integrality of
`j τ₁₆₃` (statement 1, proved in parallel).

## Structure of the proof (steps `(C1)`–`(C7)` of the plan)

Let `j₀ := j τ₁₆₃` and `x` an arbitrary complex root of `minpoly ℚ j₀`.

* **(C1)/(C2, transport)** Rather than a field embedding, we transport *polynomial identities*
  via `minpoly.dvd`: if `Φ_m(j₀, j₀) = 0` then `minpoly ℚ j₀ ∣ diagPhiQ Φ_m` (the diagonal
  `G_m(X) = Φ_m(X, X) ∈ ℚ[X]`), so `Φ_m(x, x) = G_m(x) = 0` for every root `x`.
* **(C2, input)** For each `m ∈ {41, 43, 61}` the CM matrix `M_n = [[n+1,−41],[1,n]]`
  (`CMRelations.cmMatrix_fixes`) fixes `τ₁₆₃`; decomposing `M_n = γ · Acol m n` with
  `γ ∈ SL(2,ℤ)` shows some coset value `f m i τ₁₆₃ = j τ₁₆₃`, whence `G_m(j₀) = 0`.
* **(C3)** Surjectivity gives `τ′` with `j τ′ = x`.
* **(C4)** `G_m(x) = 0 = ∏_i (x − f m i τ′)` produces a coset coincidence `f m i τ′ = j τ′`,
  hence an integer matrix of determinant `m` fixing `τ′`, i.e. a positive-definite integer
  form of discriminant `t² − 4m` rooted at `τ′`.
* **(C5)** The three forms are integer multiples of the common primitive form of `τ′`
  (discriminant `D₀`); `FormReduction.disc_of_three_relations` forces `D₀ = −163`.
* **(C6)** `FormReduction.cm_disc_neg163_smul_eq_τ₁₆₃`: `τ′` is `Γ`-equivalent to `τ₁₆₃`.
* **(C7)** Hence `x = j τ′ = j τ₁₆₃ = j₀`; every root of `minpoly ℚ j₀` equals `j₀`, and the
  Vieta relation on the subleading coefficient (a rational) forces `j₀ ∈ ℚ`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex Polynomial
open scoped Real Manifold MatrixGroups

/-! ## (C1)/(C2) The diagonal polynomial `G_m(X) = Φ_m(X, X) ∈ ℚ[X]` and its evaluation -/

/-- The diagonal polynomial `G_m(X) := Φ_m(X, X) ∈ ℚ[X]`, obtained by substituting the outer
variable `X` for the coefficient variable `Y` (the `ℚ`-analogue of `diagPhiZ`). -/
def diagPhiQ (PhiQ : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  PhiQ.eval (X : Polynomial ℚ)

/-- The diagonal substitution commutes with `Y ↦ z`: `G_m(z) = Φ_m(z, z)` for `z : ℂ`, where
the left side is `aeval z (diagPhiQ Φ_m)` and the right side is `(specializeY z Φ_m).eval z`. -/
theorem diagQ_aeval_eq (PhiQ : Polynomial (Polynomial ℚ)) (z : ℂ) :
    (aeval z) (diagPhiQ PhiQ) = (specializeY z PhiQ).eval z := by
  rw [diagPhiQ, aeval_def]
  have key : (eval₂RingHom (algebraMap ℚ ℂ) z).comp (evalRingHom (X : Polynomial ℚ))
      = eval₂RingHom (eval₂RingHom (algebraMap ℚ ℂ) z) z := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom, eval_C, eval₂_C]
    · simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom, eval_X, eval₂_X]
  have h := DFunLike.congr_fun key PhiQ
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom] at h
  rw [specializeY, coe_mapRingHom, eval_map]
  have hrh : ((Polynomial.aeval z).toRingHom : Polynomial ℚ →+* ℂ)
      = eval₂RingHom (algebraMap ℚ ℂ) z := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_ <;> simp
  rw [hrh]
  exact h

/-- `G_m(j τ) = ∏_i (j τ − f m i τ)`: evaluating the diagonal polynomial at `j τ` recovers the
orbit product. -/
theorem diagQ_eval_eq_prod {m : ℕ} [NeZero m] {PhiQ : Polynomial (Polynomial ℚ)}
    (hPhiQ : ∀ τ : ℍ, orbitPoly m τ = specializeY (j τ) PhiQ) (τ : ℍ) :
    (aeval (j τ)) (diagPhiQ PhiQ) = ∏ i : Option (ZMod m), (j τ - f m i τ) := by
  rw [diagQ_aeval_eq, ← hPhiQ τ, orbitPoly_eval_eq_prod]

/-! ## (C2, input) The CM coset relation `∃ i, f m i τ₁₆₃ = j τ₁₆₃`

The CM matrix `M_n = [[n+1, −41],[1, n]]` fixes `τ₁₆₃`; it decomposes as `γ · Acol m n` with
`γ = [[n+1, −1],[1, 0]] ∈ SL(2,ℤ)`, so `j (Acol m n • τ₁₆₃) = j τ₁₆₃`. -/

variable {m : ℕ}

/-- The CM matrix `M_n = [[n+1, −41],[1, n]]` as an element of `GL (Fin 2) ℝ` (determinant
`n² + n + 41 > 0`). -/
def cmGL (n : ℤ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(n : ℝ) + 1, -41; 1, (n : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    nlinarith [sq_nonneg (2 * (n : ℝ) + 1)])

@[simp] lemma val_cmGL (n : ℤ) :
    (cmGL n).val = !![(n : ℝ) + 1, -41; 1, (n : ℝ)] := rfl

lemma cmGL_det_pos (n : ℤ) : 0 < (cmGL n).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_cmGL, Matrix.det_fin_two_of]
  nlinarith [sq_nonneg (2 * (n : ℝ) + 1)]

/-- **`M_n` fixes `τ₁₆₃`** as a Möbius transformation. -/
lemma cmGL_smul_eq (n : ℤ) : cmGL n • τ₁₆₃ = τ₁₆₃ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (cmGL_det_pos n), div_eq_iff (denom_ne_zero (cmGL n) τ₁₆₃)]
  have hfix := cmMatrix_fixes n
  simp only [QF.Fixes] at hfix
  simp only [num, denom, val_cmGL, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  push_cast at hfix
  linear_combination hfix

/-- The `SL(2,ℤ)` cofactor `γ = [[n+1, −1],[1, 0]]` (determinant `1`). -/
def cmGamma (n : ℤ) : SL(2, ℤ) :=
  ⟨!![n + 1, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

/-- **Coset decomposition** `M_n = γ · Acol m n` (as `GL (Fin 2) ℝ`), valid when
`m = n² + n + 41`. -/
lemma cmGL_factor (n : ℤ) [NeZero m] (hm : (m : ℤ) = n ^ 2 + n + 41) :
    cmGL n = (cmGamma n : GL (Fin 2) ℝ) * Acol m n := by
  have hmR : (m : ℝ) = (n : ℝ) ^ 2 + (n : ℝ) + 41 := by exact_mod_cast hm
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  fin_cases a <;> fin_cases c <;>
    simp [val_cmGL, val_Acol, cmGamma, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [hmR]

/-- **The `b`-coset value at `τ₁₆₃`.** `j (Acol m n • τ₁₆₃) = j τ₁₆₃`. -/
lemma cm_coset_val (n : ℤ) [NeZero m] (hm : (m : ℤ) = n ^ 2 + n + 41) :
    j (Acol m n • τ₁₆₃) = j τ₁₆₃ := by
  have htransfer : j (cmGL n • τ₁₆₃) = j (Acol m n • τ₁₆₃) :=
    j_matrix_transfer (cmGamma n) (cmGL n) (Acol m n) τ₁₆₃ (cmGL_factor n hm)
  rw [cmGL_smul_eq] at htransfer
  exact htransfer.symm

/-- **(C2, input): the CM coset relation.** For `m = n² + n + 41`, some coset value coincides
with `j τ₁₆₃`: `f m (some (n : ZMod m)) τ₁₆₃ = j τ₁₆₃`. -/
lemma cm_coset_rel (n : ℤ) [NeZero m] (hm : (m : ℤ) = n ^ 2 + n + 41) :
    ∃ i : Option (ZMod m), f m i τ₁₆₃ = j τ₁₆₃ := by
  refine ⟨some (n : ZMod m), ?_⟩
  rw [f_some]
  have hdvd : (m : ℤ) ∣ ((n : ZMod m).val : ℤ) - n := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [ZMod.natCast_val, ZMod.intCast_cast, ZMod.ringHom_map_cast]
    simp
  rw [j_Acol_smul_congr hdvd τ₁₆₃]
  exact cm_coset_val n hm

/-! ## (C4)/(C5) Form-theory helpers (binary quadratic forms of a CM point)

Added to the `Chudnovsky.QF` namespace of `QuadraticPoints.lean` / `FormReduction.lean`.
They provide: a fixing integer matrix of a point yields a definite integer form; two forms
with a common root are proportional; a primitive representative exists; and the mod-4
constraint `disc ≤ −3`. -/

namespace QF

/-- A binary quadratic form with `a ≠ 0` whose root lies in `ℍ` (a non-real number) has
negative discriminant. -/
lemma disc_neg_of_isRoot {F : BQF} {τ : ℍ} (ha : F.a ≠ 0) (h : IsRoot F τ) : disc F < 0 := by
  by_contra hcon
  push Not at hcon
  have hsq := sq_two_a_root h
  set s : ℝ := Real.sqrt (disc F) with hs
  have hsD : (s : ℂ) ^ 2 = (disc F : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hcon : (0:ℝ) ≤ (disc F : ℝ))]
    norm_cast
  have hfac :
      (2 * (F.a : ℂ) * (τ : ℂ) + (F.b : ℂ) - (s : ℂ)) *
        (2 * (F.a : ℂ) * (τ : ℂ) + (F.b : ℂ) + (s : ℂ)) = 0 := by
    have hz : (2 * (F.a : ℂ) * (τ : ℂ) + (F.b : ℂ)) ^ 2 - (s : ℂ) ^ 2 = 0 := by
      rw [hsq, hsD]; ring
    linear_combination hz
  have hcontr : ∀ β : ℝ, 2 * (F.a : ℂ) * (τ : ℂ) + (F.b : ℂ) + (β : ℂ) = 0 → False := by
    intro β hβ
    have hlin : ((2 * (F.a : ℝ) : ℝ) : ℂ) * (τ : ℂ) + (((F.b : ℝ) + β : ℝ) : ℂ) = 0 := by
      push_cast; linear_combination hβ
    obtain ⟨hα, _⟩ := real_lin_eq_zero τ hlin
    have : (F.a : ℝ) = 0 := by linarith
    exact ha (by exact_mod_cast this)
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact hcontr (-s) (by push_cast; linear_combination h1)
  · exact hcontr s h1

/-- Two forms with a common root `τ ∈ ℍ` are proportional: `F.a·G.b = G.a·F.b` and
`F.a·G.c = G.a·F.c`. -/
lemma root_prop {F G : BQF} {τ : ℍ} (hF : IsRoot F τ) (hG : IsRoot G τ) :
    F.a * G.b = G.a * F.b ∧ F.a * G.c = G.a * F.c := by
  have hlin :
      ((G.a * F.b - F.a * G.b : ℤ) : ℂ) * (τ : ℂ) + ((G.a * F.c - F.a * G.c : ℤ) : ℂ) = 0 := by
    simp only [IsRoot] at hF hG
    push_cast
    linear_combination (G.a : ℂ) * hF - (F.a : ℂ) * hG
  obtain ⟨h1, h2⟩ := int_lin_eq_zero τ hlin
  exact ⟨by linarith, by linarith⟩

/-- If `F` is primitive with a root `τ`, any form `G` with the same root is an integer
multiple of `F`. -/
lemma exists_int_mult {F G : BQF} {τ : ℍ} (hFp : IsPrimitive F) (hFa : F.a ≠ 0)
    (hF : IsRoot F τ) (hG : IsRoot G τ) :
    ∃ l : ℤ, G.a = l * F.a ∧ G.b = l * F.b ∧ G.c = l * F.c := by
  obtain ⟨hb, hc⟩ := root_prop hF hG
  obtain ⟨u, v, w, huvw⟩ := bezout_of_primitive hFp
  have e1 : (u * G.a + v * G.b + w * G.c) * F.a = G.a := by
    linear_combination v * hb + w * hc + G.a * huvw
  refine ⟨u * G.a + v * G.b + w * G.c, e1.symm, ?_, ?_⟩
  · have h : F.a * G.b = F.a * ((u * G.a + v * G.b + w * G.c) * F.b) := by
      linear_combination hb - F.b * e1
    exact mul_left_cancel₀ hFa h
  · have h : F.a * G.c = F.a * ((u * G.a + v * G.b + w * G.c) * F.c) := by
      linear_combination hc - F.c * e1
    exact mul_left_cancel₀ hFa h

/-- A positive-definite form has a primitive positive-definite representative with the same
root. -/
lemma exists_primitive_isRoot {F : BQF} {τ : ℍ} (hpd : IsPosDef F) (hroot : IsRoot F τ) :
    ∃ F₀ : BQF, IsPrimitive F₀ ∧ IsPosDef F₀ ∧ IsRoot F₀ τ := by
  have ha : F.a ≠ 0 := hpd.1.ne'
  set d : ℤ := (Int.gcd (Int.gcd F.a F.b) F.c : ℤ) with hd
  have hdc : d ∣ F.c := Int.gcd_dvd_right _ _
  have hdab : d ∣ (Int.gcd F.a F.b : ℤ) := Int.gcd_dvd_left _ _
  have hda : d ∣ F.a := hdab.trans (Int.gcd_dvd_left _ _)
  have hdb : d ∣ F.b := hdab.trans (Int.gcd_dvd_right _ _)
  have hdpos : 0 < d := by
    rcases (Int.natCast_nonneg (Int.gcd (Int.gcd F.a F.b) F.c)).lt_or_eq with h | h
    · exact h
    · exfalso; apply ha
      have hd0 : d = 0 := h.symm
      rw [hd0] at hda
      exact zero_dvd_iff.mp hda
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  obtain ⟨a₀, ha0⟩ := hda
  obtain ⟨b₀, hb0⟩ := hdb
  obtain ⟨c₀, hc0⟩ := hdc
  refine ⟨⟨a₀, b₀, c₀⟩, ?_, ?_, ?_⟩
  · -- primitivity
    intro e hea heb hec
    have hEa : e * d ∣ F.a := by rw [ha0, mul_comm e d]; exact mul_dvd_mul_left d hea
    have hEb : e * d ∣ F.b := by rw [hb0, mul_comm e d]; exact mul_dvd_mul_left d heb
    have hEc : e * d ∣ F.c := by rw [hc0, mul_comm e d]; exact mul_dvd_mul_left d hec
    have hEdd : e * d ∣ d := by
      have hh := Int.dvd_coe_gcd (Int.dvd_coe_gcd hEa hEb) hEc
      rwa [← hd] at hh
    obtain ⟨k, hk⟩ := hEdd
    have hek : e * k = 1 := by
      have h2 : d * (e * k) = d * 1 := by rw [mul_one]; linear_combination -hk
      exact mul_left_cancel₀ hdpos.ne' h2
    exact isUnit_of_dvd_one ⟨k, hek.symm⟩
  · -- positive definite
    refine ⟨?_, ?_⟩
    · have h1 : 0 < d * a₀ := by rw [← ha0]; exact hpd.1
      exact (mul_pos_iff_of_pos_left hdpos).mp h1
    · have hdF : disc F = d ^ 2 * disc (⟨a₀, b₀, c₀⟩ : BQF) := by
        simp only [disc, ha0, hb0, hc0]; ring
      have hdneg := hpd.2
      rw [hdF] at hdneg
      nlinarith [hdneg, sq_nonneg d, hdpos]
  · -- root
    simp only [IsRoot] at hroot ⊢
    rw [ha0, hb0, hc0] at hroot
    apply mul_left_cancel₀ hdne
    rw [mul_zero]
    push_cast at hroot ⊢
    linear_combination hroot

/-- A positive-definite form has discriminant `≤ −3` (its discriminant is `≡ 0` or `1 mod 4`
and negative). -/
lemma disc_le_neg_three {F : BQF} (hpd : IsPosDef F) : disc F ≤ -3 := by
  have h1 : disc F < 0 := hpd.2
  have hexpand : disc F = F.b ^ 2 - 4 * (F.a * F.c) := by simp only [disc]; ring
  have h4 : F.b ^ 2 % 4 = 0 ∨ F.b ^ 2 % 4 = 1 := by
    rcases Int.even_or_odd F.b with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; rw [hk]; have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
      rw [this]; omega
    · right; rw [hk]; have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
      rw [this]; omega
  omega

end QF

/-! ## (C4) From a coset coincidence to a fixing integer matrix and a definite form -/

/-- **Fixing matrix from a coset factorization.** If `γ ∈ SL(2,ℤ)` sends the coset point `Aτ`
(with `Aτ = (e·τ' + f)/g`) to `τ'`, then the integer matrix `γ · [[e,f],[0,g]]` fixes `τ'`;
its entries give a `QF.Fixes` relation of determinant `e·g`. -/
lemma fixes_of_coset {e f g : ℤ} (γ : SL(2, ℤ)) {Aτ τ' : ℍ}
    (hW : (Aτ : ℂ) = ((e : ℂ) * (τ' : ℂ) + (f : ℂ)) / (g : ℂ)) (hg : (g : ℂ) ≠ 0)
    (hfix : γ • Aτ = τ') :
    ∃ p q r s : ℤ, QF.Fixes p q r s τ' ∧ p * s - q * r = e * g := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (A := γ)
    rwa [Matrix.det_fin_two] at h
  refine ⟨γ 0 0 * e, γ 0 0 * f + γ 0 1 * g, γ 1 0 * e, γ 1 0 * f + γ 1 1 * g, ?_, ?_⟩
  · have hco := coe_specialLinearGroup_apply γ Aτ
    rw [hfix] at hco
    have hden : (algebraMap ℤ ℝ (γ 1 0) : ℂ) * (Aτ : ℂ) + (algebraMap ℤ ℝ (γ 1 1) : ℂ) ≠ 0 := by
      intro h0
      simp only [eq_intCast] at h0
      push_cast at h0
      obtain ⟨hc0, hd0⟩ := QF.int_lin_eq_zero Aτ h0
      rw [hc0, hd0] at hdet; simp at hdet
    rw [eq_div_iff hden, hW] at hco
    simp only [eq_intCast] at hco
    simp only [QF.Fixes]
    push_cast at hco ⊢
    field_simp at hco
    linear_combination -hco
  · linear_combination (e * g) * hdet

/-- **(C4).** A coset coincidence `f m i τ′ = j τ′` yields integers `p q r s` with a
`QF.Fixes` relation of determinant `m`. -/
lemma exists_fixes_of_coincidence [Fact m.Prime] {τ' : ℍ} {i : Option (ZMod m)}
    (h : f m i τ' = j τ') :
    ∃ p q r s : ℤ, QF.Fixes p q r s τ' ∧ p * s - q * r = (m : ℤ) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hmpos : 0 < m := (Fact.out : m.Prime).pos
  cases i with
  | none =>
    have hj : j (AInf m • τ') = j τ' := by rw [← f_none]; exact h
    obtain ⟨γ, hγ⟩ := j_injective_mod_Γ hj
    obtain ⟨p, q, r, s, hfix, hdet⟩ :=
      fixes_of_coset (e := (m : ℤ)) (f := 0) (g := 1) γ
        (by rw [coe_AInf_smul]; push_cast; ring) (by norm_num) hγ.symm
    exact ⟨p, q, r, s, hfix, by rw [hdet]; ring⟩
  | some b =>
    have hj : j (Acol m (b.val : ℤ) • τ') = j τ' := by rw [← f_some]; exact h
    obtain ⟨γ, hγ⟩ := j_injective_mod_Γ hj
    obtain ⟨p, q, r, s, hfix, hdet⟩ :=
      fixes_of_coset (e := 1) (f := (b.val : ℤ)) (g := (m : ℤ)) γ
        (by rw [coe_Acol_smul]; push_cast; ring) (by exact_mod_cast hmpos.ne') hγ.symm
    exact ⟨p, q, r, s, hfix, by rw [hdet]; ring⟩

/-- **(C4), packaged.** A coset coincidence at `τ′` produces a positive-definite integer form
rooted at `τ′` of discriminant `t² − 4m`. -/
lemma exists_form_of_coincidence [Fact m.Prime] {τ' : ℍ} {i : Option (ZMod m)}
    (h : f m i τ' = j τ') :
    ∃ (F : QF.BQF) (t : ℤ), QF.IsPosDef F ∧ QF.IsRoot F τ' ∧ QF.disc F = t ^ 2 - 4 * (m : ℤ) := by
  obtain ⟨p, q, r, s, hfix, hdet⟩ := exists_fixes_of_coincidence h
  have hprime : Nat.Prime m := Fact.out
  -- `r ≠ 0`: else the matrix is scalar and `m` a perfect square.
  have hr0 : r ≠ 0 := by
    intro hr
    have hAf : (p : ℂ) * (τ' : ℂ) + (q : ℂ) = (τ' : ℂ) * ((s : ℂ)) := by
      simp only [QF.Fixes, hr] at hfix; linear_combination hfix
    have hlin : ((p - s : ℤ) : ℂ) * (τ' : ℂ) + ((q : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination hAf
    obtain ⟨hps, hq⟩ := QF.int_lin_eq_zero τ' hlin
    have hpeqs : p = s := by linarith
    have hsq : s * s = (m : ℤ) := by
      rw [hpeqs, hq, hr] at hdet; simpa using hdet
    have hnat : s.natAbs * s.natAbs = m := by
      have h1 : (↑(s.natAbs * s.natAbs) : ℤ) = (m : ℤ) := by rw [Int.natAbs_mul_self]; exact hsq
      exact_mod_cast h1
    have hdvd : s.natAbs ∣ m := ⟨s.natAbs, hnat.symm⟩
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with hh | hh
    · rw [hh] at hnat; have := hprime.two_le; omega
    · rw [hh] at hnat; nlinarith [hprime.two_le]
  -- the fixing form `(r, s−p, −q)`
  have hroot0 : QF.IsRoot ⟨r, s - p, -q⟩ τ' := by
    simp only [QF.IsRoot, QF.Fixes] at hfix ⊢; push_cast
    linear_combination -hfix
  have hdisc0 : QF.disc (⟨r, s - p, -q⟩ : QF.BQF) = (p + s) ^ 2 - 4 * (m : ℤ) := by
    simp only [QF.disc]; rw [← hdet]; ring
  have hnegd : QF.disc (⟨r, s - p, -q⟩ : QF.BQF) < 0 := QF.disc_neg_of_isRoot hr0 hroot0
  rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
  · -- negate the form so the leading coefficient is positive
    refine ⟨⟨-r, -(s - p), q⟩, p + s, ⟨by simpa using neg_pos.mpr hrneg, ?_⟩, ?_, ?_⟩
    · show QF.disc (⟨-r, -(s - p), q⟩ : QF.BQF) < 0
      have : QF.disc (⟨-r, -(s - p), q⟩ : QF.BQF) = QF.disc (⟨r, s - p, -q⟩ : QF.BQF) := by
        simp only [QF.disc]; ring
      rw [this]; exact hnegd
    · simp only [QF.IsRoot] at hroot0 ⊢; push_cast; push_cast at hroot0; linear_combination -hroot0
    · show QF.disc (⟨-r, -(s - p), q⟩ : QF.BQF) = (p + s) ^ 2 - 4 * (m : ℤ)
      have : QF.disc (⟨-r, -(s - p), q⟩ : QF.BQF) = QF.disc (⟨r, s - p, -q⟩ : QF.BQF) := by
        simp only [QF.disc]; ring
      rw [this]; exact hdisc0
  · exact ⟨⟨r, s - p, -q⟩, p + s, ⟨hrpos, hnegd⟩, hroot0, hdisc0⟩

/-! ## (C5)/(C6) The three-prime bridge: `τ′` is `Γ`-equivalent to `τ₁₆₃` -/

/-- **(C5)+(C6).** If `τ′` carries a coset coincidence for each of `m ∈ {41, 43, 61}`, then
`τ′` is `SL(2,ℤ)`-equivalent to `τ₁₆₃`. -/
theorem cm_bridge {τ' : ℍ}
    (h41 : ∃ i : Option (ZMod 41), f 41 i τ' = j τ')
    (h43 : ∃ i : Option (ZMod 43), f 43 i τ' = j τ')
    (h61 : ∃ i : Option (ZMod 61), f 61 i τ' = j τ') :
    ∃ M : SL(2, ℤ), M • τ' = τ₁₆₃ := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  obtain ⟨i41, hi41⟩ := h41
  obtain ⟨i43, hi43⟩ := h43
  obtain ⟨i61, hi61⟩ := h61
  obtain ⟨F41, t1, hpd41, hr41, hdsc41⟩ := exists_form_of_coincidence (m := 41) hi41
  obtain ⟨F43, t2, hpd43, hr43, hdsc43⟩ := exists_form_of_coincidence (m := 43) hi43
  obtain ⟨F61, t3, hpd61, hr61, hdsc61⟩ := exists_form_of_coincidence (m := 61) hi61
  obtain ⟨F₀, hprim, hpd0, hr0⟩ := QF.exists_primitive_isRoot hpd41 hr41
  obtain ⟨l1, hl1a, hl1b, hl1c⟩ := QF.exists_int_mult hprim hpd0.1.ne' hr0 hr41
  obtain ⟨l2, hl2a, hl2b, hl2c⟩ := QF.exists_int_mult hprim hpd0.1.ne' hr0 hr43
  obtain ⟨l3, hl3a, hl3b, hl3c⟩ := QF.exists_int_mult hprim hpd0.1.ne' hr0 hr61
  have hs1 : QF.disc F41 = l1 ^ 2 * QF.disc F₀ := by
    simp only [QF.disc, hl1a, hl1b, hl1c]; ring
  have hs2 : QF.disc F43 = l2 ^ 2 * QF.disc F₀ := by
    simp only [QF.disc, hl2a, hl2b, hl2c]; ring
  have hs3 : QF.disc F61 = l3 ^ 2 * QF.disc F₀ := by
    simp only [QF.disc, hl3a, hl3b, hl3c]; ring
  have h1 : t1 ^ 2 - 4 * 41 = QF.disc F₀ * l1 ^ 2 := by
    have h := hs1.symm.trans hdsc41; push_cast at h ⊢; linear_combination -h
  have h2 : t2 ^ 2 - 4 * 43 = QF.disc F₀ * l2 ^ 2 := by
    have h := hs2.symm.trans hdsc43; push_cast at h ⊢; linear_combination -h
  have h3 : t3 ^ 2 - 4 * 61 = QF.disc F₀ * l3 ^ 2 := by
    have h := hs3.symm.trans hdsc61; push_cast at h ⊢; linear_combination -h
  have hl1ne : l1 ≠ 0 := by
    intro hl; rw [hl, zero_mul] at hl1a; exact hpd41.1.ne' hl1a
  have hl2ne : l2 ≠ 0 := by
    intro hl; rw [hl, zero_mul] at hl2a; exact hpd43.1.ne' hl2a
  have hl3ne : l3 ≠ 0 := by
    intro hl; rw [hl, zero_mul] at hl3a; exact hpd61.1.ne' hl3a
  have hD3 : QF.disc F₀ ≤ -3 := QF.disc_le_neg_three hpd0
  have hD0 : QF.disc F₀ = -163 :=
    QF.disc_of_three_relations hD3 hl1ne hl2ne hl3ne h1 h2 h3
  exact QF.cm_disc_neg163_smul_eq_τ₁₆₃ hpd0 hD0 hr0

/-! ## (C1)–(C3) Vanishing of `Φ_m(x, x)` at roots, and the coincidence at `τ′` -/

/-- **(C2)+(C3).** For a root `x` of `minpoly ℚ j₀` and `τ′` with `j τ′ = x`, each prime
`m = n² + n + 41` yields a coset coincidence `f m i τ′ = j τ′`. -/
lemma phi_coincidence (n : ℤ) (mm : ℕ) [NeZero mm] [Fact mm.Prime] (hm : (mm : ℤ) = n ^ 2 + n + 41)
    {x : ℂ} (hx : (aeval x) (minpoly ℚ (j τ₁₆₃)) = 0)
    {τ' : ℍ} (hτ' : j τ' = x) : ∃ i : Option (ZMod mm), f mm i τ' = j τ' := by
  obtain ⟨PhiQ, hPhiQ⟩ := exists_PhiQ_closed (m := mm)
  have hG0 : (aeval (j τ₁₆₃)) (diagPhiQ PhiQ) = 0 := by
    rw [diagQ_eval_eq_prod hPhiQ]
    obtain ⟨i, hi⟩ := cm_coset_rel n hm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, sub_self])
  obtain ⟨k, hk⟩ := minpoly.dvd ℚ (j τ₁₆₃) hG0
  have hGx : (aeval x) (diagPhiQ PhiQ) = 0 := by rw [hk, map_mul, hx, zero_mul]
  rw [← hτ', diagQ_eval_eq_prod hPhiQ] at hGx
  obtain ⟨i, _, hi0⟩ := Finset.prod_eq_zero_iff.mp hGx
  exact ⟨i, (sub_eq_zero.mp hi0).symm⟩

/-! ## (C7) Rationality of `j τ₁₆₃` -/

/-- **The three-prime argument (§4.2).** Assuming surjectivity of `j` and integrality of
`j τ₁₆₃`, the value `j τ₁₆₃` is rational. -/
theorem j_τ₁₆₃_rational_of (hsurj : Function.Surjective (j : ℍ → ℂ))
    (hint : IsIntegral ℤ (j τ₁₆₃)) : ∃ r : ℚ, j τ₁₆₃ = (r : ℂ) := by
  haveI : NeZero (41 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero (43 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero (61 : ℕ) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  set j₀ : ℂ := j τ₁₆₃ with hj0
  -- `j₀` is integral (hence algebraic) over `ℚ`.
  have hintQ : IsIntegral ℚ j₀ := by
    obtain ⟨P, hPm, hPe⟩ := hint
    refine ⟨P.map (algebraMap ℤ ℚ), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ ℂ]
    exact hPe
  -- Every complex root of `minpoly ℚ j₀` equals `j₀`.
  have hallroots : ∀ x : ℂ, (aeval x) (minpoly ℚ j₀) = 0 → x = j₀ := by
    intro x hx
    obtain ⟨τ', hτ'⟩ := hsurj x
    have h41 := phi_coincidence 0 41 (by norm_num) hx hτ'
    have h43 := phi_coincidence 1 43 (by norm_num) hx hτ'
    have h61 := phi_coincidence 4 61 (by norm_num) hx hτ'
    obtain ⟨M, hM⟩ := cm_bridge h41 h43 h61
    rw [← hτ', hj0, ← hM, j_smul]
  -- Finish: all roots equal `j₀`, so `j₀` is rational (Vieta on the subleading coefficient).
  set p : Polynomial ℚ := minpoly ℚ j₀ with hp
  have hpmonic : p.Monic := minpoly.monic hintQ
  have hdpos : 0 < p.natDegree := minpoly.natDegree_pos hintQ
  set φ : ℚ →+* ℂ := algebraMap ℚ ℂ with hφ
  set pC : Polynomial ℂ := p.map φ with hpC
  have hpCmonic : pC.Monic := hpmonic.map _
  have hsplit := IsAlgClosed.splits pC
  have hCdeg : pC.natDegree = p.natDegree := hpmonic.natDegree_map φ
  -- all roots of `pC` equal `j₀`
  have hrootval : ∀ z ∈ pC.roots, z = j₀ := by
    intro z hz
    have hz0 : pC.eval z = 0 := (Polynomial.mem_roots (hpCmonic.ne_zero)).mp hz
    have : (aeval z) p = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hz0
    exact hallroots z this
  -- the root multiset is `replicate d j₀`
  have hcard : Multiset.card pC.roots = pC.natDegree :=
    (Splits.natDegree_eq_card_roots hsplit).symm
  have hrepl : pC.roots = Multiset.replicate pC.natDegree j₀ :=
    Multiset.eq_replicate.mpr ⟨hcard, hrootval⟩
  -- `nextCoeff pC = -(d • j₀) = φ(nextCoeff p)`
  have hnc1 : pC.nextCoeff = -(pC.roots.sum) :=
    hsplit.nextCoeff_eq_neg_sum_roots_of_monic hpCmonic
  have hnc2 : pC.nextCoeff = φ p.nextCoeff := Polynomial.nextCoeff_map_eq p φ
  rw [hrepl, Multiset.sum_replicate, hCdeg] at hnc1
  -- combine: `φ(nextCoeff p) = -(d • j₀)`
  have hkey : φ p.nextCoeff = -((p.natDegree : ℂ) * j₀) := by
    rw [← hnc2, hnc1, nsmul_eq_mul]
  -- solve for `j₀`
  refine ⟨-p.nextCoeff / (p.natDegree : ℚ), ?_⟩
  have hdQ : (p.natDegree : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have : φ (-p.nextCoeff / (p.natDegree : ℚ)) = j₀ := by
    rw [map_div₀, map_neg, hkey, hφ]
    rw [map_natCast]
    have hdC : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    field_simp
  rw [← this, eq_ratCast φ (-p.nextCoeff / (p.natDegree : ℚ))]

end Chudnovsky
