/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.JFunction

/-!
# The `m`-isogeny coset orbit of `j` (Phase C, chunk B2)

Second file of Track 1 of Phase C (see `Playground/Pi/PhaseC-PLAN.md`, §3.1 sub-lemma
`(B2)` and §6.5 decision point 2). For a **prime** `m` (kept generic; the project
instantiates `m ∈ {41, 43, 61, 163}` later) this file builds the degree-`m` isogeny orbit
of the `j`-invariant: the `m + 1` functions

* `f_∞(τ) = j (m·τ)` — from the Hermite-normal-form matrix `[[m,0],[0,1]]`;
* `f_b(τ) = j ((τ + b)/m)` for `b = 0, …, m-1` — from the matrices `[[1,b],[0,m]]`.

indexed by `Option (ZMod m)` (`none ↦ f_∞`, `some b ↦ f_b`). The point maps are realized
through Mathlib's `GL (Fin 2) ℝ`-action on `ℍ` (`UpperHalfPlane.MoebiusAction`), the choice
recommended by the plan's trap list ("pick one action early and stick to it").

The `(B2)` deliverables:

* `f` : the `m + 1` orbit functions, and `mdifferentiable_f` : each is holomorphic on `ℍ`;
* `f_some_congr` : well-definedness mod `m` (the `some`-index really lives on `ZMod m`);
* **`T`-permutation** `f_T_smul`: `f i (T • τ) = f (σ_T i) τ` with `σ_T` the rotation
  `none ↦ none`, `some b ↦ some (b + 1)`;
* **`S`-permutation** `f_S_smul`: `f i (S • τ) = f (σ_S i) τ` with `σ_S` the involution
  `none ↔ some 0`, `some b ↦ some (-b⁻¹)` (`b ≠ 0`; needs `m` prime for the field inverse);
* the master statement `f_SL_perm` : the multiset `{f i τ}` is permuted by every `S`/`T`
  generator (hence `SL(2,ℤ)`-invariant), packaged as the pair of permutation lemmas.

## q-expansions in the base variable `w = exp(2πiτ/m)` (decision point 2)

Rather than Puiseux series in `q^{1/m}`, we follow the clean formulation flagged in the
plan brief: introduce the honest holomorphic function `w = wParam m τ = exp(2πiτ/m)` (a
genuine power series variable, **no root-taking**) and the constant `ζ = zetaM m = exp(2πi/m)`.
The nome factorizes on each coset point:

* `q_Acol_smul` : `q ((τ+b)/m) = ζ^b · w`;
* `q_AInf_smul` : `q (m·τ) = w^{m²}`,

so composing `JFunction`'s integer expansion `hasSum_j_mul_q` gives, for every `τ`,

* `hasSum_f_some` : `HasSum (fun n ↦ c n · (ζ^b·w)^n) (f (some b) τ · ζ^b·w)`;
* `hasSum_f_none` : `HasSum (fun n ↦ c n · (w^{m²})^n) (f none τ · w^{m²})`,

with `c n = jqInt.coeff n ∈ ℤ` the integer `j`-coefficients. The `b`-dependence is exactly
`ζ^{bn}`, which is what powers the root-of-unity averaging of `ModularPolynomialQ.lean`'s
`(B3)`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm
open scoped Real Manifold MatrixGroups

variable {m : ℕ}

/-! ## The coset matrices and their action on `ℍ` -/

/-- The Hermite-normal-form matrix `[[m,0],[0,1]]` of determinant `m`, as an element of
`GL (Fin 2) ℝ`; its Möbius action is `τ ↦ m·τ`. -/
def AInf (m : ℕ) [NeZero m] : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(m : ℝ), 0; 0, 1] (by
    simp [Matrix.det_fin_two_of, Nat.cast_ne_zero.mpr (NeZero.ne m)])

/-- The Hermite-normal-form matrix `[[1,b],[0,m]]` of determinant `m`, as an element of
`GL (Fin 2) ℝ`; its Möbius action is `τ ↦ (τ + b)/m`. -/
def Acol (m : ℕ) [NeZero m] (b : ℤ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![1, (b : ℝ); 0, (m : ℝ)] (by
    simp [Matrix.det_fin_two_of, Nat.cast_ne_zero.mpr (NeZero.ne m)])

@[simp] lemma val_AInf [NeZero m] : (AInf m).val = !![(m : ℝ), 0; 0, 1] := rfl

@[simp] lemma val_Acol [NeZero m] (b : ℤ) : (Acol m b).val = !![1, (b : ℝ); 0, (m : ℝ)] := rfl

lemma det_AInf_pos [NeZero m] : 0 < (AInf m).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_AInf, Matrix.det_fin_two_of]
  simpa using (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)) : (0 : ℝ) < m)

lemma det_Acol_pos [NeZero m] (b : ℤ) : 0 < (Acol m b).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_Acol, Matrix.det_fin_two_of]
  simpa using (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)) : (0 : ℝ) < m)

/-- The `∞`-coset point: `AInf m • τ = m·τ`. -/
lemma coe_AInf_smul [NeZero m] (τ : ℍ) : (↑(AInf m • τ) : ℂ) = m * τ := by
  rw [coe_smul_of_det_pos det_AInf_pos τ, num, denom, val_AInf]
  simp

/-- The `b`-coset point: `Acol m b • τ = (τ + b)/m`. -/
lemma coe_Acol_smul [NeZero m] (b : ℤ) (τ : ℍ) :
    (↑(Acol m b • τ) : ℂ) = (↑τ + b) / m := by
  rw [coe_smul_of_det_pos (det_Acol_pos b) τ, num, denom, val_Acol]
  simp

/-! ## The orbit functions and holomorphy -/

/-- The `m + 1` coset-orbit functions: `f none τ = j (m·τ)` and `f (some b) τ = j ((τ+b)/m)`.
Indexed by `Option (ZMod m)`. -/
def f (m : ℕ) [NeZero m] : Option (ZMod m) → ℍ → ℂ
  | none, τ => j (AInf m • τ)
  | some b, τ => j (Acol m b.val • τ)

@[simp] lemma f_none [NeZero m] (τ : ℍ) : f m none τ = j (AInf m • τ) := rfl

@[simp] lemma f_some [NeZero m] (b : ZMod m) (τ : ℍ) :
    f m (some b) τ = j (Acol m b.val • τ) := rfl

/-- Each orbit function is holomorphic on `ℍ`. -/
lemma mdifferentiable_f [NeZero m] (i : Option (ZMod m)) : MDiff (f m i) := by
  cases i with
  | none => exact mdifferentiable_j.comp (mdifferentiable_smul det_AInf_pos)
  | some b => exact mdifferentiable_j.comp (mdifferentiable_smul (det_Acol_pos b.val))

/-! ## `j` under integer translation and well-definedness of the `b`-cosets mod `m` -/

/-- `j` is invariant under translation by any integer: `j (n +ᵥ τ) = j τ`. -/
lemma j_vadd_int (n : ℤ) (τ : ℍ) : j ((n : ℝ) +ᵥ τ) = j τ := by
  rw [← modular_T_zpow_smul, j_smul]

/-- The `b`-coset function depends only on `b mod m`: if `m ∣ a' - a` then
`j ((τ+a')/m) = j ((τ+a)/m)` (adding `m` to the offset shifts the point by an integer,
which `j` absorbs). -/
lemma j_Acol_smul_congr [NeZero m] {a a' : ℤ} (h : (m : ℤ) ∣ a' - a) (τ : ℍ) :
    j (Acol m a' • τ) = j (Acol m a • τ) := by
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hpt : Acol m a' • τ = (k : ℝ) +ᵥ (Acol m a • τ) := by
    apply UpperHalfPlane.ext
    rw [coe_Acol_smul, UpperHalfPlane.coe_vadd, coe_Acol_smul]
    have hc : (a' : ℂ) = a + m * k := by
      have : a' = a + (m : ℤ) * k := by omega
      exact_mod_cast this
    rw [hc]; push_cast; field_simp; ring
  rw [hpt, j_vadd_int]

/-- `((b.val : ℤ) + c)` reduces to `b + c` in `ZMod m`, giving the divisibility feeding
`j_Acol_smul_congr`. -/
private lemma dvd_val_add [NeZero m] (b : ZMod m) (c : ℤ) :
    (m : ℤ) ∣ ((b.val : ℤ) + c) - ((b + (c : ZMod m)).val : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [ZMod.natCast_val, ZMod.intCast_cast, ZMod.ringHom_map_cast]
  simp

/-! ## The `T`-permutation

`T • τ = τ + 1` cyclically permutes the `b`-cosets (`b ↦ b + 1`) and fixes `f_∞`. -/

/-- The permutation of the orbit induced by `T`: rotation `some b ↦ some (b+1)`, `none` fixed. -/
def σT (m : ℕ) : Equiv.Perm (Option (ZMod m)) := Equiv.optionCongr (Equiv.addRight (1 : ZMod m))

@[simp] lemma σT_none : σT m none = none := rfl
@[simp] lemma σT_some (b : ZMod m) : σT m (some b) = some (b + 1) := rfl

/-- **`T`-permutation**: `f i (T • τ) = f (σT i) τ`, i.e. `f i (τ + 1) = f (σT i) τ`. -/
lemma f_T_smul [NeZero m] (i : Option (ZMod m)) (τ : ℍ) :
    f m i ((1 : ℝ) +ᵥ τ) = f m (σT m i) τ := by
  cases i with
  | none =>
    simp only [f_none, σT_none]
    have hpt : AInf m • ((1 : ℝ) +ᵥ τ) = (m : ℝ) +ᵥ (AInf m • τ) := by
      apply UpperHalfPlane.ext
      simp only [coe_AInf_smul, UpperHalfPlane.coe_vadd]
      push_cast; ring
    rw [hpt]
    simpa using j_vadd_int (m : ℤ) (AInf m • τ)
  | some b =>
    simp only [f_some, σT_some]
    -- first move the `+1` inside the coset offset: point equality
    have hpt : Acol m b.val • ((1 : ℝ) +ᵥ τ) = Acol m (b.val + 1) • τ := by
      apply UpperHalfPlane.ext
      simp only [coe_Acol_smul, UpperHalfPlane.coe_vadd]
      push_cast; ring
    rw [hpt]
    -- then reduce `(b.val + 1)` to `(b+1).val` mod m
    exact j_Acol_smul_congr (by simpa using dvd_val_add b 1) τ

/-! ## The `S`-permutation

`S • τ = -1/τ`. The key transfer lemma: if the `GL`-matrix `A` factors as `↑γ * B` with
`γ ∈ SL(2,ℤ)`, then `j (A • τ) = j (B • τ)` (the `SL(2,ℤ)`-factor is absorbed by
`j_smul`). All `S`-orbit identities are instances of a single matrix identity
`coset i · S = γ' · coset (σS i)`. -/

/-- Absorb an `SL(2,ℤ)` left factor of a `GL`-matrix into `j`-invariance. -/
lemma j_matrix_transfer (γ : SL(2, ℤ)) (A B : GL (Fin 2) ℝ) (τ : ℍ)
    (h : A = (γ : GL (Fin 2) ℝ) * B) : j (A • τ) = j (B • τ) := by
  rw [h, mul_smul, ← ModularGroup.sl_moeb]
  exact j_smul γ (B • τ)

/-- Rewrite `f i (S • τ)` as `j` of a single `GL`-matrix acting on `τ` (`coset i · S`). -/
private lemma j_smul_S_mul (A : GL (Fin 2) ℝ) (τ : ℍ) :
    j (A • (ModularGroup.S • τ)) = j ((A * (ModularGroup.S : GL (Fin 2) ℝ)) • τ) := by
  rw [ModularGroup.sl_moeb, mul_smul]

/-- The permutation of the orbit induced by `S`: the involution swapping `none ↔ some 0` and
sending `some b ↦ some (-b⁻¹)` for `b ≠ 0` (needs `m` prime for the field inverse). -/
def sSfun (m : ℕ) [Fact m.Prime] : Option (ZMod m) → Option (ZMod m)
  | none => some 0
  | some b => if b = 0 then none else some (-b⁻¹)

lemma sSfun_involutive [Fact m.Prime] : Function.Involutive (sSfun m) := by
  intro i
  cases i with
  | none => simp [sSfun]
  | some b =>
    by_cases hb : b = 0
    · simp [sSfun, hb]
    · have hb' : -b⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hb)
      simp [sSfun, hb, hb', inv_neg, inv_inv]

/-- The `S`-permutation as an `Equiv.Perm`. -/
def σS (m : ℕ) [Fact m.Prime] : Equiv.Perm (Option (ZMod m)) := sSfun_involutive.toPerm

@[simp] lemma σS_apply [Fact m.Prime] (i : Option (ZMod m)) : σS m i = sSfun m i := rfl

/-- **`S`-permutation**: `f i (S • τ) = f (σS i) τ`, i.e. `f i (-1/τ) = f (σS i) τ`.
This is what makes the elementary symmetric functions of the orbit `SL(2,ℤ)`-invariant. -/
lemma f_S_smul [Fact m.Prime] (i : Option (ZMod m)) (τ : ℍ) :
    f m i (ModularGroup.S • τ) = f m (σS m i) τ := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  cases i with
  | none =>
    have htarget : σS m none = some 0 := rfl
    rw [f_none, j_smul_S_mul, htarget, f_some]
    -- matrix identity  AInf · S = S · Acol 0
    refine j_matrix_transfer ModularGroup.S _ (Acol m ((0 : ZMod m).val)) τ ?_
    apply Matrix.GeneralLinearGroup.ext
    intro a c
    fin_cases a <;> fin_cases c <;>
      simp [val_AInf, val_Acol, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, ZMod.val_zero]
  | some b =>
    by_cases hb : b = 0
    · subst hb
      have htarget : σS m (some (0 : ZMod m)) = none := by simp [σS, sSfun]
      rw [f_some, j_smul_S_mul, htarget, f_none]
      -- matrix identity  Acol 0 · S = S · AInf
      refine j_matrix_transfer ModularGroup.S _ (AInf m) τ ?_
      apply Matrix.GeneralLinearGroup.ext
      intro a c
      fin_cases a <;> fin_cases c <;>
        simp [val_AInf, val_Acol, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, ZMod.val_zero]
    · have htarget : σS m (some b) = some (-b⁻¹) := by simp [σS, sSfun, hb]
      rw [f_some, j_smul_S_mul, htarget, f_some]
      -- integers  B = b.val,  B' = (-b⁻¹).val,  and the quotient q with  B·B' + 1 = m·q
      set B : ℤ := (b.val : ℤ) with hB
      set B' : ℤ := ((-b⁻¹).val : ℤ) with hB'
      obtain ⟨q, hq⟩ : (m : ℤ) ∣ B * B' + 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hB, hB']
        push_cast [ZMod.natCast_zmod_val]
        rw [mul_neg, mul_inv_cancel₀ hb]; ring
      -- the SL(2,ℤ) transfer matrix  γ' = [[B, -q],[m, -B']],  det = 1
      have hdet : Matrix.det !![B, -q; (m : ℤ), -B'] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination -hq
      set γ' : SL(2, ℤ) := ⟨!![B, -q; (m : ℤ), -B'], hdet⟩ with hγ'
      refine j_matrix_transfer γ' _ (Acol m B') τ ?_
      have hqR : (B : ℝ) * (B' : ℝ) - (q : ℝ) * (m : ℝ) = -1 := by
        have h : (B : ℝ) * B' + 1 = m * q := by exact_mod_cast hq
        linarith
      -- matrix identity  Acol B · S = γ' · Acol B'
      apply Matrix.GeneralLinearGroup.ext
      intro a c
      fin_cases a <;> fin_cases c <;>
        simp [val_Acol, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, hγ'] <;>
        linarith [hqR]

/-! ## q-expansions in the base variable `w = exp(2πiτ/m)`

The clean formulation of decision point 2: everything is a genuine power series in the
honest holomorphic function `w = wParam m τ = exp(2πiτ/m)` (no root-taking), with the
`m`-th root of unity `ζ = zetaM m = exp(2πi/m)`. The nome factorizes on each coset point,
and composing `JFunction`'s integer expansion `hasSum_j_mul_q` yields the coefficientwise
`HasSum` statements consumed by `ModularPolynomialQ.lean`'s `(B3)`. -/

/-- The base variable `w = exp(2πiτ/m)`: an honest holomorphic function of `τ`
(no `q^{1/m}`), with `w^m = q τ`. -/
def wParam (m : ℕ) (τ : ℍ) : ℂ := Complex.exp (2 * π * Complex.I * (τ : ℂ) / m)

/-- The `m`-th root of unity `ζ = exp(2πi/m)`. -/
def zetaM (m : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / m)

lemma wParam_ne_zero (τ : ℍ) : wParam m τ ≠ 0 := Complex.exp_ne_zero _

lemma zetaM_ne_zero : zetaM m ≠ 0 := Complex.exp_ne_zero _

/-- `w^m = q τ`: raising the base variable to the `m`-th power recovers the ordinary nome. -/
lemma wParam_pow_m [NeZero m] (τ : ℍ) : wParam m τ ^ m = q τ := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [wParam, q_eq, ← Complex.exp_nat_mul]
  congr 1
  field_simp

/-- `ζ^m = 1`. -/
lemma zetaM_pow_m [NeZero m] : zetaM m ^ m = 1 := by
  rw [zetaM, ← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) * (2 * π * Complex.I / m) = 2 * π * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- The nome on the `b`-coset point factorizes as `ζ^b · w`: `q ((τ+b)/m) = ζ^b · w`. -/
lemma q_Acol_smul [NeZero m] (b : ℤ) (τ : ℍ) :
    q (Acol m b • τ) = zetaM m ^ b * wParam m τ := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [q_eq, coe_Acol_smul, zetaM, wParam, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The nome on the `∞`-coset point is `w^{m²}`: `q (m·τ) = w^{m²}`. -/
lemma q_AInf_smul [NeZero m] (τ : ℍ) :
    q (AInf m • τ) = wParam m τ ^ (m ^ 2) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [q_eq, coe_AInf_smul, wParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- **q-expansion of the `b`-coset function** in `(ζ^b·w)`: the `HasSum` obtained from
`JFunction`'s integer `j`-expansion. The `b`-dependence is exactly `ζ^{b·n}` inside
`(ζ^b w)^n`, which powers the root-of-unity averaging of `(B3)`. -/
lemma hasSum_f_some [NeZero m] (b : ZMod m) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ)
        * (zetaM m ^ (b.val : ℤ) * wParam m τ) ^ n)
      (f m (some b) τ * (zetaM m ^ (b.val : ℤ) * wParam m τ)) := by
  have h := hasSum_j_mul_q (Acol m (b.val : ℤ) • τ)
  rw [q_Acol_smul] at h
  simpa only [f_some] using h

/-- **q-expansion of the `∞`-coset function** in `w^{m²}`. -/
lemma hasSum_f_none [NeZero m] (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ) * (wParam m τ ^ (m ^ 2)) ^ n)
      (f m none τ * wParam m τ ^ (m ^ 2)) := by
  have h := hasSum_j_mul_q (AInf m • τ)
  rw [q_AInf_smul] at h
  simpa only [f_none] using h

/-! ## Master statement: `SL(2,ℤ)`-invariance of the orbit's symmetric functions

Since `S` and `T` generate `SL(2,ℤ)`, the fact that both permute the multiset `{f i τ}`
(the `S`/`T`-permutation lemmas above) makes every symmetric function of the orbit
`SL(2,ℤ)`-invariant. We record the two consequences `ModularPolynomialQ.lean`'s `(B3)`/`(B4)`
consume directly: any product (e.g. `∏ (X - f i)`, the elementary symmetric generating
polynomial) and any sum (e.g. `∑ (f i)^k`, the power sums) of the orbit values is unchanged
by each generator. -/

/-- Any product over the orbit is `T`-invariant. -/
lemma prod_orbit_T_smul [NeZero m] {M : Type*} [CommMonoid M] (g : ℂ → M) (τ : ℍ) :
    ∏ i, g (f m i ((1 : ℝ) +ᵥ τ)) = ∏ i, g (f m i τ) := by
  simp_rw [f_T_smul]
  exact Equiv.prod_comp (σT m) (fun i ↦ g (f m i τ))

/-- Any sum over the orbit is `T`-invariant (e.g. the power sums `∑ (f i)^k`). -/
lemma sum_orbit_T_smul [NeZero m] {M : Type*} [AddCommMonoid M] (g : ℂ → M) (τ : ℍ) :
    ∑ i, g (f m i ((1 : ℝ) +ᵥ τ)) = ∑ i, g (f m i τ) := by
  simp_rw [f_T_smul]
  exact Equiv.sum_comp (σT m) (fun i ↦ g (f m i τ))

/-- Any product over the orbit is `S`-invariant. -/
lemma prod_orbit_S_smul [Fact m.Prime] {M : Type*} [CommMonoid M] (g : ℂ → M) (τ : ℍ) :
    ∏ i, g (f m i (ModularGroup.S • τ)) = ∏ i, g (f m i τ) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  simp_rw [f_S_smul]
  exact Equiv.prod_comp (σS m) (fun i ↦ g (f m i τ))

/-- Any sum over the orbit is `S`-invariant (e.g. the power sums `∑ (f i)^k`). -/
lemma sum_orbit_S_smul [Fact m.Prime] {M : Type*} [AddCommMonoid M] (g : ℂ → M) (τ : ℍ) :
    ∑ i, g (f m i (ModularGroup.S • τ)) = ∑ i, g (f m i τ) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  simp_rw [f_S_smul]
  exact Equiv.sum_comp (σS m) (fun i ↦ g (f m i τ))

end Chudnovsky
