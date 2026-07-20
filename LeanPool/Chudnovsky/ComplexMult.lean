/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.DivisionValues
import LeanPool.Chudnovsky.Fourier
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# Complex multiplication and the integrality of `E₂*` (Milla, Appendix B)

For a CM point `τ` with `A + Bτ + Cτ² = 0` (`A, B, C ∈ ℤ`, `gcd = 1`,
discriminant `D = B² − 4AC < 0`), the paper defines `κ·ω₂ := A·η₁ − C·τ·η₂` and proves
(PLAN B2):

* `lemkapa1` : `κ = −√D·(π²/(3ω₁²))·E₂*(τ)`  (via Legendre and `η₁ = π²E₂/3`);
* `lemkapa2` : `Cτ·κ = −∑_{v ∈ DIV(Cτ)} ℘(v)` (via the elliptic ζ-combination and
  `theowpsum`);
* `theoezweisternrest` : `√D·(E₂*(τ)/η(τ)⁴)·(AC)²` is an algebraic integer, where `η`
  is the Dedekind eta function (`1728·η²⁴ = E₄³ − E₆²`, Mathlib's `discriminant`).

Branch convention: for the root of `A + Bτ + Cτ² = 0` in `ℍ` we have
`√D = 2Cτ + B` (the paper's choice of `√D`); all statements below use `2Cτ + B`
in place of `√D`, which keeps them branch-free.

At `τ₁₆₃` : `41 − τ + τ² = 0`, i.e. `A = 41, B = −1, C = 1`, `D = −163`,
`√D = 2τ − 1 = i√163`, `AC = 41` — the specialization used in `Coefficients.lean`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm

open scoped Real

/-- Milla's `κ` (Def. `defkappa`), for the lattice `L_τ = ℤ + ℤτ` (so `ω₁ = 1`,
`ω₂ = τ`): `κ = (A·η₁ − C·τ·η₂)/τ`. -/
def kappa (τ : ℍ) (A C : ℤ) : ℂ :=
  ((A : ℂ) * (Lτ τ).eta₁ - (C : ℂ) * τ * (Lτ τ).eta₂) / τ

/-- Milla's `lemkapa1`: `κ = −√D·(π²/3)·E₂*(τ)` (with `ω₁ = 1` and `√D = 2Cτ + B`).
Uses the Legendre relation and `η₁ = π²E₂/3`. -/
theorem lemkapa1 {τ : ℍ} {A B C : ℤ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    kappa τ A C = -(2 * C * τ + B) * (π : ℂ) ^ 2 / 3 * E₂star τ := by
  -- Nonvanishing facts used to clear denominators.
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hyR : (τ.im : ℝ) ≠ 0 := τ.im_ne_zero
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyR
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- Imaginary part of the CM relation: `2C·Re τ + B = 0`.
  have him := (Complex.ext_iff.mp hCM).2
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.zero_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    pow_two, zero_mul, add_zero, zero_add] at him
  have hre2 : 2 * (C : ℝ) * τ.re + B = 0 := by
    have hfac : (τ.im : ℝ) * (2 * (C : ℝ) * τ.re + B) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h τ.im_ne_zero
    · exact h
  -- Hence `√D = 2Cτ + B = 2iC·Im τ` (pure imaginary, no case split on the branch).
  have hcoe : (τ : ℂ) = ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hre2C : 2 * (C : ℂ) * ((τ.re : ℝ) : ℂ) + (B : ℂ) = 0 := by exact_mod_cast hre2
  have hkey : 2 * (C : ℂ) * (τ : ℂ) + (B : ℂ) = 2 * (C : ℂ) * (τ.im : ℝ) * Complex.I := by
    rw [hcoe]; linear_combination hre2C
  -- Legendre and `η₁ = π²E₂/3`, rearranged for substitution.
  have hleg := legendre_Lτ τ
  have heta1 := eta₁_Lτ τ
  have hA : (A : ℂ) = -(B : ℂ) * τ - (C : ℂ) * (τ : ℂ) ^ 2 := by linear_combination hCM
  have hB : (B : ℂ) = 2 * (C : ℂ) * (τ.im : ℝ) * Complex.I - 2 * (C : ℂ) * (τ : ℂ) := by
    linear_combination hkey
  have he2 : (Lτ τ).eta₂ = (Lτ τ).eta₁ * (τ : ℂ) - 2 * (π : ℂ) * Complex.I := by
    linear_combination -hleg
  rw [kappa, E₂star, div_eq_iff hτ, hA, hB, he2, heta1]
  field_simp
  ring

/-- Intermediate step towards `theoezweisternrest` (Milla's final "product of algebraic
integers" step): `C·τbar` is an algebraic integer, being a root of the monic integer
polynomial `X² + B·X + AC`. Indeed `τbar = conj τ` satisfies the conjugate CM relation
`A + B·τbar + C·τbar² = 0` (the coefficients `A, B, C` are real), and multiplying by `C`
gives `(Cτbar)² + B·(Cτbar) + AC = 0`. -/
theorem isIntegral_C_mul_conj {τ : ℍ} {A B C : ℤ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    IsIntegral ℤ ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) := by
  have hconj : (A : ℂ) + B * (starRingEnd ℂ) (τ : ℂ) +
      C * ((starRingEnd ℂ) (τ : ℂ)) ^ 2 = 0 := by
    have := congrArg (starRingEnd ℂ) hCM
    simpa using this
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C B * Polynomial.X + Polynomial.C (A * C)), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add (Polynomial.degree_linear_le.trans_lt (by norm_num))
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    push_cast
    linear_combination (C : ℂ) * hconj

/-- Easy part of Milla's `satzezweistern`: `E₄/η⁸` is an algebraic integer whenever
`j = 1728·J` is (it is a root of `X³ − j`). -/
theorem isIntegral_E₄_div_eta_pow (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ)) :
    IsIntegral ℤ (E₄ τ / ModularForm.eta τ ^ 8) := by
  refine IsIntegral.of_pow (n := 3) (by norm_num) ?_
  have hΔ : ModularForm.discriminant τ = ModularForm.eta τ ^ 24 := rfl
  have hx : (E₄ τ / ModularForm.eta τ ^ 8) ^ 3 = 1728 * J τ := by
    rw [mul_J_eq, div_pow, show (ModularForm.eta τ ^ 8) ^ 3 = ModularForm.discriminant τ by
      rw [hΔ]; ring]
  rw [hx]; exact hj

/-- Easy part of Milla's `satzezweistern`: `E₆/η¹²` is an algebraic integer whenever
`j = 1728·J` is (it is a root of `X² − (j − 1728)`). -/
theorem isIntegral_E₆_div_eta_pow (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ)) :
    IsIntegral ℤ (E₆ τ / ModularForm.eta τ ^ 12) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  have hΔ : ModularForm.discriminant τ = ModularForm.eta τ ^ 24 := rfl
  have hne := discriminant_ne_zero τ
  have hrel := E₄_cube_sub_E₆_sq_eq_discriminant τ
  have h1728 : IsIntegral ℤ (1728 : ℂ) := by
    rw [show (1728 : ℂ) = algebraMap ℤ ℂ 1728 by simp]
    exact isIntegral_algebraMap
  have hx : (E₆ τ / ModularForm.eta τ ^ 12) ^ 2 = 1728 * J τ - 1728 := by
    rw [mul_J_eq, div_pow, show (ModularForm.eta τ ^ 12) ^ 2 = ModularForm.discriminant τ by
      rw [hΔ]; ring]
    field_simp
    linear_combination -hrel
  rw [hx]
  exact hj.sub h1728

/-! ## Rescaling to the lattice `L̂ = (π/√3)·η²·L_τ` and the final integrality

Milla's `proofzweistern` rescales `L_τ` to `L̂ = a·L_τ` with `a = (π/√3)·η(τ)²`, so that
`ω₁(L̂) = a`, `π²/(3ω₁(L̂)²) = 1/η⁴`, and `¼g₂(L̂) = 3E₄/η⁸`, `¼g₃(L̂) = 2E₆/η¹²` become
algebraic integers (given the integrality of `j = 1728J`).  The identity of
Prop. `lemkapppppa` applied to `L̂` then reads
`√D·(E₂*/η⁴)·(AC)² = (∑_{v ∈ DIV(Cτ)} AC·℘(v;L̂))·Cτbar`, whose right-hand side is a
product of algebraic integers (`theomwpu` with `m = AC`, plus `isIntegral_C_mul_conj`). -/

/-- The Dedekind `η`-function is non-vanishing on `ℍ` (from `Δ = η²⁴ ≠ 0`). -/
private lemma eta_ne_zero' (τ : ℍ) : ModularForm.eta τ ≠ 0 := by
  have h : ModularForm.discriminant τ = ModularForm.eta τ ^ 24 := rfl
  have hne := discriminant_ne_zero τ
  rw [h] at hne
  exact fun hc => hne (by rw [hc]; ring)

/-- The rescaling factor `a = (π/√3)·η(τ)²` (paper `proofzweistern`), as a unit of `ℂ`. -/
private def latHatUnit (τ : ℍ) : ℂˣ :=
  Units.mk0 ((π : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ) * ModularForm.eta τ ^ 2) (by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    exact mul_ne_zero (div_ne_zero hπ hs3) (pow_ne_zero _ (eta_ne_zero' τ)))

private lemma latHatUnit_val (τ : ℍ) :
    (latHatUnit τ : ℂ) = (π : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ) * ModularForm.eta τ ^ 2 := rfl

/-- `√3² = 3` transported to `ℂ`. -/
private lemma sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

private lemma latHatUnit_pow4 (τ : ℍ) :
    (latHatUnit τ : ℂ) ^ 4 = (π : ℂ) ^ 4 / 9 * ModularForm.eta τ ^ 8 := by
  have hs4 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 4 = 9 := by
    calc ((Real.sqrt 3 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) ^ 2 := by ring
    _ = 9 := by rw [sqrt3_sq]; norm_num
  rw [latHatUnit_val, mul_pow, div_pow, hs4]; ring

private lemma latHatUnit_pow6 (τ : ℍ) :
    (latHatUnit τ : ℂ) ^ 6 = (π : ℂ) ^ 6 / 27 * ModularForm.eta τ ^ 12 := by
  have hs6 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 6 = 27 := by
    calc ((Real.sqrt 3 : ℝ) : ℂ) ^ 6 = (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) ^ 3 := by ring
    _ = 27 := by rw [sqrt3_sq]; norm_num
  rw [latHatUnit_val, mul_pow, div_pow, hs6]; ring

/-- `¼g₂(L̂) = 3·E₄/η⁸` (paper `proofzweistern`). -/
private lemma latHat_g₂_div_four (τ : ℍ) :
    (latHatUnit τ • Lτ τ).g₂ / 4 = 3 * (E₄ τ / ModularForm.eta τ ^ 8) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hη : ModularForm.eta τ ≠ 0 := eta_ne_zero' τ
  rw [PeriodPair.g₂_smul, g₂_Lτ, latHatUnit_pow4]
  field_simp
  ring

/-- `¼g₃(L̂) = 2·E₆/η¹²` (paper `proofzweistern`). -/
private lemma latHat_g₃_div_four (τ : ℍ) :
    (latHatUnit τ • Lτ τ).g₃ / 4 = 2 * (E₆ τ / ModularForm.eta τ ^ 12) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hη : ModularForm.eta τ ≠ 0 := eta_ne_zero' τ
  rw [PeriodPair.g₃_smul, g₃_Lτ, latHatUnit_pow6]
  field_simp
  ring

/-- `¼g₂(L̂)` is an algebraic integer whenever `j = 1728J` is. -/
private lemma isIntegral_latHat_g₂_div_four (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ)) :
    IsIntegral ℤ ((latHatUnit τ • Lτ τ).g₂ / 4) := by
  rw [latHat_g₂_div_four]
  have h3 : IsIntegral ℤ (3 : ℂ) := by
    rw [show (3 : ℂ) = algebraMap ℤ ℂ 3 by simp]; exact isIntegral_algebraMap
  exact h3.mul (isIntegral_E₄_div_eta_pow τ hj)

/-- `¼g₃(L̂)` is an algebraic integer whenever `j = 1728J` is. -/
private lemma isIntegral_latHat_g₃_div_four (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ)) :
    IsIntegral ℤ ((latHatUnit τ • Lτ τ).g₃ / 4) := by
  rw [latHat_g₃_div_four]
  have h2 : IsIntegral ℤ (2 : ℂ) := by
    rw [show (2 : ℂ) = algebraMap ℤ ℂ 2 by simp]; exact isIntegral_algebraMap
  exact h2.mul (isIntegral_E₆_div_eta_pow τ hj)

/-- Transfer of integrality: since `¼g₂(L̂)` and `¼g₃(L̂)` are algebraic integers (given
`j = 1728J` integral), everything integral over `ℤ[¼g₂(L̂), ¼g₃(L̂)]` is integral over `ℤ`
(tower of integral extensions). This is the bridge that turns `theomwpu`'s conclusion
(integrality over `ℤ[¼g₂, ¼g₃]`) into integrality over `ℤ`. -/
private lemma isIntegral_of_adjoin_latHat (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ)) {x : ℂ}
    (hx : IsIntegral (Algebra.adjoin ℤ
      ({(latHatUnit τ • Lτ τ).g₂ / 4, (latHatUnit τ • Lτ τ).g₃ / 4} : Set ℂ)) x) :
    IsIntegral ℤ x := by
  have hgen : ∀ y ∈ ({(latHatUnit τ • Lτ τ).g₂ / 4, (latHatUnit τ • Lτ τ).g₃ / 4} : Set ℂ),
      IsIntegral ℤ y := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact isIntegral_latHat_g₂_div_four τ hj
    · rw [h]; exact isIntegral_latHat_g₃_div_four τ hj
  haveI : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ
      ({(latHatUnit τ • Lτ τ).g₂ / 4, (latHatUnit τ • Lτ τ).g₃ / 4} : Set ℂ)) :=
    Algebra.IsIntegral.adjoin hgen
  exact isIntegral_trans x hx

/-- Any finite sum `∑ AC·℘(v;L̂)` over nonzero `AC`-division points is an algebraic integer
(given `j = 1728J` integral): each summand is integral over `ℤ[¼g₂(L̂), ¼g₃(L̂)]` by
`theomwpu`, hence over `ℤ` by `isIntegral_of_adjoin_latHat`. -/
private lemma isIntegral_sum_mul_weierstrassP_latHat (τ : ℍ) (hj : IsIntegral ℤ (1728 * J τ))
    (M : ℕ) [NeZero M] (s : Finset (Fin M × Fin M)) (hs : (0 : Fin M × Fin M) ∉ s) :
    IsIntegral ℤ (∑ v ∈ s, (M : ℂ) *
      (latHatUnit τ • Lτ τ).weierstrassP ((latHatUnit τ • Lτ τ).divPt M v)) := by
  apply IsIntegral.sum
  intro v hv
  have hv0 : v ≠ 0 := fun h => hs (h ▸ hv)
  exact isIntegral_of_adjoin_latHat τ hj ((latHatUnit τ • Lτ τ).theomwpu M hv0)

/-- Division points scale linearly under `a • L`: `divPt(a•L) = a·divPt(L)`. -/
private lemma divPt_smul (a : ℂˣ) (L : PeriodPair) (m : ℕ) (v : Fin m × Fin m) :
    (a • L).divPt m v = (a : ℂ) * L.divPt m v := by
  simp only [PeriodPair.divPt, PeriodPair.smul_ω₁, PeriodPair.smul_ω₂]; ring

/-- `a² = (π²/3)·η⁴` for the rescaling unit `a = (π/√3)·η²`. -/
private lemma latHatUnit_sq (τ : ℍ) :
    (latHatUnit τ : ℂ) ^ 2 = (π : ℂ) ^ 2 / 3 * ModularForm.eta τ ^ 4 := by
  rw [latHatUnit_val, mul_pow, div_pow, sqrt3_sq]; ring

/-- The CM norm identity `(Cτ)·(C τbar) = AC` (product of the roots of `X² + BX + AC`). -/
private lemma C_mul_conj_mul {τ : ℍ} {A B C : ℤ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    ((C : ℂ) * τ) * ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) = (A : ℂ) * C := by
  rcases eq_or_ne ((C : ℂ)) 0 with hC | hC
  · simp [hC]
  · have hconj : (A : ℂ) + B * (starRingEnd ℂ) (τ : ℂ) +
        C * ((starRingEnd ℂ) (τ : ℂ)) ^ 2 = 0 := by
      have := congrArg (starRingEnd ℂ) hCM; simpa using this
    have hX : ((C : ℂ) * τ) ^ 2 + B * ((C : ℂ) * τ) + A * C = 0 := by
      linear_combination (C : ℂ) * hCM
    have hY : ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) ^ 2 +
        B * ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) + A * C = 0 := by
      linear_combination (C : ℂ) * hconj
    have hne : (C : ℂ) * τ ≠ (C : ℂ) * (starRingEnd ℂ) (τ : ℂ) := by
      intro h
      have hτ : (τ : ℂ) = (starRingEnd ℂ) (τ : ℂ) := mul_left_cancel₀ hC h
      have him := congrArg Complex.im hτ
      simp only [Complex.conj_im, UpperHalfPlane.coe_im] at him
      exact absurd him (by have := τ.im_pos; linarith)
    have hfac : ((C : ℂ) * τ - (C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) *
        ((C : ℂ) * τ + (C : ℂ) * (starRingEnd ℂ) (τ : ℂ) + B) = 0 := by
      linear_combination hX - hY
    have hsum : (C : ℂ) * τ + (C : ℂ) * (starRingEnd ℂ) (τ : ℂ) = -B := by
      have hz := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
      linear_combination hz
    linear_combination -hX + ((C : ℂ) * τ) * hsum

/-! ### `lemkapa2`: the elliptic ζ-combination (Milla's `lemfellip`–`lemkapa2` + `lemctau`)

We prove `∑_{v ∈ DIV(Cτ)} ℘(v) = −AC·η₁ + C²τ·η₂ (= −Cτ·κ)` by the `theowpsum` template of
`DivisionValues.lean`, applied to multiplication by `α = Cτ` (which maps `L_τ` into itself
with index `AC`): the difference `∑_u ℘(z+u) − α²·℘(αz)`, summed over a transversal `u` of
`α⁻¹L/L`, is entire and elliptic, hence a constant `c`; the ζ-combination
`∑_u ζ(z+u) − α·ζ(αz)` has derivative `−(that difference)` and additive period defect
`AC·η₁ − C²τ·η₂` in the direction `ω₁ = 1`, so `F(z) = ζ-comb + c·z`, being locally constant
on the connected complement of `α⁻¹L`, forces `c = −AC·η₁ + C²τ·η₂`.  Evaluating at `z = 0`
identifies `c` with the division-value sum.  The transversal is Milla's `lemctau`
(eq. `ctauu`): the `M = AC` points `u = (v₁/M) + (v₂/M)·τ` with `C ∣ v₂` and
`M ∣ C·v₁ − B·v₂`. -/

section Lemkapa2

/-- The lattice is countable (local copy of the private helper in `DivisionValues.lean`). -/
private lemma countable_lattice_cm (L : PeriodPair) : (↑L.lattice : Set ℂ).Countable := by
  have : Countable ↥L.lattice := countable_of_Lindelof_of_discrete
  simpa using Set.countable_range (Subtype.val : ↥L.lattice → ℂ)

/-- A signed fraction `k/m` with integral value and `|k| < m` is zero (local copy of the
private helper in `DivisionValues.lean`). -/
private lemma frac_den_one_imp_zero_cm {m : ℕ} (hm : 0 < m) {k : ℤ}
    (hlt : k.natAbs < m) (h : ((k : ℚ) / (m : ℚ)).den = 1) : k = 0 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  set q : ℚ := (k : ℚ) / (m : ℚ) with hqdef
  have heq : ((q.num : ℤ) : ℚ) = q := (Rat.den_eq_one_iff q).mp h
  have hqk : (k : ℚ) = q.num * (m : ℚ) := by
    rw [heq, hqdef, div_mul_cancel₀ _ hmQ]
  have hkeq : k = q.num * (m : ℤ) := by exact_mod_cast hqk
  have hnat : k.natAbs = q.num.natAbs * m := by
    rw [hkeq, Int.natAbs_mul, Int.natAbs_natCast]
  rcases Nat.eq_zero_or_pos q.num.natAbs with h0 | h0
  · rw [hkeq]; simp [Int.natAbs_eq_zero.mp h0]
  · exfalso
    have hle : m ≤ q.num.natAbs * m := Nat.le_mul_of_pos_left m h0
    omega

/-- Division points with distinct indices differ by a non-lattice point (local copy of the
private helper in `DivisionValues.lean`). -/
private lemma divPt_sub_notMem_lattice_cm (L : PeriodPair) {m : ℕ} (hm : 0 < m)
    {v v' : Fin m × Fin m} (hne : v ≠ v') : L.divPt m v - L.divPt m v' ∉ L.lattice := by
  intro hmem
  have hdiff : L.divPt m v - L.divPt m v'
      = ((((v.1 : ℤ) - (v'.1 : ℤ) : ℤ) : ℚ) / (m : ℚ) : ℚ) * L.ω₁
        + ((((v.2 : ℤ) - (v'.2 : ℤ) : ℤ) : ℚ) / (m : ℚ) : ℚ) * L.ω₂ := by
    simp only [PeriodPair.divPt]; push_cast; ring
  rw [hdiff, PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at hmem
  obtain ⟨hd1, hd2⟩ := hmem
  have e1 : (v.1 : ℤ) - (v'.1 : ℤ) = 0 := by
    refine frac_den_one_imp_zero_cm hm ?_ hd1
    have := v.1.isLt; have := v'.1.isLt; omega
  have e2 : (v.2 : ℤ) - (v'.2 : ℤ) = 0 := by
    refine frac_den_one_imp_zero_cm hm ?_ hd2
    have := v.2.isLt; have := v'.2.isLt; omega
  apply hne
  have h1 : v.1 = v'.1 := Fin.ext (by omega)
  have h2 : v.2 = v'.2 := Fin.ext (by omega)
  exact Prod.ext h1 h2

/-- Iterated quasi-periodicity of `ζ` in a single direction, for integer multiples. -/
private lemma weierstrassZeta_add_int_cm (L : PeriodPair) {ω et : ℂ} (hω : ω ∈ L.lattice)
    (hq : ∀ z ∉ L.lattice, L.weierstrassZeta (z + ω) = L.weierstrassZeta z + et) (a : ℤ)
    {w : ℂ} (hw : w ∉ L.lattice) :
    L.weierstrassZeta (w + (a : ℂ) * ω) = L.weierstrassZeta w + (a : ℂ) * et := by
  have hmem : ∀ b : ℤ, w + (b : ℂ) * ω ∉ L.lattice := by
    intro b hc
    apply hw
    have hb : (b : ℂ) * ω ∈ L.lattice := by
      rw [← zsmul_eq_mul]; exact zsmul_mem hω b
    simpa using sub_mem hc hb
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show w + ((k + 1 : ℤ) : ℂ) * ω = (w + ((k : ℤ) : ℂ) * ω) + ω by push_cast; ring,
      hq _ (hmem k), ih]
    push_cast; ring
  | pred k ih =>
    have h := hq (w + ((-k - 1 : ℤ) : ℂ) * ω) (hmem (-k - 1))
    rw [show w + ((-k - 1 : ℤ) : ℂ) * ω + ω = w + ((-k : ℤ) : ℂ) * ω by push_cast; ring,
      ih] at h
    push_cast at h ⊢
    linear_combination -h

/-- The additive quasi-period map: `ζ(w + (m·ω₁ + n·ω₂)) = ζ(w) + m·η₁ + n·η₂` for `w ∉ L`. -/
private lemma weierstrassZeta_add_pair_cm (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice)
    (m n : ℤ) :
    L.weierstrassZeta (w + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂))
      = L.weierstrassZeta w + (m : ℂ) * L.eta₁ + (n : ℂ) * L.eta₂ := by
  have hmem : w + (m : ℂ) * L.ω₁ ∉ L.lattice := by
    intro hc
    apply hw
    have : (m : ℂ) * L.ω₁ ∈ L.lattice := by
      rw [← zsmul_eq_mul]; exact zsmul_mem L.ω₁_mem_lattice m
    simpa using sub_mem hc this
  have h1 := weierstrassZeta_add_int_cm L L.ω₁_mem_lattice
    (fun z hz => L.weierstrassZeta_add_ω₁ z hz) m hw
  have h2 := weierstrassZeta_add_int_cm L L.ω₂_mem_lattice
    (fun z hz => L.weierstrassZeta_add_ω₂ z hz) n hmem
  rw [show w + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂)
      = (w + (m : ℂ) * L.ω₁) + (n : ℂ) * L.ω₂ by ring, h2, h1]

open Classical in
/-- The index set of Milla's `lemctau` (eq. `ctauu`): the pairs `(v₁, v₂) ∈ (ℤ/M)²` (with
`M = AC`) for which `u = (v₁/M) + (v₂/M)·τ` satisfies `Cτ·u ∈ L_τ`, i.e. `C ∣ v₂` and
`M ∣ C·v₁ − B·v₂`.  These `M` points form a transversal of `(Cτ)⁻¹L_τ/L_τ`; the `M − 1`
nonzero ones are exactly the `Cτ`-division points `DIV(Cτ)`. -/
private def cmSet (B C : ℤ) (M : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun v => C ∣ (v.2 : ℤ) ∧ (M : ℤ) ∣ C * (v.1 : ℤ) - B * (v.2 : ℤ)

private lemma mem_cmSet_iff {B C : ℤ} {M : ℕ} {v : Fin M × Fin M} :
    v ∈ cmSet B C M ↔ C ∣ (v.2 : ℤ) ∧ (M : ℤ) ∣ C * (v.1 : ℤ) - B * (v.2 : ℤ) := by
  simp [cmSet]

private lemma zero_mem_cmSet {B C : ℤ} {M : ℕ} [NeZero M] :
    (0 : Fin M × Fin M) ∈ cmSet B C M := by
  simp [mem_cmSet_iff]

/-- `Cτ ∈ L_τ`. -/
private lemma cm_alpha_mem (τ : ℍ) (C : ℤ) : (C : ℂ) * τ ∈ (Lτ τ).lattice :=
  PeriodPair.mem_lattice.mpr ⟨0, C, by simp⟩

/-- Multiplication by `α = Cτ` maps the lattice into itself (this is complex
multiplication: `Cτ·1 = Cτ ∈ L` and `Cτ·τ = −A − Bτ ∈ L`). -/
private lemma cm_alpha_mul_mem {τ : ℍ} {A B C : ℤ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    {l : ℂ} (hl : l ∈ (Lτ τ).lattice) : (C : ℂ) * τ * l ∈ (Lτ τ).lattice := by
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hl
  refine PeriodPair.mem_lattice.mpr ⟨-(n * A), m * C - n * B, ?_⟩
  simp only [Lτ_ω₁, Lτ_ω₂] at hmn ⊢
  push_cast
  linear_combination ((C : ℂ) * τ) * hmn - (n : ℂ) * hCM

/-- Points of `cmSet` are mapped into the lattice by `α = Cτ` (they lie in `α⁻¹L`). -/
private lemma cmSet_mul_divPt_mem {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) (hM0 : 0 < M) (hMAC : (M : ℤ) = A * C)
    {v : Fin M × Fin M} (hv : v ∈ cmSet B C M) :
    (C : ℂ) * τ * (Lτ τ).divPt M v ∈ (Lτ τ).lattice := by
  obtain ⟨hv2, hv1⟩ := mem_cmSet_iff.mp hv
  obtain ⟨w, hw⟩ := hv2
  obtain ⟨d, hd⟩ := hv1
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hwC : ((v.2 : ℕ) : ℂ) = (C : ℂ) * w := by exact_mod_cast hw
  have hdC : (C : ℂ) * ((v.1 : ℕ) : ℂ) - (B : ℂ) * ((v.2 : ℕ) : ℂ) = (M : ℂ) * d := by
    exact_mod_cast hd
  have hMACC : (M : ℂ) = (A : ℂ) * C := by exact_mod_cast hMAC
  have hu : (M : ℂ) * (Lτ τ).divPt M v = ((v.1 : ℕ) : ℂ) + ((v.2 : ℕ) : ℂ) * τ := by
    simp only [PeriodPair.divPt, Lτ_ω₁, Lτ_ω₂, mul_one]
    field_simp
  refine PeriodPair.mem_lattice.mpr ⟨-w, d, ?_⟩
  apply mul_left_cancel₀ hMC
  rw [show (M : ℂ) * ((C : ℂ) * ↑τ * (Lτ τ).divPt M v)
      = (C : ℂ) * ↑τ * ((M : ℂ) * (Lτ τ).divPt M v) by ring, hu]
  simp only [Lτ_ω₁, Lτ_ω₂, mul_one]
  push_cast
  linear_combination (-(C : ℂ) * w) * hCM - ((B : ℂ) * τ + (C : ℂ) * (τ : ℂ) ^ 2) * hwC
    - (τ : ℂ) * hdC - (w : ℂ) * hMACC

/-- **Covering**: every point of `α⁻¹L` is congruent mod `L` to (minus) a point of `cmSet`
(the transversal property of Milla's `lemctau`). -/
private lemma cmSet_exists_add_mem {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C)
    {z : ℂ} (hz : (C : ℂ) * τ * z ∈ (Lτ τ).lattice) :
    ∃ v ∈ cmSet B C M, z + (Lτ τ).divPt M v ∈ (Lτ τ).lattice := by
  have hM0 : (0 : ℤ) < M := by rw [hMAC]; exact mul_pos hA hC
  obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hz
  simp only [Lτ_ω₁, Lτ_ω₂, mul_one] at hpq
  -- the representative: `y ≡ p (mod A)`, `x ≡ Bp − Aq (mod M)`, `v = (x, C·y)`
  set y : ℤ := p % A with hydef
  set x : ℤ := (B * p - A * q) % M with hxdef
  have hy0 : 0 ≤ y := Int.emod_nonneg _ hA.ne'
  have hyA : y < A := Int.emod_lt_of_pos _ hA
  have hx0 : 0 ≤ x := Int.emod_nonneg _ hM0.ne'
  have hxM : x < M := Int.emod_lt_of_pos _ hM0
  have hCy0 : 0 ≤ C * y := mul_nonneg hC.le hy0
  have hCyM : C * y < M := by
    have h1 : C * y < C * A := mul_lt_mul_of_pos_left hyA hC
    nlinarith
  -- exact-division witnesses
  obtain ⟨k, hk⟩ : (A : ℤ) ∣ y - p := ⟨-(p / A), by rw [hydef, Int.emod_def]; ring⟩
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ x - (B * p - A * q) :=
    ⟨-((B * p - A * q) / M), by rw [hxdef, Int.emod_def]; ring⟩
  -- the arithmetic membership conditions
  have hAxy : (A : ℤ) ∣ x - B * y := by
    have d1 : (A : ℤ) ∣ x - (B * p - A * q) := dvd_trans ⟨C, hMAC⟩ ⟨t, ht⟩
    have d2 : (A : ℤ) ∣ B * (p - y) := Dvd.dvd.mul_left ⟨-k, by linarith⟩ B
    have hsplit : x - B * y = (x - (B * p - A * q)) + B * (p - y) + A * (-q) := by ring
    rw [hsplit]
    exact dvd_add (dvd_add d1 d2) (Dvd.intro _ rfl)
  have hb1 : x.toNat < M := by omega
  have hb2 : (C * y).toNat < M := by omega
  set v : Fin M × Fin M := (⟨x.toNat, hb1⟩, ⟨(C * y).toNat, hb2⟩) with hvdef
  have hv1 : ((v.1 : ℕ) : ℤ) = x := by simp [hvdef, Int.toNat_of_nonneg hx0]
  have hv2 : ((v.2 : ℕ) : ℤ) = C * y := by simp [hvdef, Int.toNat_of_nonneg hCy0]
  refine ⟨v, ?_, ?_⟩
  · -- membership in `cmSet`
    rw [mem_cmSet_iff]
    constructor
    · rw [hv2]; exact dvd_mul_right C y
    · obtain ⟨e, he⟩ := hAxy
      refine ⟨e, ?_⟩
      rw [hv1, hv2, hMAC]
      linear_combination (C : ℤ) * he
  · -- lattice membership of `z + u`
    have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
    have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hv1C : ((v.1 : ℕ) : ℂ) = (x : ℂ) := by exact_mod_cast hv1
    have hv2C : ((v.2 : ℕ) : ℂ) = (C : ℂ) * y := by exact_mod_cast hv2
    have hMdiv : (M : ℂ) * (Lτ τ).divPt M v = (x : ℂ) + (C : ℂ) * (y : ℂ) * τ := by
      simp only [PeriodPair.divPt, Lτ_ω₁, Lτ_ω₂, mul_one, hv1C, hv2C]
      field_simp
    have hkC : (y : ℂ) - p = (A : ℂ) * k := by exact_mod_cast hk
    have htC : (x : ℂ) - ((B : ℂ) * p - (A : ℂ) * q) = (M : ℂ) * t := by exact_mod_cast ht
    have hMACC : (M : ℂ) = (A : ℂ) * C := by exact_mod_cast hMAC
    refine PeriodPair.mem_lattice.mpr ⟨t, k, ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hCne hτne) hMne)
    rw [show (C : ℂ) * ↑τ * (M : ℂ) * (z + (Lτ τ).divPt M v)
        = (M : ℂ) * ((C : ℂ) * ↑τ * z) + (C : ℂ) * ↑τ * ((M : ℂ) * (Lτ τ).divPt M v) by ring,
      ← hpq, hMdiv]
    simp only [Lτ_ω₁, Lτ_ω₂, mul_one]
    linear_combination (-(C : ℂ) * p) * hCM + (-(C : ℂ) * τ) * htC
      + (-(C : ℂ) ^ 2 * (τ : ℂ) ^ 2) * hkC
      + ((C : ℂ) * k * (τ : ℂ) ^ 2 - (p : ℂ) - (q : ℂ) * τ) * hMACC

/-- **Counting** (Milla's `lemctau`): the transversal has exactly `M = AC` points. -/
private lemma card_cmSet {A B C : ℤ} {M : ℕ} (hA : 0 < A) (hC : 0 < C)
    (hMAC : (M : ℤ) = A * C) : (cmSet B C M).card = M := by
  set a := A.toNat with hadef
  set c := C.toNat with hcdef
  have haA : (a : ℤ) = A := Int.toNat_of_nonneg hA.le
  have hcC : (c : ℤ) = C := Int.toNat_of_nonneg hC.le
  have ha0 : 0 < a := by omega
  have hc0 : 0 < c := by omega
  have hM : M = a * c := by
    have : (M : ℤ) = (a : ℤ) * c := by rw [haA, hcC]; exact hMAC
    exact_mod_cast this
  have hM0 : 0 < M := by rw [hM]; exact Nat.mul_pos ha0 hc0
  have hAne : (A : ℤ) ≠ 0 := by omega
  have hCne : (C : ℤ) ≠ 0 := by omega
  -- bounds for the two maps of the bijection with `Fin a × Fin c`
  have hbound1 : ∀ u : Fin M, (u : ℕ) / c < a := fun u => by
    rw [Nat.div_lt_iff_lt_mul hc0]
    calc (u : ℕ) < M := u.isLt
    _ = a * c := hM
  have hbound2 : ∀ u : Fin M, (u : ℕ) / a < c := fun u => by
    rw [Nat.div_lt_iff_lt_mul ha0]
    calc (u : ℕ) < M := u.isLt
    _ = a * c := hM
    _ = c * a := Nat.mul_comm a c
  have hjb1 : ∀ w : Fin a × Fin c,
      ((B * ((w.1 : ℕ) : ℤ)) % A).toNat + a * (w.2 : ℕ) < M := fun w => by
    have h1 : (B * ((w.1 : ℕ) : ℤ)) % A < A := Int.emod_lt_of_pos _ (by omega)
    have h2 : 0 ≤ (B * ((w.1 : ℕ) : ℤ)) % A := Int.emod_nonneg _ hAne
    have h3 : ((B * ((w.1 : ℕ) : ℤ)) % A).toNat < a := by omega
    calc ((B * ((w.1 : ℕ) : ℤ)) % A).toNat + a * (w.2 : ℕ)
        < a + a * (w.2 : ℕ) := Nat.add_lt_add_right h3 _
    _ = a * ((w.2 : ℕ) + 1) := by ring
    _ ≤ a * c := Nat.mul_le_mul_left a (by have := w.2.isLt; omega)
    _ = M := hM.symm
  have hjb2 : ∀ w : Fin a, c * (w : ℕ) < M := fun w => by
    calc c * (w : ℕ) < c * a := mul_lt_mul_of_pos_left w.isLt hc0
    _ = a * c := Nat.mul_comm c a
    _ = M := hM.symm
  -- the bijection
  have key : (cmSet B C M).card = (Finset.univ : Finset (Fin a × Fin c)).card := by
    refine Finset.card_nbij'
      (i := fun v => (⟨(v.2 : ℕ) / c, hbound1 v.2⟩, ⟨(v.1 : ℕ) / a, hbound2 v.1⟩))
      (j := fun w => (⟨((B * ((w.1 : ℕ) : ℤ)) % A).toNat + a * (w.2 : ℕ), hjb1 w⟩,
        ⟨c * (w.1 : ℕ), hjb2 w.1⟩))
      (fun v _ => Finset.mem_univ _) ?_ ?_ ?_
    · -- MapsTo j
      intro w _
      rw [Finset.mem_coe, mem_cmSet_iff]
      have h2 : 0 ≤ (B * ((w.1 : ℕ) : ℤ)) % A := Int.emod_nonneg _ hAne
      constructor
      · refine ⟨((w.1 : ℕ) : ℤ), ?_⟩
        push_cast
        rw [hcC]
      · refine ⟨((w.2 : ℕ) : ℤ) - (B * ((w.1 : ℕ) : ℤ)) / A, ?_⟩
        have hemod := Int.emod_def (B * ((w.1 : ℕ) : ℤ)) A
        push_cast [Int.toNat_of_nonneg h2]
        rw [hMAC]
        linear_combination (C : ℤ) * hemod + (C * ((w.2 : ℕ) : ℤ)) * haA
          - (B * ((w.1 : ℕ) : ℤ)) * hcC
    · -- left inverse (on cmSet)
      intro v hv
      rw [Finset.mem_coe, mem_cmSet_iff] at hv
      obtain ⟨hdvd2, ⟨d, hd⟩⟩ := hv
      have hcv2 : c ∣ (v.2 : ℕ) := by
        have h : (c : ℤ) ∣ ((v.2 : ℕ) : ℤ) := by rw [hcC]; exact hdvd2
        exact_mod_cast h
      set y : ℕ := (v.2 : ℕ) / c with hydef
      have hv2c : c * y = (v.2 : ℕ) := Nat.mul_div_cancel' hcv2
      -- `A ∣ v₁ − B·y`, from `M ∣ C·v₁ − B·v₂` and `v₂ = C·y`
      have hAd : ((v.1 : ℕ) : ℤ) - B * (y : ℤ) = A * d := by
        have hv2y : ((v.2 : ℕ) : ℤ) = C * (y : ℤ) := by
          rw [← hcC]; exact_mod_cast hv2c.symm
        have hCC : (C : ℤ) * (((v.1 : ℕ) : ℤ) - B * (y : ℤ)) = C * (A * d) := by
          calc (C : ℤ) * (((v.1 : ℕ) : ℤ) - B * (y : ℤ))
              = C * ((v.1 : ℕ) : ℤ) - B * ((v.2 : ℕ) : ℤ) := by rw [hv2y]; ring
          _ = (M : ℤ) * d := hd
          _ = C * (A * d) := by rw [hMAC]; ring
        exact mul_left_cancel₀ hCne hCC
      have hmod : (B * (y : ℤ)) % A = ((v.1 : ℕ) : ℤ) % A := by
        conv_rhs => rw [show ((v.1 : ℕ) : ℤ) = B * (y : ℤ) + A * d by linarith]
        rw [Int.add_mul_emod_self_left]
      have htn : ((B * (y : ℤ)) % A).toNat = (v.1 : ℕ) % a := by
        have h1 : ((v.1 : ℕ) : ℤ) % A = (((v.1 : ℕ) % a : ℕ) : ℤ) := by
          rw [← haA, Int.natCast_mod]
        omega
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · change ((B * (y : ℤ)) % A).toNat + a * ((v.1 : ℕ) / a) = (v.1 : ℕ)
        rw [htn]
        exact Nat.mod_add_div _ _
      · exact hv2c
    · -- right inverse (on univ)
      intro w _
      have h2 : 0 ≤ (B * ((w.1 : ℕ) : ℤ)) % A := Int.emod_nonneg _ hAne
      have h1 : (B * ((w.1 : ℕ) : ℤ)) % A < A := Int.emod_lt_of_pos _ (by omega)
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · change (c * (w.1 : ℕ)) / c = (w.1 : ℕ)
        exact Nat.mul_div_cancel_left _ hc0
      · change (((B * ((w.1 : ℕ) : ℤ)) % A).toNat + a * (w.2 : ℕ)) / a = (w.2 : ℕ)
        rw [Nat.add_mul_div_left _ _ ha0, Nat.div_eq_of_lt (by omega)]
        omega
  rw [key, Finset.card_univ]
  simp [hM]

private lemma cmM_pos {A C : ℤ} {M : ℕ} (hA : 0 < A) (hC : 0 < C)
    (hMAC : (M : ℤ) = A * C) : 0 < M := by
  have : (0 : ℤ) < (M : ℤ) := by rw [hMAC]; exact mul_pos hA hC
  omega

/-- **Pole cancellation** (analogue of `mulPole_identity` in `DivisionValues.lean`): at a point
`z ∈ α⁻¹L` congruent to `−u_{v₀}`, the diverging pair `℘(w + u_{v₀}) − α²·℘(αw)` equals an
expression analytic at `z` (the two double poles cancel algebraically). -/
private lemma mulPoleCM_identity {τ : ℍ} {C : ℤ} {M : ℕ}
    (hCne : (C : ℂ) ≠ 0) {z : ℂ} {v₀ : Fin M × Fin M}
    (hv₀ : z + (Lτ τ).divPt M v₀ ∈ (Lτ τ).lattice)
    (hmp : (C : ℂ) * τ * z ∈ (Lτ τ).lattice) (w : ℂ) :
    (Lτ τ).weierstrassP (w + (Lτ τ).divPt M v₀)
        - ((C : ℂ) * τ) ^ 2 * (Lτ τ).weierstrassP ((C : ℂ) * τ * w)
      = (Lτ τ).weierstrassPExcept 0 (w - z)
        - ((C : ℂ) * τ) ^ 2 * (Lτ τ).weierstrassPExcept 0 ((C : ℂ) * τ * (w - z)) := by
  have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hE1 : (Lτ τ).weierstrassPExcept 0 (w - z)
      = (Lτ τ).weierstrassP (w - z) + -((w - z) ^ 2)⁻¹ := by
    simpa using (Lτ τ).weierstrassPExcept_def (0 : (Lτ τ).lattice) (w - z)
  have hE2 : (Lτ τ).weierstrassPExcept 0 ((C : ℂ) * τ * (w - z))
      = (Lτ τ).weierstrassP ((C : ℂ) * τ * (w - z))
        + -(((C : ℂ) * τ * (w - z)) ^ 2)⁻¹ := by
    simpa using (Lτ τ).weierstrassPExcept_def (0 : (Lτ τ).lattice) ((C : ℂ) * τ * (w - z))
  have hP1 : (Lτ τ).weierstrassP (w - z) = (Lτ τ).weierstrassP (w + (Lτ τ).divPt M v₀) := by
    rw [show w + (Lτ τ).divPt M v₀ = (w - z) + (z + (Lτ τ).divPt M v₀) by ring]
    exact ((Lτ τ).weierstrassP_add_coe (w - z) ⟨_, hv₀⟩).symm
  have hP2 : (Lτ τ).weierstrassP ((C : ℂ) * τ * (w - z))
      = (Lτ τ).weierstrassP ((C : ℂ) * τ * w) := by
    rw [show (C : ℂ) * τ * w = ((C : ℂ) * τ * (w - z)) + ((C : ℂ) * τ * z) by ring]
    exact ((Lτ τ).weierstrassP_add_coe ((C : ℂ) * τ * (w - z)) ⟨_, hmp⟩).symm
  have hfrac : ((C : ℂ) * τ) ^ 2 * (((C : ℂ) * τ * (w - z)) ^ 2)⁻¹ = ((w - z) ^ 2)⁻¹ := by
    rcases eq_or_ne (w - z) 0 with h | h
    · simp [h]
    · field_simp
  rw [hE1, hE2, hP1, hP2]
  linear_combination -hfrac

/-- The multiplication-by-`Cτ` difference `∑_{u ∈ transversal} ℘(z + u) − (Cτ)²·℘(Cτ·z)`
(the analogue of `mulDiff` in `DivisionValues.lean` for complex multiplication). -/
private def mulDiffCM (τ : ℍ) (B C : ℤ) (M : ℕ) (z : ℂ) : ℂ :=
  (∑ v ∈ cmSet B C M, (Lτ τ).weierstrassP (z + (Lτ τ).divPt M v))
    - ((C : ℂ) * τ) ^ 2 * (Lτ τ).weierstrassP ((C : ℂ) * τ * z)

/-- The `Cτ`-multiplication difference is entire: away from `α⁻¹L` every summand is analytic,
and at `z ∈ α⁻¹L` the two double poles cancel (`mulPoleCM_identity`), using that the
transversal hits the class of `z` exactly once. -/
private lemma analyticAt_mulDiffCM {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C) (z : ℂ) :
    AnalyticAt ℂ (mulDiffCM τ B C M) z := by
  have hM0 : 0 < M := cmM_pos hA hC hMAC
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  by_cases hmp : (C : ℂ) * τ * z ∈ (Lτ τ).lattice
  · obtain ⟨v₀, hv₀mem, hv₀⟩ := cmSet_exists_add_mem hCM hA hC hMAC hmp
    have heq : mulDiffCM τ B C M
        = fun w => (∑ v ∈ (cmSet B C M).erase v₀,
              (Lτ τ).weierstrassP (w + (Lτ τ).divPt M v))
            + ((Lτ τ).weierstrassPExcept 0 (w - z)
              - ((C : ℂ) * τ) ^ 2 * (Lτ τ).weierstrassPExcept 0 ((C : ℂ) * τ * (w - z))) := by
      funext w
      simp only [mulDiffCM]
      rw [← Finset.add_sum_erase (cmSet B C M)
          (fun v => (Lτ τ).weierstrassP (w + (Lτ τ).divPt M v)) hv₀mem,
        ← mulPoleCM_identity hCne hv₀ hmp w]
      ring
    rw [heq]
    apply AnalyticAt.add
    · apply Finset.analyticAt_fun_sum
      intro v hv
      have hne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
      have hnl : z + (Lτ τ).divPt M v ∉ (Lτ τ).lattice := by
        intro hcc
        exact divPt_sub_notMem_lattice_cm (Lτ τ) hM0 hne (by
          have h := sub_mem hcc hv₀
          simpa [add_sub_add_left_eq_sub] using h)
      have hf : AnalyticAt ℂ (fun w : ℂ => w + (Lτ τ).divPt M v) z := by fun_prop
      exact ((Lτ τ).analyticOnNhd_weierstrassP _ hnl).comp_of_eq hf rfl
    · apply AnalyticAt.sub
      · have hf : AnalyticAt ℂ (fun w : ℂ => w - z) z := by fun_prop
        exact ((Lτ τ).analyticAt_weierstrassPExcept 0).comp_of_eq hf (sub_self z)
      · refine analyticAt_const.mul ?_
        have hf : AnalyticAt ℂ (fun w : ℂ => (C : ℂ) * τ * (w - z)) z := by fun_prop
        exact ((Lτ τ).analyticAt_weierstrassPExcept 0).comp_of_eq hf (by rw [sub_self, mul_zero])
  · change AnalyticAt ℂ (fun w =>
        (∑ v ∈ cmSet B C M, (Lτ τ).weierstrassP (w + (Lτ τ).divPt M v))
          - ((C : ℂ) * τ) ^ 2 * (Lτ τ).weierstrassP ((C : ℂ) * τ * w)) z
    apply AnalyticAt.sub
    · apply Finset.analyticAt_fun_sum
      intro v hv
      have hnl : z + (Lτ τ).divPt M v ∉ (Lτ τ).lattice := fun hcc => hmp (by
        simpa [mul_add] using
          sub_mem (cm_alpha_mul_mem hCM hcc) (cmSet_mul_divPt_mem hCM hM0 hMAC hv))
      have hf : AnalyticAt ℂ (fun w : ℂ => w + (Lτ τ).divPt M v) z := by fun_prop
      exact ((Lτ τ).analyticOnNhd_weierstrassP _ hnl).comp_of_eq hf rfl
    · refine analyticAt_const.mul ?_
      have hf : AnalyticAt ℂ (fun w : ℂ => (C : ℂ) * τ * w) z := by fun_prop
      exact ((Lτ τ).analyticOnNhd_weierstrassP _ hmp).comp_of_eq hf rfl

/-- The `Cτ`-multiplication difference is entire and elliptic, hence constant (first
Liouville theorem; Milla's `lemfellip`/`lemkonst`). -/
private lemma exists_mulDiffCM_const {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C) :
    ∃ c : ℂ, ∀ z, mulDiffCM τ B C M z = c := by
  have hdiff : Differentiable ℂ (mulDiffCM τ B C M) :=
    fun z => (analyticAt_mulDiffCM hCM hA hC hMAC z).differentiableAt
  have hell : (Lτ τ).IsEllipticWith (mulDiffCM τ B C M) := by
    refine ⟨fun z => (analyticAt_mulDiffCM hCM hA hC hMAC z).meromorphicAt, ?_⟩
    intro z l
    simp only [mulDiffCM]
    congr 1
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [show z + (l : ℂ) + (Lτ τ).divPt M v = (z + (Lτ τ).divPt M v) + l by ring]
      exact (Lτ τ).weierstrassP_add_coe _ l
    · congr 1
      rw [show (C : ℂ) * τ * (z + (l : ℂ)) = (C : ℂ) * τ * z + (C : ℂ) * τ * (l : ℂ) by ring]
      exact (Lτ τ).weierstrassP_add_coe ((C : ℂ) * τ * z) ⟨_, cm_alpha_mul_mem hCM l.2⟩
  obtain ⟨c, hcf⟩ := hell.exists_eq_const_of_differentiable hdiff
  exact ⟨c, fun z => congrFun hcf z⟩

/-- The ζ-combination `∑_{u ∈ transversal} ζ(z + u) − Cτ·ζ(Cτ·z)` (Milla's `f`/`g` of
`lemfellip`/`lemkonst`, in the `zetaComb` form of `DivisionValues.lean`). -/
private def zetaCombCM (τ : ℍ) (B C : ℤ) (M : ℕ) (z : ℂ) : ℂ :=
  (∑ v ∈ cmSet B C M, (Lτ τ).weierstrassZeta (z + (Lτ τ).divPt M v))
    - (C : ℂ) * τ * (Lτ τ).weierstrassZeta ((C : ℂ) * τ * z)

/-- Off `α⁻¹L`, `zetaCombCM` is differentiable with derivative `−mulDiffCM` (since `ζ' = −℘`). -/
private lemma hasDerivAt_zetaCombCM {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C)
    {z : ℂ} (hU : (C : ℂ) * τ * z ∉ (Lτ τ).lattice) :
    HasDerivAt (zetaCombCM τ B C M) (-(mulDiffCM τ B C M z)) z := by
  have hM0 : 0 < M := cmM_pos hA hC hMAC
  have hda : ∀ p : ℂ, p ∉ (Lτ τ).lattice →
      HasDerivAt (Lτ τ).weierstrassZeta (-((Lτ τ).weierstrassP p)) p := by
    intro p hp
    have hd := ((Lτ τ).differentiableOn_weierstrassZeta.differentiableAt
      ((Lτ τ).isClosed_lattice.isOpen_compl.mem_nhds hp)).hasDerivAt
    rwa [(Lτ τ).deriv_weierstrassZeta p hp] at hd
  have hz1 : ∀ v ∈ cmSet B C M,
      HasDerivAt (fun w => (Lτ τ).weierstrassZeta (w + (Lτ τ).divPt M v))
        (-((Lτ τ).weierstrassP (z + (Lτ τ).divPt M v))) z := by
    intro v hv
    have hp : z + (Lτ τ).divPt M v ∉ (Lτ τ).lattice := fun hcc => hU (by
      simpa [mul_add] using
        sub_mem (cm_alpha_mul_mem hCM hcc) (cmSet_mul_divPt_mem hCM hM0 hMAC hv))
    exact (hda _ hp).comp_add_const z _
  have hsum : HasDerivAt
      (fun w => ∑ v ∈ cmSet B C M, (Lτ τ).weierstrassZeta (w + (Lτ τ).divPt M v))
      (∑ v ∈ cmSet B C M, -((Lτ τ).weierstrassP (z + (Lτ τ).divPt M v))) z :=
    HasDerivAt.fun_sum hz1
  have hcomp2 : HasDerivAt (fun w => (Lτ τ).weierstrassZeta ((C : ℂ) * τ * w))
      ((C : ℂ) * τ * -((Lτ τ).weierstrassP ((C : ℂ) * τ * z))) z := by
    have h := HasDerivAt.scomp (𝕜 := ℂ) z (hda _ hU)
      ((hasDerivAt_id' z).const_mul ((C : ℂ) * τ))
    simpa [Function.comp_def, mul_comm] using h
  have hterm2 : HasDerivAt (fun w => (C : ℂ) * τ * (Lτ τ).weierstrassZeta ((C : ℂ) * τ * w))
      ((C : ℂ) * τ * ((C : ℂ) * τ * -((Lτ τ).weierstrassP ((C : ℂ) * τ * z)))) z :=
    HasDerivAt.const_mul ((C : ℂ) * τ) hcomp2
  have hcomb : HasDerivAt (zetaCombCM τ B C M)
      ((∑ v ∈ cmSet B C M, -((Lτ τ).weierstrassP (z + (Lτ τ).divPt M v)))
        - (C : ℂ) * τ * ((C : ℂ) * τ * -((Lτ τ).weierstrassP ((C : ℂ) * τ * z)))) z :=
    hsum.sub hterm2
  convert hcomb using 1
  have hsn : (∑ v ∈ cmSet B C M, -((Lτ τ).weierstrassP (z + (Lτ τ).divPt M v)))
      = -(∑ v ∈ cmSet B C M, (Lτ τ).weierstrassP (z + (Lτ τ).divPt M v)) :=
    Finset.sum_neg_distrib _
  rw [hsn]
  simp only [mulDiffCM]
  ring

/-- The period-`1` defect of `zetaCombCM`: the sum contributes `M·η₁` (`M = |transversal|`),
the `Cτ·ζ(Cτz)`-term contributes `Cτ·(C·η₂)` (since `Cτ·1 = 0·ω₁ + C·ω₂`). -/
private lemma zetaCombCM_add_one {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C)
    {z : ℂ} (hU : (C : ℂ) * τ * z ∉ (Lτ τ).lattice) :
    zetaCombCM τ B C M (z + 1) = zetaCombCM τ B C M z
      + ((M : ℂ) * (Lτ τ).eta₁ - (C : ℂ) ^ 2 * τ * (Lτ τ).eta₂) := by
  have hM0 : 0 < M := cmM_pos hA hC hMAC
  have hzv : ∀ v ∈ cmSet B C M, z + (Lτ τ).divPt M v ∉ (Lτ τ).lattice := fun v hv hcc =>
    hU (by
      simpa [mul_add] using
        sub_mem (cm_alpha_mul_mem hCM hcc) (cmSet_mul_divPt_mem hCM hM0 hMAC hv))
  have hsum : (∑ v ∈ cmSet B C M, (Lτ τ).weierstrassZeta (z + 1 + (Lτ τ).divPt M v))
      = (∑ v ∈ cmSet B C M, (Lτ τ).weierstrassZeta (z + (Lτ τ).divPt M v))
        + (M : ℂ) * (Lτ τ).eta₁ := by
    have hterm : ∀ v ∈ cmSet B C M, (Lτ τ).weierstrassZeta (z + 1 + (Lτ τ).divPt M v)
        = (Lτ τ).weierstrassZeta (z + (Lτ τ).divPt M v) + (Lτ τ).eta₁ := fun v hv => by
      rw [show z + 1 + (Lτ τ).divPt M v = (z + (Lτ τ).divPt M v) + (Lτ τ).ω₁ by
        simp only [Lτ_ω₁]; ring]
      exact (Lτ τ).weierstrassZeta_add_ω₁ _ (hzv v hv)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
      card_cmSet hA hC hMAC, nsmul_eq_mul]
  have hmz : (Lτ τ).weierstrassZeta ((C : ℂ) * τ * (z + 1))
      = (Lτ τ).weierstrassZeta ((C : ℂ) * τ * z) + (C : ℂ) * (Lτ τ).eta₂ := by
    have h := weierstrassZeta_add_pair_cm (Lτ τ) hU 0 C
    rw [show (C : ℂ) * τ * (z + 1)
        = (C : ℂ) * τ * z + (((0 : ℤ) : ℂ) * (Lτ τ).ω₁ + ((C : ℤ) : ℂ) * (Lτ τ).ω₂) by
      simp only [Lτ_ω₁, Lτ_ω₂]; push_cast; ring, h]
    push_cast
    ring
  simp only [zetaCombCM]
  rw [hsum, hmz]
  ring

/-- **The value of the multiplication constant.**  `F(z) = zetaCombCM(z) + c·z` has zero
derivative on the connected set `(α⁻¹L)ᶜ`, hence is constant there; comparing at `z₀` and
`z₀ + 1` against the period defect of `zetaCombCM` forces
`c = −M·η₁ + C²τ·η₂` (Milla's `lemkonst` + the Laurent extraction of `lemkapa2`). -/
private lemma mulDiffCM_const_value {τ : ℍ} {A B C : ℤ} {M : ℕ}
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hA : 0 < A) (hC : 0 < C) (hMAC : (M : ℤ) = A * C) {c : ℂ}
    (hc : ∀ z, mulDiffCM τ B C M z = c) :
    c = -(M : ℂ) * (Lτ τ).eta₁ + (C : ℂ) ^ 2 * τ * (Lτ τ).eta₂ := by
  have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hα0 : (C : ℂ) * τ ≠ 0 := mul_ne_zero hCne hτne
  set S : Set ℂ := (fun z => (C : ℂ) * τ * z) ⁻¹' (↑(Lτ τ).lattice) with hSdef
  have hScount : S.Countable :=
    (countable_lattice_cm (Lτ τ)).preimage (mul_right_injective₀ hα0)
  have hSclosed : IsClosed S := IsClosed.preimage (by fun_prop) (Lτ τ).isClosed_lattice
  have hUopen : IsOpen (Sᶜ : Set ℂ) := hSclosed.isOpen_compl
  have hUconn : IsPreconnected (Sᶜ : Set ℂ) :=
    (hScount.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hcount2 : (S ∪ (fun z => z + 1) ⁻¹' S).Countable :=
    hScount.union (hScount.preimage (add_left_injective 1))
  obtain ⟨z₀, hz₀⟩ := (hcount2.isConnected_compl_of_one_lt_rank (by simp)).nonempty
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hz₀
  obtain ⟨hz₀S, hz₀S'⟩ := hz₀
  have hUz₀ : (C : ℂ) * τ * z₀ ∉ (Lτ τ).lattice := hz₀S
  set F : ℂ → ℂ := fun z => zetaCombCM τ B C M z + c * z with hFdef
  have hFderiv : ∀ z ∈ (Sᶜ : Set ℂ), HasDerivAt F 0 z := by
    intro z hz
    have hU : (C : ℂ) * τ * z ∉ (Lτ τ).lattice := hz
    have hG := hasDerivAt_zetaCombCM hCM hA hC hMAC hU
    rw [hc z] at hG
    have h2 : HasDerivAt (fun w => zetaCombCM τ B C M w + c * w) (-c + c * 1) z :=
      hG.fun_add ((hasDerivAt_id' z).const_mul c)
    have h3 : (-c + c * 1 : ℂ) = 0 := by ring
    rw [hFdef]
    exact h3 ▸ h2
  have hFdiff : DifferentiableOn ℂ F (Sᶜ) :=
    fun z hz => (hFderiv z hz).differentiableAt.differentiableWithinAt
  have hderivEq : (Sᶜ : Set ℂ).EqOn (deriv F) (deriv (fun _ => F z₀)) := by
    intro z hz
    rw [(hFderiv z hz).deriv, deriv_const']
  have hEqOn := hUopen.eqOn_of_deriv_eq hUconn hFdiff (differentiableOn_const _) hderivEq
    hz₀S rfl
  have e1 : F (z₀ + 1) = F z₀ := hEqOn hz₀S'
  have hdefect := zetaCombCM_add_one hCM hA hC hMAC hUz₀
  simp only [hFdef] at e1
  rw [hdefect] at e1
  linear_combination e1

/-- **`lemkapa2` for positive `A, C`**: the raw division-value identity of `lemkapa2_raw`. -/
private lemma lemkapa2_pos (τ : ℍ) {A B C : ℤ} (hA : 0 < A) (hC : 0 < C)
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    ∃ (M : ℕ) (_ : NeZero M) (s : Finset (Fin M × Fin M)), (0 : Fin M × Fin M) ∉ s ∧
      (M : ℂ) = (A : ℂ) * C ∧
      ∑ v ∈ s, (Lτ τ).weierstrassP ((Lτ τ).divPt M v) =
        (2 * (C : ℂ) * τ + B) * ((C : ℂ) * τ) * ((π : ℂ) ^ 2 / 3) * E₂star τ := by
  set M : ℕ := (A * C).toNat with hMdef
  have hMAC : (M : ℤ) = A * C := Int.toNat_of_nonneg (mul_pos hA hC).le
  have hM0 : 0 < M := cmM_pos hA hC hMAC
  haveI : NeZero M := ⟨hM0.ne'⟩
  obtain ⟨c, hc⟩ := exists_mulDiffCM_const hCM hA hC hMAC
  have hval := mulDiffCM_const_value hCM hA hC hMAC hc
  -- evaluate the constant multiplication formula at `z = 0`
  have h0 := hc 0
  rw [hval] at h0
  simp only [mulDiffCM] at h0
  rw [mul_zero, (Lτ τ).weierstrassP_zero, mul_zero, sub_zero] at h0
  simp only [zero_add] at h0
  rw [← Finset.add_sum_erase (cmSet B C M)
    (fun v => (Lτ τ).weierstrassP ((Lτ τ).divPt M v)) zero_mem_cmSet] at h0
  have hd0 : (Lτ τ).divPt M (0 : Fin M × Fin M) = 0 := by simp [PeriodPair.divPt]
  rw [hd0, (Lτ τ).weierstrassP_zero, zero_add] at h0
  -- combine with `lemkapa1`
  refine ⟨M, ⟨hM0.ne'⟩, (cmSet B C M).erase 0, Finset.notMem_erase _ _, ?_, ?_⟩
  · exact_mod_cast hMAC
  · rw [h0]
    have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hk := lemkapa1 hCM
    rw [kappa, div_eq_iff hτne] at hk
    have hMC : (M : ℂ) = (A : ℂ) * C := by exact_mod_cast hMAC
    linear_combination (-(C : ℂ)) * hk - (Lτ τ).eta₁ * hMC

end Lemkapa2

/-! ### The remaining analytic + combinatorial core

The following lemma is the paper's `lemkapa2`/`lemkapppppa` (the elliptic `ζ`-combination,
Laurent-residue argument via Liouville 1 and `theowpsum`) *rescaled* to the lattice `L̂` and
combined with `lemctau` (`DIV(Cτ) ⊂ DIV(AC)`, `|DIV(Cτ)| = AC − 1`).  It packages exactly
```
√D·(E₂*/η⁴)·(AC)² = (∑_{v ∈ DIV(Cτ)} AC·℘(v; L̂))·Cτbar
```
as an existential over the (nonzero) `AC`-division-point index set carrying the sum.
Everything else in `theoezweisternrest_of_isIntegral_j` is proved from it.

This is the sole remaining gap in Appendix B: it needs (i) the Laurent-coefficient
extraction for `ζ` at `z = 0` and (ii) the explicit `DIV(Cτ) ↪ DIV(AC)` embedding
(paper Lemma `lemctau`), neither of which is available in the current toolbox
(`theowpsum`/`theomwpu` in `DivisionValues.lean` are themselves pinned interfaces). -/
/-- **The raw identity over `L_τ`** (paper `lemkapppppa` at `ω₁ = 1`, i.e. `lemkapa1` = `lemkapa2`
combined with `lemctau`): there is an index set `s` of nonzero `AC`-division points — the image
of `DIV(Cτ)` under the embedding `DIV(Cτ) ↪ DIV(AC)` of Milla's `lemctau` — for which
`∑_{v ∈ s} ℘(v; L_τ) = √D·(Cτ)·(π²/3)·E₂*(τ)` (with `√D = 2Cτ + B`).

This is the sole remaining gap in Appendix B.  It is the analytic core:
* `lemkapa1` (proved: `κ = −√D·(π²/3)·E₂*`) together with
* `lemkapa2` (`Cτ·κ = −∑_{v ∈ DIV(Cτ)} ℘(v)`, provable by the `theowpsum`/`mulDiff` template in
  `DivisionValues.lean`: the elliptic `ζ`-combination `g` of Milla's `lemfellip`/`lemkonst` has
  vanishing derivative, whose `z → 0` limit — via `HasDerivAt L.weierstrassZeta (−℘)` and the
  pole-cancellation identities analogous to `mulPole_identity` — yields the sum), and
* `lemctau` (the modular-arithmetic embedding `DIV(Cτ) ↪ DIV(AC)`, `|DIV(Cτ)| = AC − 1`,
  giving `s` and `(M : ℂ) = AC`, hence `NeZero M`).

Everything downstream (`lemkapppppa_rescaled` and `theoezweisternrest_of_isIntegral_j`) is proved
from this. -/
private lemma lemkapa2_raw (τ : ℍ) {A B C : ℤ}
    (hgcd : Int.gcd (Int.gcd A B) C = 1)
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    ∃ (M : ℕ) (_ : NeZero M) (s : Finset (Fin M × Fin M)), (0 : Fin M × Fin M) ∉ s ∧
      (M : ℂ) = (A : ℂ) * C ∧
      ∑ v ∈ s, (Lτ τ).weierstrassP ((Lτ τ).divPt M v) =
        (2 * (C : ℂ) * τ + B) * ((C : ℂ) * τ) * ((π : ℂ) ^ 2 / 3) * E₂star τ := by
  -- Real and imaginary parts of the CM relation: `B = −2C·Re τ` and `A = C·|τ|²`.
  have him := (Complex.ext_iff.mp hCM).2
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.zero_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    pow_two, zero_mul, add_zero, zero_add] at him
  have hre := (Complex.ext_iff.mp hCM).1
  simp only [Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.zero_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    pow_two, zero_mul, sub_zero] at hre
  have hyR : (τ.im : ℝ) ≠ 0 := τ.im_ne_zero
  have hre2 : 2 * (C : ℝ) * τ.re + B = 0 := by
    have hfac : (τ.im : ℝ) * (2 * (C : ℝ) * τ.re + B) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hyR
    · exact h
  have hA_eq : (A : ℝ) = C * (τ.re ^ 2 + τ.im ^ 2) := by
    linear_combination hre - τ.re * hre2
  have hsq : (0 : ℝ) < τ.re ^ 2 + τ.im ^ 2 := by
    have h1 : (0 : ℝ) < τ.im := τ.im_pos
    positivity
  -- `C ≠ 0` (else `B = 0`, `A = 0`, contradicting `gcd = 1`)
  have hC0 : C ≠ 0 := by
    intro h
    have hB : (B : ℝ) = 0 := by rw [h] at hre2; push_cast at hre2; linarith
    have hA0 : (A : ℝ) = 0 := by rw [h] at hA_eq; push_cast at hA_eq; linarith
    have hBz : B = 0 := by exact_mod_cast hB
    have hAz : A = 0 := by exact_mod_cast hA0
    rw [hAz, hBz, h] at hgcd
    simp at hgcd
  rcases lt_or_gt_of_ne hC0 with hCneg | hCpos
  · -- `C < 0`: apply the positive case to `(−A, −B, −C)`; the statement is invariant.
    have hAneg : A < 0 := by
      have h1 : (A : ℝ) < 0 := by
        rw [hA_eq]; exact mul_neg_of_neg_of_pos (by exact_mod_cast hCneg) hsq
      exact_mod_cast h1
    have hCM' : ((-A : ℤ) : ℂ) + ((-B : ℤ) : ℂ) * τ + ((-C : ℤ) : ℂ) * (τ : ℂ) ^ 2 = 0 := by
      push_cast
      linear_combination -hCM
    obtain ⟨M, hne, s, hs0, hM, hsum⟩ :=
      lemkapa2_pos τ (by omega : 0 < -A) (by omega : 0 < -C) hCM'
    refine ⟨M, hne, s, hs0, ?_, ?_⟩
    · push_cast at hM ⊢
      linear_combination hM
    · push_cast at hsum ⊢
      linear_combination hsum
  · -- `C > 0`: then also `A > 0`.
    have hApos : 0 < A := by
      have h1 : (0 : ℝ) < (A : ℝ) := by
        rw [hA_eq]; exact mul_pos (by exact_mod_cast hCpos) hsq
      exact_mod_cast h1
    exact lemkapa2_pos τ hApos hCpos hCM

private lemma lemkapppppa_rescaled (τ : ℍ) {A B C : ℤ}
    (hgcd : Int.gcd (Int.gcd A B) C = 1)
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0) :
    ∃ (M : ℕ) (_ : NeZero M) (s : Finset (Fin M × Fin M)), (0 : Fin M × Fin M) ∉ s ∧
      (2 * (C : ℂ) * τ + B) * (E₂star τ / ModularForm.eta τ ^ 4) * ((A : ℂ) * C) ^ 2 =
        (∑ v ∈ s, (M : ℂ) *
            (latHatUnit τ • Lτ τ).weierstrassP ((latHatUnit τ • Lτ τ).divPt M v)) *
          ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) := by
  obtain ⟨M, hMne, s, hs0, hM, hraw⟩ := lemkapa2_raw τ hgcd hCM
  refine ⟨M, hMne, s, hs0, ?_⟩
  have hη : ModularForm.eta τ ≠ 0 := eta_ne_zero' τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : ((C : ℂ) * τ) * ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) = (A : ℂ) * C :=
    C_mul_conj_mul hCM
  -- Rescale each summand `℘(·; L̂)` to `℘(·; L_τ)` via `divPt_smul` and `weierstrassP_smul`.
  have hsum : (∑ v ∈ s, (M : ℂ) *
        (latHatUnit τ • Lτ τ).weierstrassP ((latHatUnit τ • Lτ τ).divPt M v)) =
      (M : ℂ) * ((latHatUnit τ : ℂ) ^ 2)⁻¹ *
        (∑ v ∈ s, (Lτ τ).weierstrassP ((Lτ τ).divPt M v)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [divPt_smul, PeriodPair.weierstrassP_smul]; ring
  rw [hsum, hraw, hM, latHatUnit_sq]
  rw [show ((A : ℂ) * C * ((π : ℂ) ^ 2 / 3 * ModularForm.eta τ ^ 4)⁻¹ *
        ((2 * (C : ℂ) * τ + B) * ((C : ℂ) * τ) * ((π : ℂ) ^ 2 / 3) * E₂star τ)) *
          ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)) =
      (A : ℂ) * C * ((π : ℂ) ^ 2 / 3 * ModularForm.eta τ ^ 4)⁻¹ * (2 * (C : ℂ) * τ + B) *
        ((π : ℂ) ^ 2 / 3) * E₂star τ * (((C : ℂ) * τ) * ((C : ℂ) * (starRingEnd ℂ) (τ : ℂ)))
      from by ring]
  rw [hprod]
  field_simp

/-- **Conditional form of `theoezweisternrest`** (the honest, provable statement): if
`j = 1728·J(τ)` is an algebraic integer, then so is `√D·(E₂*/η⁴)·(AC)²`.

This is the full content of Milla's `proofzweistern` *except* the CM input that `j(τ)` is an
algebraic integer.  For a general CM point that input is Silverman's theorem (PLAN Phase C,
`SingularModuli.lean`), which is only pinned here at `τ₁₆₃`; the unconditional
`theoezweisternrest` below therefore genuinely requires it (see the statement audit note). -/
theorem theoezweisternrest_of_isIntegral_j (τ : ℍ) {A B C : ℤ}
    (hgcd : Int.gcd (Int.gcd A B) C = 1)
    (hCM : (A : ℂ) + B * τ + C * (τ : ℂ) ^ 2 = 0)
    (hj : IsIntegral ℤ (1728 * J τ)) :
    IsIntegral ℤ ((2 * (C : ℂ) * τ + B) * (E₂star τ / ModularForm.eta τ ^ 4) *
      ((A : ℂ) * C) ^ 2) := by
  obtain ⟨M, hne, s, hs0, hid⟩ := lemkapppppa_rescaled τ hgcd hCM
  haveI : NeZero M := hne
  rw [hid]
  exact (isIntegral_sum_mul_weierstrassP_latHat τ hj M s hs0).mul (isIntegral_C_mul_conj hCM)

end Chudnovsky
