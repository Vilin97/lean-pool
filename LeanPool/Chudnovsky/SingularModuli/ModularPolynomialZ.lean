/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.ModularPolynomialQ
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# The modular polynomial `Φ_m ∈ ℤ[X, Y]` and Kronecker's lemma (Phase C, chunks B6–B7)

Fourth file of Track 1 of Phase C (see `Playground/Pi/PhaseC-PLAN.md`, §3.1 sub-lemmas
`(B6)`–`(B7)`). It refines the `ℚ`-coefficient modular polynomial of `ModularPolynomialQ.lean`
to a **`ℤ`-coefficient** one (needed for `m = 41`, the smallest usable index), and packages
Kronecker's unit-leading-coefficient lemma into the form `Integrality.lean` consumes.

## What is delivered

* **(ℤ[ζ_m] ∩ ℚ = ℤ)** `isInt_of_integral_of_rat` / `mem_bot_of_integral_of_rat`: a
  self-contained algebra tool — a complex number that is *both* rational and an algebraic
  integer lies in the image of `ℤ` (i.e. in the bottom subring `⊥ ⊆ ℂ`). This is the pointwise
  mechanism by which the `ℤ[ζ_m]`-integrality of the un-averaged `w`-expansion coefficients, once
  combined with the rationality of the *averaged* `q`-coefficients (the `(B3)`/`Sk_eq_poly_j`
  output), upgrades a coefficient from `ℚ` to `ℤ`. Provided now, standalone.

* **(B6)** `exists_PhiZ`: given that each coefficient of the orbit polynomial
  `∏_i (X − f_i τ)` is *cusp-meromorphic of finite order with coefficients in `⊥`* (the
  hypothesis `hZ`, mirroring the `hrat` gate of `ModularPolynomialQ.lean`'s `exists_PhiQ`, but
  with the integer subring `⊥` in place of a `ℚ`-subring — the `hrat`-closing machinery yields
  **both**, since the coefficient-tracking of `Sk_eq_poly_j` is generic in the subring `R`), the
  file produces `PhiZ : Polynomial (Polynomial ℤ)` with the keystone identity
  `∏_i (X − f_i τ) = Φ_m(X, j τ)` (`orbitPoly m τ = specializeZ (j τ) PhiZ`). The proof runs the
  *unconditional* `Sk_eq_poly_j_closed` at `R = ⊥` and lifts each `⊥`-coefficient polynomial to
  `ℤ`.

* **API for `Rationality.lean` / `MasserA1.lean` / `Integrality.lean`**:
  - `orbitPoly_eval_eq_prod` : `(∏_i (X − f_i τ)).eval z = ∏_i (z − f_i τ)`;
  - `PhiQ_eval_j_root` (the bridge `§4.2`/`§5` consume): if `j σ = f m i τ` for some coset
    index `i`, then `Φ_m(j σ, j τ) = 0` — one factor of the orbit product vanishes. Stated
    against an abstract `PhiQ` + its defining identity, so that plugging in the parallel agent's
    `exists_PhiQ_closed` is a three-line follow-up;
  - `diagPhiZ` and `diagPhiZ_map_eval` : the diagonal polynomial `G_m(X) := Φ_m(X, X) ∈ ℤ[X]`
    with `G_m(j τ) = ∏_i (j τ − f_i τ)`;
  - `isIntegral_of_kronecker` : the `(B9)` bridge — if `G_m` has leading coefficient `±1`
    (Kronecker) and `j τ` is a root of `G_m` (a CM relation), then `IsIntegral ℤ (j τ)`.

## Status of the two remaining deep inputs (zero `sorry`)

1. **DISCHARGED** (see the appended `w`-expansion section, `orbitPoly_coeff_isCuspMeroR_bot`,
   yielding `exists_PhiZ_closed`). The `⊥`-coefficient cusp-meromorphy hypothesis `hZ` of
   `exists_PhiZ` was originally taken as an argument; it is now closed unconditionally.
   Route (per `PhaseC-PLAN.md` §3.1 (B6)): each `q`-expansion coefficient of
   `(orbitPoly m τ).coeff n · qᴺ` is (i) rational — the `(B3)` root-of-unity averaging /
   `Sk_eq_poly_j` output, exactly the datum the parallel agent produces for `exists_PhiQ`; and
   (ii) an algebraic integer — the un-averaged `w = exp(2πiτ/m)`-expansion of each orbit piece
   `f_i` has coefficients in the subring `ℤ[ζ_m] ⊆ ℂ` (substitute `q ↦ ζ^{b}·wⁿ` into `jqInt`'s
   *integer* coefficients, `hasSum_f_some`/`hasSum_f_none` of `CosetOrbit.lean`), whose elements
   are integral over `ℤ` (`ζ_m` is a root of unity; the integral elements form a subring). By
   `mem_bot_of_integral_of_rat` each coefficient then lies in `⊥`. No Galois descent is used —
   this is the plan's main simplification (§6.6): rationality from averaging, integrality from
   ring closure, combined pointwise.

2. **(B7) Kronecker `G_m.leadingCoeff = ±1`** is taken as the hypothesis `hlead` of
   `isIntegral_of_kronecker`. Route (per `PhaseC-PLAN.md` §3.1 (B7); `m` non-square, here the
   prime `41`): the product `D(τ) = ∏_i (j τ − f_i τ) = G_m(j τ)` has a leading `q`-Laurent term
   computable from the `w`-expansions of `CosetOrbit.lean`. With `q = wᵐ`:
   `j ~ w^{-m}` (leading coeff `1`, from `jqInt.coeff 0 = 1`), `f_b ~ ζ^{-b} w^{-1}`
   (from `hasSum_f_some`, `jqInt.coeff 0 = 1`), `f_∞ ~ w^{-m²}` (from `hasSum_f_none`). As
   `m ≥ 2`: `j − f_b ~ w^{-m}` (leading coeff `1`) and `j − f_∞ ~ −w^{-m²}` (leading coeff
   `−1`); the product is `−w^{-2m²}·(1 + O(w)) = −q^{-2m}·(1 + …)`, so `D ~ −(j)^{2m}`. Since
   `G_m(j τ) = D(τ)` and `j` has a simple pole with leading coefficient `1`, matching the most
   negative `q`-powers gives `natDegree G_m = 2m` and `G_m.leadingCoeff = −1` (a `±1`, up to the
   sign bookkeeping `ζ^{−Σb} = ζ^{−m(m−1)/2} = 1` for `m` odd). Formalizing the leading-term
   extraction of the product `D` and matching against `∑ a_r (j)^r` is the `cuspLeadCoeff`-level
   work flagged in the plan (§6.3, "ModularPolynomialZ + Kronecker", medium risk). Everything
   *downstream* of `±1` (the monic-up-to-sign annihilator ⇒ `IsIntegral`) is proved here in full,
   so once the extraction lands, `hlead` is discharged and `Integrality.lean` closes.

The `(B8)` CM relation `∃ i, j τ₁₆₃ = f m i τ₁₆₃` that feeds both the root bridge and Kronecker
lives in `CMRelations.lean` (a two-line Möbius computation), consumed via `diagPhiZ_eval_eq_zero`
/ `PhiQ_eval_j_root`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm Finset Polynomial
open scoped Real Manifold MatrixGroups

variable {m : ℕ}

/-! ## (ℤ[ζ_m] ∩ ℚ = ℤ) : rational + algebraic-integer ⇒ integer

The self-contained algebra tool. A complex number that is rational and integral over `ℤ` is an
integer (`IsIntegrallyClosed` for `ℤ ⊆ ℚ`); packaged as membership in the bottom subring `⊥ ⊆ ℂ`
(which, by `Subring.mem_bot`, is exactly the image of `ℤ`). Re-derived from Mathlib here (the
identical fact is `private` in `Coefficients.lean`). -/

/-- **Rational algebraic integer is an integer.** If `x : ℂ` is integral over `ℤ` and equals a
rational `r`, then `x = (m : ℂ)` for some `m : ℤ`. -/
theorem isInt_of_integral_of_rat {x : ℂ} (hint : IsIntegral ℤ x) {r : ℚ}
    (hr : x = (r : ℂ)) : ∃ m : ℤ, x = (m : ℂ) := by
  have hinj : Function.Injective (algebraMap ℚ ℂ) := FaithfulSMul.algebraMap_injective ℚ ℂ
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ r) := by
    have hx : algebraMap ℚ ℂ r = x := by rw [hr]; simp
    rw [hx]; exact hint
  have h2 : IsIntegral ℤ r := (isIntegral_algebraMap_iff hinj).mp h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨n, by rw [hr, ← hn]; simp⟩

/-- **`ℤ[ζ_m] ∩ ℚ = ℤ`, packaged.** A complex number that is integral over `ℤ` (e.g. an element
of `ℤ[ζ_m]`) and rational lies in the bottom subring `⊥ ⊆ ℂ` (the image of `ℤ`). This is the
pointwise upgrade `ℚ`-coefficient ⇒ `ℤ`-coefficient of `(B6)`. -/
theorem mem_bot_of_integral_of_rat {x : ℂ} (hint : IsIntegral ℤ x)
    (hrat : ∃ r : ℚ, x = (r : ℂ)) : x ∈ (⊥ : Subring ℂ) := by
  obtain ⟨r, hr⟩ := hrat
  obtain ⟨n, hn⟩ := isInt_of_integral_of_rat hint hr
  exact Subring.mem_bot.mpr ⟨n, hn.symm⟩

/-! ## Lifting `⊥`-coefficient complex polynomials to `ℤ`

A `Polynomial ℂ` all of whose coefficients lie in `⊥` (i.e. are integers) is the image of a
`Polynomial ℤ` under `Int.castRingHom ℂ`. -/

/-- If every coefficient of `P : ℂ[X]` lies in `⊥` (is an integer), then `P = Q.map (ℤ → ℂ)` for
some `Q : ℤ[X]`. -/
theorem exists_intPoly_of_coeff_mem_bot {P : Polynomial ℂ}
    (hP : ∀ i, P.coeff i ∈ (⊥ : Subring ℂ)) :
    ∃ Q : Polynomial ℤ, P = Q.map (Int.castRingHom ℂ) := by
  choose c hc using fun i ↦ Subring.mem_bot.mp (hP i)
  -- `hc i : (c i : ℂ) = P.coeff i`
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), C (c i) * X ^ i, ?_⟩
  have hQcoeff : ∀ k : ℕ,
      (∑ i ∈ Finset.range (P.natDegree + 1), C (c i) * X ^ i).coeff k
        = if k < P.natDegree + 1 then c k else 0 := by
    intro k
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
  ext k
  rw [coeff_map, hQcoeff]
  by_cases hk : k < P.natDegree + 1
  · rw [if_pos hk, eq_intCast (Int.castRingHom ℂ) (c k)]
    exact (hc k).symm
  · rw [if_neg hk, map_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## (B6) The modular polynomial `Φ_m ∈ ℤ[Y][X]`

The `ℤ`-analogue of `ModularPolynomialQ.lean`'s `specializeY` / `exists_PhiQ`. -/

/-- Specialization of a `ℤ[Y][X]`-polynomial at `Y = Y₀ ∈ ℂ`: map each `ℤ[Y]`-coefficient to its
value at `Y₀` under `ℤ → ℂ`, landing in `ℂ[X]`. Applied at `Y₀ = j τ` this is `Φ_m(X, j τ)`. -/
def specializeZ (Y₀ : ℂ) : Polynomial (Polynomial ℤ) →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) Y₀)

/-- Per-coefficient `ℤ`-refinement: assuming the coefficient `(orbitPoly m τ).coeff n` is
cusp-meromorphic of finite order with coefficients in `⊥`, it equals a `ℤ`-polynomial in `j τ`.
Uses the unconditional `Sk_eq_poly_j_closed` at `R = ⊥` and lifts the resulting `⊥`-coefficient
polynomial to `ℤ`. -/
theorem orbitPoly_coeff_intPoly [Fact m.Prime]
    (hZ : ∀ n : ℕ, ∃ N : ℕ,
      IsCuspMeroR (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) N (⊥ : Subring ℂ))
    (n : ℕ) :
    ∃ Q : Polynomial ℤ, ∀ τ : ℍ,
      (orbitPoly m τ).coeff n = Q.eval₂ (Int.castRingHom ℂ) (j τ) := by
  obtain ⟨N, hmero⟩ := hZ n
  obtain ⟨P, hPmem, _, hPeval⟩ :=
    Sk_eq_poly_j_closed N (⊥ : Subring ℂ) (fun τ : ℍ ↦ (orbitPoly m τ).coeff n)
      (fun γ τ ↦ congrArg (fun p : Polynomial ℂ ↦ p.coeff n) (orbitPoly_smul γ τ))
      (mdifferentiable_orbitPoly_coeff n) hmero
  obtain ⟨Q, hQ⟩ := exists_intPoly_of_coeff_mem_bot hPmem
  refine ⟨Q, fun τ ↦ ?_⟩
  rw [hPeval τ, hQ, eval_map]

/-- **(B6) The modular polynomial `Φ_m ∈ ℤ[Y][X]`.** Given the `⊥`-coefficient cusp-meromorphy of
every orbit-polynomial coefficient (`hZ`), there is `PhiZ : Polynomial (Polynomial ℤ)` with the
keystone identity `∏_i (X − f_i τ) = Φ_m(X, j τ)` for every `τ`. This is the object consumed by
`Integrality.lean` (through `diagPhiZ` / Kronecker). -/
theorem exists_PhiZ [Fact m.Prime]
    (hZ : ∀ n : ℕ, ∃ N : ℕ,
      IsCuspMeroR (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) N (⊥ : Subring ℂ)) :
    ∃ PhiZ : Polynomial (Polynomial ℤ),
      ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  choose Q hQ using orbitPoly_coeff_intPoly hZ
  refine ⟨∑ n ∈ Finset.range (m + 2), C (Q n) * X ^ n, ?_⟩
  have hPcoeff : ∀ k : ℕ, (∑ n ∈ Finset.range (m + 2), C (Q n) * X ^ n).coeff k
      = if k < m + 2 then Q k else 0 := by
    intro k
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
  intro τ
  ext k
  rw [specializeZ, coe_mapRingHom, coeff_map, hPcoeff]
  by_cases hk : k < m + 2
  · rw [if_pos hk, coe_eval₂RingHom]
    exact hQ k τ
  · rw [if_neg hk, map_zero]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (orbitPoly_natDegree_le τ) (by omega))

/-! ## Evaluation of the orbit polynomial and the root bridge

The keystone identity `orbitPoly m τ = Φ_m(X, j τ)` turns coset coincidences `j σ = f_i τ` into
roots `Φ_m(j σ, j τ) = 0`. Stated against an abstract `PhiQ` + its defining property (so the
parallel agent's `exists_PhiQ_closed`, of the same shape as `exists_PhiQ`, discharges it in three
lines), and mirrored for `PhiZ`. -/

/-- Evaluating the orbit polynomial at `z : ℂ` gives the product `∏_i (z − f_i τ)`. -/
theorem orbitPoly_eval_eq_prod [NeZero m] (τ : ℍ) (z : ℂ) :
    (orbitPoly m τ).eval z = ∏ i : Option (ZMod m), (z - f m i τ) := by
  rw [orbitPoly, eval_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [eval_sub, eval_X, eval_C]

/-- If `j σ = f m i τ` for some coset index `i`, then `j σ` is a root of the orbit polynomial
`∏_i (X − f_i τ)`. -/
theorem orbitPoly_eval_eq_zero [NeZero m] {τ σ : ℍ} {i : Option (ZMod m)}
    (h : j σ = f m i τ) : (orbitPoly m τ).eval (j σ) = 0 := by
  rw [orbitPoly_eval_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, sub_self])

/-- **The root bridge (`§4.2`/`§5`), `ℚ`-version.** If `j σ` coincides with some coset value
`f m i τ` (a CM relation), then `Φ_m(j σ, j τ) = 0`. Consumed by `Rationality.lean` (`C2`, applied
under a field embedding `σ : ℚ(j₀) → ℂ`) and `MasserA1.lean` (`F(z) = Φ₁₆₃(j(Λz), j z) ≡ 0`).

Stated against an abstract `PhiQ : Polynomial (Polynomial ℚ)` together with its defining identity
`hPhiQ` — exactly the pair produced by `ModularPolynomialQ.exists_PhiQ`; supply the parallel
agent's `exists_PhiQ_closed` to obtain it unconditionally. -/
theorem PhiQ_eval_j_root [NeZero m] (PhiQ : Polynomial (Polynomial ℚ))
    (hPhiQ : ∀ τ : ℍ, orbitPoly m τ = specializeY (j τ) PhiQ)
    {τ σ : ℍ} {i : Option (ZMod m)} (h : j σ = f m i τ) :
    (specializeY (j τ) PhiQ).eval (j σ) = 0 := by
  rw [← hPhiQ τ]; exact orbitPoly_eval_eq_zero h

/-! ## (B7) The diagonal polynomial `G_m(X) = Φ_m(X, X)` and Kronecker's lemma -/

/-- The diagonal polynomial `G_m(X) := Φ_m(X, X) ∈ ℤ[X]`, obtained by substituting the coefficient
variable `Y` by the outer variable `X` (evaluating the outer `PhiZ` at `X : ℤ[X]`). -/
def diagPhiZ (PhiZ : Polynomial (Polynomial ℤ)) : Polynomial ℤ :=
  PhiZ.eval (X : Polynomial ℤ)

/-- The diagonal substitution commutes with `Y ↦ z`: evaluating `G_m` (mapped to `ℂ`) at `z`
equals evaluating `Φ_m(X, z)` at `z`. Both are the two ways to compute `Φ_m(z, z)`. -/
theorem diag_eval₂_eq (PhiZ : Polynomial (Polynomial ℤ)) (z : ℂ) :
    (PhiZ.eval (X : Polynomial ℤ)).eval₂ (Int.castRingHom ℂ) z
      = (specializeZ z PhiZ).eval z := by
  have key : (eval₂RingHom (Int.castRingHom ℂ) z).comp (evalRingHom (X : Polynomial ℤ))
      = eval₂RingHom (eval₂RingHom (Int.castRingHom ℂ) z) z := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom, eval_C, eval₂_C]
    · simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom, eval_X, eval₂_X]
  have h := DFunLike.congr_fun key PhiZ
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom] at h
  rw [specializeZ, coe_mapRingHom, eval_map]
  exact h

/-- **`G_m(j τ) = ∏_i (j τ − f_i τ)`.** Evaluating the diagonal polynomial (mapped to `ℂ`) at
`j τ` recovers the orbit product. The bridge Kronecker / `Integrality.lean` extract from. -/
theorem diagPhiZ_map_eval [NeZero m] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhiZ : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ) (τ : ℍ) :
    (diagPhiZ PhiZ).eval₂ (Int.castRingHom ℂ) (j τ) = ∏ i : Option (ZMod m), (j τ - f m i τ) := by
  rw [diagPhiZ, diag_eval₂_eq, ← hPhiZ τ, orbitPoly_eval_eq_prod]

/-- **The diagonal CM root.** If `j τ = f m i τ` for some coset index `i` (a fixing relation at a
CM point), then `j τ` is a root of `G_m` (mapped to `ℂ`). Combined with Kronecker's `±1` leading
coefficient this yields integrality. -/
theorem diagPhiZ_eval_eq_zero [NeZero m] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhiZ : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ)
    {τ : ℍ} {i : Option (ZMod m)} (h : j τ = f m i τ) :
    (diagPhiZ PhiZ).eval₂ (Int.castRingHom ℂ) (j τ) = 0 := by
  rw [diagPhiZ_map_eval hPhiZ]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, sub_self])

/-- **(B9) The integrality bridge.** If `G_m = Φ_m(X, X)` has leading coefficient `±1`
(Kronecker's lemma, `(B7)` — the gated input, see the module `TODO`) and `j τ` is a root of `G_m`
(a CM relation `(B8)`, from `CMRelations.lean` via `diagPhiZ_eval_eq_zero`), then `j τ` is
integral over `ℤ`. This is exactly the shape `Integrality.lean` needs for `isIntegral_j_τ₁₆₃` at
`m = 41`. The `±1` monic-up-to-sign annihilator argument is proved here in full. -/
theorem isIntegral_of_kronecker [NeZero m] {PhiZ : Polynomial (Polynomial ℤ)}
    (hlead : (diagPhiZ PhiZ).leadingCoeff = 1 ∨ (diagPhiZ PhiZ).leadingCoeff = -1)
    {τ : ℍ}
    (hroot : (diagPhiZ PhiZ).eval₂ (Int.castRingHom ℂ) (j τ) = 0) :
    IsIntegral ℤ (j τ) := by
  rcases hlead with h1 | h1
  · refine ⟨diagPhiZ PhiZ, h1, ?_⟩
    rw [algebraMap_int_eq]; exact hroot
  · refine ⟨-(diagPhiZ PhiZ), ?_, ?_⟩
    · change (-(diagPhiZ PhiZ)).leadingCoeff = 1
      rw [leadingCoeff_neg, h1]; norm_num
    · rw [algebraMap_int_eq, eval₂_neg, hroot, neg_zero]

end Chudnovsky

/-! ## Discharging the `hZ` gate of `exists_PhiZ`: the `w`-expansion integrality machinery

This appended section closes the `hZ` hypothesis of `exists_PhiZ` unconditionally, yielding
`exists_PhiZ_closed`. Each `q`-coefficient of `(orbitPoly m τ).coeff n · qᴺ` is (i) **rational**
(the `ℚ`-averaging of `ModularPolynomialQ.lean`, via a generic `qExpansion`-ring-hom toolkit
`GoodQ`) and (ii) an **algebraic integer** (the un-averaged width-`m` `w = wParam m`-expansion of
`∏_i (X − f_i)` has coefficients in `ℤ[ζ_m]`, matched to the `q`-coefficient at index `m·p` by
a width-`m` uniqueness argument). By `mem_bot_of_integral_of_rat` each coefficient lies in `⊥`. -/

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm Finset Polynomial
open scoped Real Manifold MatrixGroups

variable {m : ℕ}


/-- Cusp-analytic with q-expansion coefficients in `R`, at width `h`. -/
structure GoodQ (h : ℝ) (R : Subring ℂ) (g : ℍ → ℂ) : Prop where
  per : Function.Periodic (g ∘ ofComplex) h
  holo : MDiff g
  bdd : IsBoundedAtImInfty g
  mem : ∀ n, (qExpansion h g).coeff n ∈ R

lemma GoodQ.ana {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g : ℍ → ℂ} (hg : GoodQ h R g) :
    AnalyticAt ℂ (cuspFunction h g) 0 :=
  analyticAt_cuspFunction_zero hh hg.per hg.holo hg.bdd

lemma GoodQ.add {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g₁ g₂ : ℍ → ℂ}
    (h₁ : GoodQ h R g₁) (h₂ : GoodQ h R g₂) : GoodQ h R (fun τ ↦ g₁ τ + g₂ τ) where
  per := by
    have := h₁.per.add h₂.per; simpa [Function.comp_def] using this
  holo := h₁.holo.add h₂.holo
  bdd := h₁.bdd.add h₂.bdd
  mem n := by
    have : (fun τ ↦ g₁ τ + g₂ τ) = g₁ + g₂ := rfl
    rw [this, qExpansion_add (h₁.ana hh) (h₂.ana hh), map_add]
    exact R.add_mem (h₁.mem n) (h₂.mem n)

lemma GoodQ.mul {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g₁ g₂ : ℍ → ℂ}
    (h₁ : GoodQ h R g₁) (h₂ : GoodQ h R g₂) : GoodQ h R (fun τ ↦ g₁ τ * g₂ τ) where
  per := by
    have := h₁.per.mul h₂.per; simpa [Function.comp_def] using this
  holo := h₁.holo.mul h₂.holo
  bdd := h₁.bdd.mul h₂.bdd
  mem n := by
    have : (fun τ ↦ g₁ τ * g₂ τ) = g₁ * g₂ := rfl
    rw [this, qExpansion_mul (h₁.ana hh) (h₂.ana hh), PowerSeries.coeff_mul]
    exact R.sum_mem (fun p _ ↦ R.mul_mem (h₁.mem p.1) (h₂.mem p.2))

lemma goodQ_one {h : ℝ} (_hh : 0 < h) {R : Subring ℂ} : GoodQ h R (fun _ : ℍ ↦ (1:ℂ)) where
  per := by simp
  holo := mdifferentiable_const
  bdd := Filter.const_boundedAtFilter atImInfty (1 : ℂ)
  mem n := by
    have h1 : (fun _ : ℍ ↦ (1:ℂ)) = (1 : ℍ → ℂ) := rfl
    rw [h1, qExpansion_one]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [PowerSeries.coeff_one, if_neg hn]; exact R.zero_mem

lemma goodQ_smul {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g : ℍ → ℂ} (hg : GoodQ h R g)
    {c : ℂ} (hc : c ∈ R) : GoodQ h R (fun τ ↦ c * g τ) where
  per := fun z ↦ by
    change c * (g ∘ ofComplex) (z + h) = c * (g ∘ ofComplex) z
    rw [hg.per z]
  holo := mdifferentiable_const.mul hg.holo
  bdd := hg.bdd.const_mul_left c
  mem n := by
    have he : (fun τ ↦ c * g τ) = c • g := by funext τ; simp [Pi.smul_apply, smul_eq_mul]
    rw [he, qExpansion_smul (hg.ana hh) c, PowerSeries.coeff_smul, smul_eq_mul]
    exact R.mul_mem hc (hg.mem n)

lemma goodQ_const {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) :
    GoodQ h R (fun _ : ℍ ↦ c) := by
  have := goodQ_smul hh (goodQ_one hh (R := R)) hc
  simpa using this

lemma GoodQ.neg {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g : ℍ → ℂ} (hg : GoodQ h R g) :
    GoodQ h R (fun τ ↦ - g τ) := by
  have := goodQ_smul hh hg (c := -1) (R.neg_mem R.one_mem)
  simpa using this

lemma GoodQ.sub {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g₁ g₂ : ℍ → ℂ}
    (h₁ : GoodQ h R g₁) (h₂ : GoodQ h R g₂) : GoodQ h R (fun τ ↦ g₁ τ - g₂ τ) := by
  have := h₁.add hh (h₂.neg hh)
  simpa [sub_eq_add_neg] using this

/-- `wParam` is holomorphic. -/
lemma mdifferentiable_wParam : MDiff (fun τ : ℍ ↦ wParam m τ) := by
  have heq : (fun τ : ℍ ↦ wParam m τ)
      = (fun z : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * z / m)) ∘ (fun τ : ℍ ↦ (τ : ℂ)) := by
    funext τ; simp [wParam, Function.comp]
  rw [heq]
  exact Differentiable.comp_mdifferentiable (by fun_prop) mdifferentiable_coe

/-- `(j·q)^k` is bounded at `i∞` (public, via the identity isogeny). -/
lemma isBoundedAtImInfty_jqPow (k : ℕ) :
    IsBoundedAtImInfty (fun τ : ℍ ↦ (j τ * q τ) ^ k) := by
  have hA : (1 : GL (Fin 2) ℝ) 1 0 = 0 := by
    simp [Matrix.one_apply_ne]
  have h := isBoundedAtImInfty_jqPow_comp k 1 hA
  simpa only [one_smul] using h

/-- `q` is bounded at `i∞`. -/
lemma isBoundedAtImInfty_q : IsBoundedAtImInfty (fun τ : ℍ ↦ q τ) :=
  (qParam_tendsto_atImInfty one_pos).isBigO_one ℝ

/-- Powers preserve `GoodQ`. -/
lemma GoodQ.pow {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {g : ℍ → ℂ} (hg : GoodQ h R g) :
    ∀ k : ℕ, GoodQ h R (fun τ ↦ g τ ^ k)
  | 0 => by simpa using goodQ_one hh (R := R)
  | (k+1) => by
    have := (hg.pow hh k).mul hh hg
    simpa [pow_succ] using this

lemma goodQ_q (R : Subring ℂ) : GoodQ 1 R (fun τ : ℍ ↦ q τ) where
  per := periodic_comp_ofComplex_of_vadd q_vadd_one
  holo := mdifferentiable_q
  bdd := isBoundedAtImInfty_q
  mem n := by
    have hHS : ∀ τ : ℍ, HasSum (fun k ↦ (if k = 1 then (1:ℂ) else 0) • q τ ^ k) (q τ) := by
      intro τ
      have := hasSum_ite_eq (1 : ℕ) (q τ)
      refine this.congr_fun (fun k ↦ ?_)
      by_cases hk : k = 1
      · subst hk; simp
      · simp [hk]
    have := qExpansion_coeff_unique_raw
      (analyticAt_cuspFunction_zero one_pos (periodic_comp_ofComplex_of_vadd q_vadd_one)
        mdifferentiable_q isBoundedAtImInfty_q)
      (periodic_comp_ofComplex_of_vadd q_vadd_one) mdifferentiable_q isBoundedAtImInfty_q hHS n
    rw [← this]
    by_cases hn : n = 1
    · rw [if_pos hn]; exact R.one_mem
    · rw [if_neg hn]; exact R.zero_mem

lemma goodQ_jq (R : Subring ℂ) : GoodQ 1 R (fun τ : ℍ ↦ j τ * q τ) where
  per := periodic_comp_ofComplex_of_vadd (fun τ ↦ by rw [j_vadd_one, q_vadd_one])
  holo := mdifferentiable_j_mul_q
  bdd := by simpa using isBoundedAtImInfty_jqPow 1
  mem n := by
    rw [qExpansion_j_mul_q, PowerSeries.coeff_map, eq_intCast (Int.castRingHom ℂ)]
    exact intCast_mem R _

lemma GoodQ.of_eq {h : ℝ} {R : Subring ℂ} {g g' : ℍ → ℂ} (hg : GoodQ h R g)
    (he : ∀ τ, g' τ = g τ) : GoodQ h R g' := by
  have : g' = g := funext he; rw [this]; exact hg

lemma goodQ_sum {h : ℝ} (hh : 0 < h) {R : Subring ℂ} {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (hg : ∀ i ∈ s, GoodQ h R (g i)) : GoodQ h R (fun τ ↦ ∑ i ∈ s, g i τ) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using goodQ_const hh (R := R) R.zero_mem
  | @insert a s ha ih =>
    have hrw : (fun τ ↦ ∑ i ∈ insert a s, g i τ)
        = (fun τ ↦ g a τ + ∑ i ∈ s, g i τ) := by
      funext τ; rw [Finset.sum_insert ha]
    rw [hrw]
    exact (hg a (Finset.mem_insert_self a s)).add hh
      (ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)))

/-- **Rationality of the orbit-polynomial coefficients (structure + `ℚ`-coefficients).**
If `(orbitPoly m τ).coeff n = aeval (j τ) P` for a `ℚ`-polynomial `P` of degree `≤ N`, then that
coefficient is cusp-meromorphic of pole order `≤ N` with `ℚ`-coefficients. -/
lemma orbitPoly_coeff_isCuspMeroR_RQ [NeZero m] (n : ℕ) (P : Polynomial ℚ)
    (hP : ∀ τ : ℍ, (orbitPoly m τ).coeff n = aeval (j τ) P) (N : ℕ) (hN : P.natDegree ≤ N) :
    IsCuspMeroR (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) N RQ := by
  have hsummand : ∀ k, GoodQ 1 RQ
      (fun τ ↦ ((P.coeff k : ℚ) : ℂ) * ((j τ * q τ) ^ k * q τ ^ (N - k))) := by
    intro k
    refine goodQ_smul one_pos ?_ (RingHom.mem_range.mpr ⟨P.coeff k, rfl⟩)
    exact ((goodQ_jq RQ).pow one_pos k).mul one_pos ((goodQ_q RQ).pow one_pos (N - k))
  have hgood : GoodQ 1 RQ (fun τ ↦ (orbitPoly m τ).coeff n * q τ ^ N) := by
    refine (goodQ_sum one_pos (Finset.range (N + 1)) _ (fun k _ ↦ hsummand k)).of_eq (fun τ ↦ ?_)
    rw [hP τ, aeval_def, eval₂_eq_sum_range' (algebraMap ℚ ℂ) (Nat.lt_succ_of_le hN),
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k hk ↦ ?_)
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcast : algebraMap ℚ ℂ (P.coeff k) = ((P.coeff k : ℚ) : ℂ) := by simp
    have hdist : (j τ) ^ k * q τ ^ N = (j τ * q τ) ^ k * q τ ^ (N - k) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hk']
    rw [hcast, mul_assoc, hdist]
  exact ⟨hgood.per, hgood.holo, hgood.bdd, hgood.mem⟩

/-- The base variable `w = wParam m τ` is the width-`m` `q`-parameter. -/
lemma wParam_eq_qParam (τ : ℍ) : wParam m τ = Function.Periodic.qParam (m : ℝ) (τ:ℂ) := by
  rw [wParam, Function.Periodic.qParam]; push_cast; ring_nf

/-- **Width-`m` raw `w`-expansion coefficient uniqueness** (mirrors `qExpansion_coeff_unique_raw`
at width `m`, with `w = wParam m` in place of `q`). -/
lemma wExpansion_coeff_unique_raw [NeZero m] {F : ℍ → ℂ} {c : ℕ → ℂ}
    (hFan : AnalyticAt ℂ (cuspFunction (m : ℝ) F) 0)
    (hFper : Function.Periodic (F ∘ ofComplex) (m : ℝ)) (hFholo : MDiff F)
    (hFbdd : IsBoundedAtImInfty F)
    (hF : ∀ τ : ℍ, HasSum (fun n ↦ c n • wParam m τ ^ n) (F τ)) (n : ℕ) :
    c n = (qExpansion (m : ℝ) F).coeff n := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hF' : ∀ τ : ℍ, HasSum (fun n ↦ c n • Function.Periodic.qParam (m : ℝ) (τ:ℂ) ^ n) (F τ) := by
    intro τ; simpa only [wParam_eq_qParam] using hF τ
  have hball1 := hasFPowerSeriesOnBall_cuspFunction hm hFan hF'
  have hsum2 : ∀ τ : ℍ,
      HasSum (fun k ↦ (qExpansion (m : ℝ) F).coeff k • Function.Periodic.qParam (m : ℝ) (τ:ℂ) ^ k)
        (F τ) := hasSum_qExpansion hm hFper hFholo hFbdd
  have hball2 := hasFPowerSeriesOnBall_cuspFunction hm hFan hsum2
  have heq := hball1.hasFPowerSeriesAt.eq_formalMultilinearSeries hball2.hasFPowerSeriesAt
  have hcoeff := congr_arg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) heq
  simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff

/-! ## Width-`m` machinery: algebraic integrality of the `w`-expansion -/

/-- The subring of algebraic integers `ℤbar ⊆ ℂ`. -/
def RI : Subring ℂ := (integralClosure ℤ ℂ).toSubring

lemma mem_RI_iff {x : ℂ} : x ∈ RI ↔ IsIntegral ℤ x := by
  rw [RI, Subalgebra.mem_toSubring]; exact mem_integralClosure_iff ℤ ℂ

lemma intCast_mem_RI (n : ℤ) : (n : ℂ) ∈ RI := intCast_mem RI n

/-- Roots of unity are algebraic integers: `ζ_m ∈ ℤbar`. -/
lemma zetaM_mem_RI [NeZero m] : zetaM m ∈ RI := by
  rw [mem_RI_iff]
  refine ⟨X ^ m - C 1, monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
  simp [zetaM_pow_m]

lemma zetaM_zpow_mem_RI [NeZero m] (n : ℤ) : zetaM m ^ n ∈ RI := by
  rw [mem_RI_iff]
  refine ⟨X ^ m - C 1, monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
  have hpow : (zetaM m ^ n) ^ m = 1 := by
    rw [← zpow_natCast (zetaM m ^ n) m, ← zpow_mul]
    exact (zetaM_zpow_eq_one_iff (n * (m : ℤ))).mpr ⟨n, by ring⟩
  simp [hpow]

/-- General period-`p` version of `periodic_comp_ofComplex_of_vadd`. -/
lemma periodic_comp_ofComplex_of_vadd_gen {f : ℍ → ℂ} {p : ℝ} (_hp : 0 < p)
    (hf : ∀ τ : ℍ, f ((p : ℝ) +ᵥ τ) = f τ) : Function.Periodic (f ∘ ofComplex) p := by
  intro w
  rcases lt_or_ge 0 w.im with hw | hw
  · have himeq : (w + (p:ℂ)).im = w.im := by simp
    have hw1 : 0 < (w + (p:ℂ)).im := by rw [himeq]; exact hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    have h := hf ⟨w, hw⟩
    convert h using 2
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]; simp [add_comm]
  · have hw1 : (w + (p:ℂ)).im ≤ 0 := by
      simp only [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
    simp only [Function.comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hw1 (by simpa using hw)]

lemma wParam_vadd_m [NeZero m] (τ : ℍ) : wParam m ((m : ℝ) +ᵥ τ) = wParam m τ := by
  have hm : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [wParam, wParam, UpperHalfPlane.coe_vadd,
    show 2*↑π*Complex.I*(((m : ℝ):ℂ)+↑τ)/m = 2*↑π*Complex.I + 2*↑π*Complex.I*↑τ/m by
      field_simp; push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

lemma f_vadd_m [NeZero m] (i : Option (ZMod m)) (τ : ℍ) :
    f m i ((m : ℝ) +ᵥ τ) = f m i τ := by
  have hm : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  cases i with
  | none =>
    simp only [f_none]
    have hpt : AInf m • ((m : ℝ) +ᵥ τ) = ((m^2 : ℕ) : ℝ) +ᵥ (AInf m • τ) := by
      apply UpperHalfPlane.ext
      simp only [coe_AInf_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hpt]; exact_mod_cast j_vadd_int (m^2 : ℕ) (AInf m • τ)
  | some b =>
    simp only [f_some]
    have hpt : Acol m b.val • ((m : ℝ) +ᵥ τ) = ((1:ℕ):ℝ) +ᵥ (Acol m b.val • τ) := by
      apply UpperHalfPlane.ext
      simp only [coe_Acol_smul, UpperHalfPlane.coe_vadd]; push_cast; field_simp; ring
    rw [hpt]; exact_mod_cast j_vadd_int (1 : ℕ) (Acol m b.val • τ)

lemma isBoundedAtImInfty_wParam [NeZero m] : IsBoundedAtImInfty (fun τ : ℍ ↦ wParam m τ) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have ht : Filter.Tendsto (fun τ : ℍ ↦ wParam m τ) atImInfty (nhds 0) := by
    simpa only [wParam_eq_qParam] using qParam_tendsto_atImInfty (h := (m : ℝ)) hm
  exact ht.isBigO_one ℝ

/-- Reindexing helper: a function with a `w`-expansion supported on the (injective) image of `e`
with `ℤbar`-coefficients is `GoodQ` at width `m` over `ℤbar`. -/
lemma goodQ_of_wHasSum [NeZero m] {F : ℍ → ℂ} {a : ℕ → ℂ} {e : ℕ → ℕ}
    (hpe : Function.Periodic (F ∘ ofComplex) (m : ℝ)) (hho : MDiff F) (hbd : IsBoundedAtImInfty F)
    (hei : Function.Injective e) (ha : ∀ n, a n ∈ RI)
    (hHS : ∀ τ : ℍ, HasSum (fun n ↦ a n • wParam m τ ^ (e n)) (F τ)) :
    GoodQ (m : ℝ) RI F := by
  classical
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set b : ℕ → ℂ := Function.extend e a (fun _ ↦ 0) with hb
  have hbmem : ∀ t, b t ∈ RI := by
    intro t
    by_cases ht : ∃ n, e n = t
    · obtain ⟨n, rfl⟩ := ht
      rw [hb, hei.extend_apply]; exact ha n
    · rw [hb, Function.extend_apply' _ _ _ (by rintro ⟨n, rfl⟩; exact ht ⟨n, rfl⟩)]
      exact RI.zero_mem
  have hHS' : ∀ τ : ℍ, HasSum (fun t ↦ b t • wParam m τ ^ t) (F τ) := by
    intro τ
    have hz : ∀ t ∉ Set.range e, (fun t ↦ b t • wParam m τ ^ t) t = 0 := by
      intro t ht
      have hbt : b t = 0 := by
        rw [hb, Function.extend_apply' _ _ _ (fun ⟨n, hn⟩ ↦ ht ⟨n, hn⟩)]
      change b t • wParam m τ ^ t = 0
      rw [hbt, zero_smul]
    rw [← hei.hasSum_iff hz]
    refine (hHS τ).congr_fun (fun n ↦ ?_)
    simp only [Function.comp_apply, hb, hei.extend_apply]
  have hFan : AnalyticAt ℂ (cuspFunction (m : ℝ) F) 0 :=
    analyticAt_cuspFunction_zero hm hpe hho hbd
  exact ⟨hpe, hho, hbd, fun n ↦ by
    rw [← wExpansion_coeff_unique_raw hFan hpe hho hbd hHS' n]; exact hbmem n⟩

/-- `G_∞ = f_∞ · w^{m²}` is `GoodQ` at width `m` over `ℤbar` (its `w`-expansion has integer
coefficients). -/
lemma goodQ_G_none [NeZero m] :
    GoodQ (m : ℝ) RI (fun τ : ℍ ↦ f m none τ * wParam m τ ^ (m ^ 2)) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hval : ∀ τ : ℍ,
      f m none τ * wParam m τ ^ (m ^ 2) = (j (AInf m • τ) * q (AInf m • τ)) ^ 1 := by
    intro τ
    have h := Fi_none_eq (m := m) 1 τ
    rw [mul_one] at h
    rw [show wParam m τ ^ (m ^ 2) = q τ ^ m by
      have := wParam_pow_mk (m := m) 1 τ; rwa [mul_one, mul_one] at this]
    simpa using h
  have hpe : Function.Periodic ((fun τ : ℍ ↦ f m none τ * wParam m τ ^ (m ^ 2)) ∘ ofComplex)
      (m : ℝ) :=
    periodic_comp_ofComplex_of_vadd_gen hm (fun τ ↦ by rw [f_vadd_m, wParam_vadd_m])
  have hho : MDiff (fun τ : ℍ ↦ f m none τ * wParam m τ ^ (m ^ 2)) :=
    (mdifferentiable_f none).mul (mdifferentiable_wParam.pow (m ^ 2))
  have hbd : IsBoundedAtImInfty (fun τ : ℍ ↦ f m none τ * wParam m τ ^ (m ^ 2)) := by
    rw [funext hval]
    exact isBoundedAtImInfty_jqPow_comp 1 (AInf m) (by simp [val_AInf])
  refine goodQ_of_wHasSum hpe hho hbd (e := fun n ↦ m ^ 2 * n)
    (a := fun n ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ))
    (fun a b hab ↦ Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) 2) hab)
    (fun n ↦ intCast_mem_RI _) (fun τ ↦ ?_)
  have h := hasSum_f_none (m := m) τ
  refine h.congr_fun (fun n ↦ ?_)
  rw [smul_eq_mul, ← pow_mul]

/-- `G_b = f_b · w^{m²}` is `GoodQ` at width `m` over `ℤbar` (its `w`-expansion has `ℤ[ζ_m]`
coefficients). -/
lemma goodQ_G_some [NeZero m] (b : ZMod m) :
    GoodQ (m : ℝ) RI (fun τ : ℍ ↦ f m (some b) τ * wParam m τ ^ (m ^ 2)) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hw2 : ∀ τ : ℍ, wParam m τ ^ (m ^ 2) = q τ ^ m := fun τ ↦ by
    have := wParam_pow_mk (m := m) 1 τ; rwa [mul_one, mul_one] at this
  have heq : (fun τ : ℍ ↦ f m (some b) τ * wParam m τ ^ (m ^ 2))
      = (fun τ : ℍ ↦ (j (Acol m b.val • τ) * q (Acol m b.val • τ)) ^ 1)
        * (fun τ : ℍ ↦ zetaM m ^ (-(↑b.val * ↑(1:ℕ) : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * 1)) := by
    funext τ
    simp only [Pi.mul_apply]
    rw [hw2 τ, ← Fi_some_eq (m := m) 1 b τ, pow_one, mul_one]
  have hpe : Function.Periodic ((fun τ : ℍ ↦ f m (some b) τ * wParam m τ ^ (m ^ 2)) ∘ ofComplex)
      (m : ℝ) :=
    periodic_comp_ofComplex_of_vadd_gen hm (fun τ ↦ by rw [f_vadd_m, wParam_vadd_m])
  have hho : MDiff (fun τ : ℍ ↦ f m (some b) τ * wParam m τ ^ (m ^ 2)) :=
    (mdifferentiable_f (some b)).mul (mdifferentiable_wParam.pow (m ^ 2))
  have hbd : IsBoundedAtImInfty (fun τ : ℍ ↦ f m (some b) τ * wParam m τ ^ (m ^ 2)) := by
    rw [heq]
    exact Filter.BoundedAtFilter.mul
      (isBoundedAtImInfty_jqPow_comp 1 (Acol m b.val) (by simp [val_Acol]))
      (isBoundedAtImInfty_of_norm_le_one (fun τ ↦ norm_gB_le_one 1 b τ))
  refine goodQ_of_wHasSum hpe hho hbd (e := fun n ↦ (m ^ 2 - 1) + n)
    (a := fun n ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ)
      * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - 1)))
    (add_right_injective (m ^ 2 - 1))
    (fun n ↦ RI.mul_mem (intCast_mem_RI _) (zetaM_zpow_mem_RI _)) (fun τ ↦ ?_)
  have hraw := hasSum_coset_some (m := m) 1 b τ
  have hv : (f m (some b) τ) ^ 1 * q τ ^ (m * 1) = f m (some b) τ * wParam m τ ^ (m ^ 2) := by
    rw [pow_one, mul_one, hw2 τ]
  rw [hv] at hraw
  refine hraw.congr_fun (fun n ↦ ?_)
  rw [pow_one, smul_eq_mul, mul_one]
  ring_nf

lemma goodQ_w [NeZero m] (R : Subring ℂ) : GoodQ (m : ℝ) R (fun τ : ℍ ↦ wParam m τ) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨periodic_comp_ofComplex_of_vadd_gen hm (fun τ ↦ wParam_vadd_m τ),
    mdifferentiable_wParam, isBoundedAtImInfty_wParam, fun n ↦ ?_⟩
  have hHS : ∀ τ : ℍ,
      HasSum (fun k ↦ (if k = 1 then (1:ℂ) else 0) • wParam m τ ^ k) (wParam m τ) := by
    intro τ
    refine (hasSum_ite_eq (1 : ℕ) (wParam m τ)).congr_fun (fun k ↦ ?_)
    by_cases hk : k = 1
    · subst hk; simp
    · simp [hk]
  have := wExpansion_coeff_unique_raw
    (analyticAt_cuspFunction_zero hm (periodic_comp_ofComplex_of_vadd_gen hm wParam_vadd_m)
      mdifferentiable_wParam isBoundedAtImInfty_wParam)
    (periodic_comp_ofComplex_of_vadd_gen hm wParam_vadd_m) mdifferentiable_wParam
    isBoundedAtImInfty_wParam hHS n
  rw [← this]
  by_cases hn : n = 1
  · rw [if_pos hn]; exact R.one_mem
  · rw [if_neg hn]; exact R.zero_mem

lemma goodQ_G [NeZero m] (i : Option (ZMod m)) :
    GoodQ (m : ℝ) RI (fun τ : ℍ ↦ f m i τ * wParam m τ ^ (m ^ 2)) := by
  cases i with
  | none => exact goodQ_G_none
  | some b => exact goodQ_G_some b

lemma coeff_linMul_zero (α β : ℂ) (Q : Polynomial ℂ) :
    ((C α * X - C β) * Q).coeff 0 = -(β * Q.coeff 0) := by
  rw [sub_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_zero_eq_eval_zero]; simp

lemma coeff_linMul_succ (α β : ℂ) (Q : Polynomial ℂ) (k : ℕ) :
    ((C α * X - C β) * Q).coeff (k + 1) = α * Q.coeff k - β * Q.coeff (k + 1) := by
  rw [sub_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul]

/-- **The product induction.** Every coefficient of the pole-cleared orbit polynomial
`∏_i (w^{m²}·X − f_i·w^{m²})` is `GoodQ` at width `m` over the algebraic integers `ℤbar`. -/
lemma goodQ_prod_coeff [NeZero m] (s : Finset (Option (ZMod m))) :
    ∀ n : ℕ, GoodQ (m : ℝ) RI (fun τ : ℍ ↦
      (∏ i ∈ s, (C (wParam m τ ^ (m ^ 2)) * X
        - C (f m i τ * wParam m τ ^ (m ^ 2)))).coeff n) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hwpow : GoodQ (m : ℝ) RI (fun τ : ℍ ↦ wParam m τ ^ (m ^ 2)) :=
    (goodQ_w RI).pow hm (m ^ 2)
  classical
  induction s using Finset.induction with
  | empty =>
    intro n
    by_cases hn : n = 0
    · refine (goodQ_const hm (show (1:ℂ) ∈ RI from RI.one_mem)).of_eq (fun τ ↦ ?_)
      simp [hn]
    · refine (goodQ_const hm RI.zero_mem).of_eq (fun τ ↦ ?_)
      simp [Finset.prod_empty, coeff_one, hn]
  | @insert a s ha ih =>
    intro n
    cases n with
    | zero =>
      refine (((goodQ_G a).mul hm (ih 0)).neg hm).of_eq (fun τ ↦ ?_)
      rw [Finset.prod_insert ha, coeff_linMul_zero]
    | succ k =>
      refine ((hwpow.mul hm (ih k)).sub hm ((goodQ_G a).mul hm (ih (k + 1)))).of_eq (fun τ ↦ ?_)
      rw [Finset.prod_insert ha, coeff_linMul_succ]

/-- **Width-`m` integrality of `(orbitPoly).coeff n · q^N`.** For `m² (m+1) ≤ m·N`, the
function `(orbitPoly m τ).coeff n · q^N` is `GoodQ` at width `m` over the algebraic integers:
its `w`-expansion has algebraic-integer coefficients. -/
lemma goodQ_orbitPoly_coeff_mul_qpow [NeZero m] (n N : ℕ) (hN : m ^ 2 * (m + 1) ≤ m * N) :
    GoodQ (m : ℝ) RI (fun τ : ℍ ↦ (orbitPoly m τ).coeff n * q τ ^ N) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have key := goodQ_prod_coeff (Finset.univ (α := Option (ZMod m))) n
  have hwe : GoodQ (m : ℝ) RI (fun τ : ℍ ↦ wParam m τ ^ (m * N - m ^ 2 * (m + 1))) :=
    (goodQ_w RI).pow hm _
  refine (key.mul hm hwe).of_eq (fun τ ↦ ?_)
  have hpe : (∏ i : Option (ZMod m), (C (wParam m τ ^ (m ^ 2)) * X
        - C (f m i τ * wParam m τ ^ (m ^ 2)))).coeff n
      = wParam m τ ^ (m ^ 2 * (m + 1)) * (orbitPoly m τ).coeff n := by
    have hfac : ∀ i : Option (ZMod m),
        (C (wParam m τ ^ (m ^ 2)) * X - C (f m i τ * wParam m τ ^ (m ^ 2)))
          = C (wParam m τ ^ (m ^ 2)) * (X - C (f m i τ)) := fun i ↦ by rw [map_mul]; ring
    rw [Finset.prod_congr rfl (fun i _ ↦ hfac i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_option, ZMod.card, orbitPoly, ← C_pow, ← pow_mul, coeff_C_mul]
  have hcombine : wParam m τ ^ (m ^ 2 * (m + 1)) * wParam m τ ^ (m * N - m ^ 2 * (m + 1))
      = q τ ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hN, pow_mul, wParam_pow_m]
  change (orbitPoly m τ).coeff n * q τ ^ N
      = (∏ i : Option (ZMod m), (C (wParam m τ ^ (m ^ 2)) * X
          - C (f m i τ * wParam m τ ^ (m ^ 2)))).coeff n * wParam m τ ^ (m * N - m ^ 2 * (m + 1))
  rw [hpe, mul_right_comm, hcombine, mul_comm]

/-- **Matching width-1 and width-`m` coefficients.** For a function `F` that is both `1`-periodic
and `m`-periodic, holomorphic and bounded at the cusp, the `p`-th ordinary `q`-coefficient equals
the `(m·p)`-th `w`-coefficient (`q = w^m`). -/
lemma widthm_coeff_eq [NeZero m] {F : ℍ → ℂ}
    (hp1 : Function.Periodic (F ∘ ofComplex) 1) (hpm : Function.Periodic (F ∘ ofComplex) (m : ℝ))
    (hho : MDiff F) (hbd : IsBoundedAtImInfty F) (p : ℕ) :
    (qExpansion 1 F).coeff p = (qExpansion (m : ℝ) F).coeff (m * p) := by
  classical
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hmne : m ≠ 0 := NeZero.ne m
  set a : ℕ → ℂ := fun p ↦ (qExpansion 1 F).coeff p with ha
  set c : ℕ → ℂ := Function.extend (fun p ↦ m * p) a (fun _ ↦ 0) with hc
  have hei : Function.Injective (fun p : ℕ ↦ m * p) :=
    fun x y h ↦ Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hmne) h
  have hHSw : ∀ τ : ℍ, HasSum (fun t ↦ c t • wParam m τ ^ t) (F τ) := by
    intro τ
    have h1 : HasSum (fun p ↦ a p • q τ ^ p) (F τ) := hasSum_qExpansion one_pos hp1 hho hbd τ
    have h2 : HasSum (fun p ↦ a p • wParam m τ ^ (m * p)) (F τ) := by
      refine h1.congr_fun (fun p ↦ ?_); rw [pow_mul, wParam_pow_m]
    have hz : ∀ t ∉ Set.range (fun p : ℕ ↦ m * p), (fun t ↦ c t • wParam m τ ^ t) t = 0 := by
      intro t ht
      have hct : c t = 0 :=
        Function.extend_apply' _ _ _ (fun ⟨p, hp⟩ ↦ ht ⟨p, hp⟩)
      change c t • wParam m τ ^ t = 0; rw [hct, zero_smul]
    rw [← hei.hasSum_iff hz]
    refine h2.congr_fun (fun p ↦ ?_)
    simp only [Function.comp_apply, hc, hei.extend_apply]
  have hFan : AnalyticAt ℂ (cuspFunction (m : ℝ) F) 0 := analyticAt_cuspFunction_zero hm hpm hho hbd
  have huniq := wExpansion_coeff_unique_raw hFan hpm hho hbd hHSw (m * p)
  have hcval : c (m * p) = a p := hei.extend_apply a (fun _ ↦ 0) p
  rw [hcval] at huniq; exact huniq

/-- **The `⊥`-gate `hZ`, discharged for each `n`.** Each orbit-polynomial coefficient is
cusp-meromorphic of finite order with coefficients in `⊥ ⊆ ℂ` (the integers): rational (averaging)
and an algebraic integer (the `ℤ[ζ_m]` `w`-expansion), hence in `⊥`. -/
theorem orbitPoly_coeff_isCuspMeroR_bot [Fact m.Prime] (n : ℕ) :
    ∃ N : ℕ, IsCuspMeroR (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) N (⊥ : Subring ℂ) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  obtain ⟨P, hP⟩ := mem_polyJ_iff.mp (orbitPoly_coeff_mem_polyJ (m := m) n)
  refine ⟨P.natDegree + (m ^ 2 + m), ?_⟩
  set N := P.natDegree + (m ^ 2 + m) with hNdef
  have hrat : IsCuspMeroR (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) N RQ :=
    orbitPoly_coeff_isCuspMeroR_RQ n P hP N (by omega)
  have hNint : m ^ 2 * (m + 1) ≤ m * N := by
    rw [hNdef]; nlinarith [Nat.zero_le (m * P.natDegree)]
  have hint : GoodQ (m : ℝ) RI (fun τ : ℍ ↦ (orbitPoly m τ).coeff n * q τ ^ N) :=
    goodQ_orbitPoly_coeff_mul_qpow n N hNint
  refine ⟨hrat.periodic, hrat.holo, hrat.bdd, fun p ↦ ?_⟩
  -- the `p`-th `q`-coefficient of `coeff_n · q^N`
  have hRQ : (qExpansion 1 (fun τ : ℍ ↦ (orbitPoly m τ).coeff n * q τ ^ N)).coeff p ∈ RQ :=
    hrat.coeff_mem p
  have hRI : (qExpansion 1 (fun τ : ℍ ↦ (orbitPoly m τ).coeff n * q τ ^ N)).coeff p ∈ RI := by
    rw [widthm_coeff_eq hrat.periodic hint.per hrat.holo hrat.bdd p]
    exact hint.mem (m * p)
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp hRQ
  exact mem_bot_of_integral_of_rat (mem_RI_iff.mp hRI) ⟨r, hr.symm⟩


/-! ## The unconditional keystone `Φ_m ∈ ℤ[Y][X]` and the unconditional `ℚ`-root bridge -/

/-- **(B6) fully closed.** For a prime `m`, the modular polynomial `Φ_m ∈ ℤ[Y][X]` exists with the
keystone identity `∏_i (X − f_i τ) = Φ_m(X, j τ)` for every `τ`. The `⊥`-coefficient
cusp-meromorphy gate `hZ` of `exists_PhiZ` is discharged by the `w`-expansion integrality machinery
(`orbitPoly_coeff_isCuspMeroR_bot`): rationality from the `ℚ`-averaging, algebraic integrality from
the `ℤ[ζ_m]`-coefficient `w`-expansion, combined pointwise by `mem_bot_of_integral_of_rat`. -/
theorem exists_PhiZ_closed [Fact m.Prime] :
    ∃ PhiZ : Polynomial (Polynomial ℤ),
      ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ :=
  exists_PhiZ orbitPoly_coeff_isCuspMeroR_bot

/-- **The root bridge, unconditional `ℚ`-version.** Instantiating `PhiQ_eval_j_root` with the
parallel agent's `exists_PhiQ_closed`: for a prime `m`, if `j σ = f m i τ` for some coset index
`i` (a CM relation), then there is a modular polynomial `Φ_m ∈ ℚ[Y][X]` with the keystone identity
for which `Φ_m(j σ, j τ) = 0`. This is the shape `Rationality.lean` / `MasserA1.lean` consume. -/
theorem exists_PhiQ_j_root [Fact m.Prime] {τ σ : ℍ} {i : Option (ZMod m)} (h : j σ = f m i τ) :
    ∃ PhiQ : Polynomial (Polynomial ℚ),
      (∀ ρ : ℍ, orbitPoly m ρ = specializeY (j ρ) PhiQ) ∧
        (specializeY (j τ) PhiQ).eval (j σ) = 0 := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  obtain ⟨PhiQ, hPhiQ⟩ := exists_PhiQ_closed (m := m)
  exact ⟨PhiQ, hPhiQ, PhiQ_eval_j_root PhiQ hPhiQ h⟩

end Chudnovsky
