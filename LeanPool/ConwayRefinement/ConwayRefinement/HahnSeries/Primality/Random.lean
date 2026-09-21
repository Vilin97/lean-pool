/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.MainTheorem

/-!
# Random series of finite degree are prime

Fornasiero, Lavi, L'Innocente and Mantova prove that a random series `b` with `sup(b) = 0` and
`ot(b) = ω^n · m + β`, `1 ≤ m, n < ω`, `β < ω^n`, is irreducible, as is `b + r` for every `r`
with `ot(r) < ω^n` and `sup(b + r) = 0` (FLLM24, Theorem 1.8), and that a random principal
series of finite degree `n ≥ 1` is irreducible (FLLM24, Corollary 1.5). These series have
degree below `ω`, so the finite-degree theorem makes them prime.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open Berarducci HahnSeries HahnSeries.Nonpositive FLLM24

variable {K : Type v} [Field K]

/-- `ω^n · m + β < ω^(n + 1)` when `β < ω^n`. -/
theorem omega0_opow_mul_add_lt_opow_succ {n m : ℕ} {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) :
    Ordinal.omega0 ^ (n : Ordinal) * m + β < Ordinal.omega0 ^ ((n + 1 : ℕ) : Ordinal) := by
  calc Ordinal.omega0 ^ (n : Ordinal) * m + β
      < Ordinal.omega0 ^ (n : Ordinal) * m + Ordinal.omega0 ^ (n : Ordinal) :=
        (add_lt_add_iff_left _).mpr hβ
    _ = Ordinal.omega0 ^ (n : Ordinal) * ((m + 1 : ℕ) : Ordinal) := by
        rw [Nat.cast_succ, mul_add_one]
    _ ≤ Ordinal.omega0 ^ (n : Ordinal) * Ordinal.omega0 :=
        mul_le_mul_right (Ordinal.natCast_lt_omega0 (m + 1)).le _
    _ = Ordinal.omega0 ^ ((n + 1 : ℕ) : Ordinal) := by
        rw [Nat.cast_succ, Ordinal.opow_add, Ordinal.opow_one]

/-- A series of order type `ω^n · m + β` with `β < ω^n` has degree below `n + 1`. -/
theorem degree_lt_succ_of_supportOrderType_eq {n m : ℕ} {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) {b : Series K}
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β) :
    (b : K⟦ℝ⟧).degree < (((n + 1 : ℕ) : NatOrdinal) : WithBot NatOrdinal) := by
  rw [degree_lt_coe_iff_supportOrderType_lt_wpow, NatOrdinal.val_wpow, NatOrdinal.val_natCast, hot]
  exact omega0_opow_mul_add_lt_opow_succ hβ

/-- Degree below a natural number is degree below `ω`. -/
theorem degree_lt_omega_of_lt_natCast {x : K⟦ℝ⟧} {n : ℕ}
    (h : x.degree < ((n : NatOrdinal) : WithBot NatOrdinal)) :
    x.degree < (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal) :=
  h.trans (WithBot.coe_lt_coe.mpr (NatOrdinal.lt_omega0.mpr ⟨n, rfl⟩))

variable [CharZero K]

/-- A random series `b` with `sup(b) = 0` and `ot(b) = ω^n · m + β`, `1 ≤ m, n < ω`,
`β < ω^n`, is prime: irreducible by FLLM24 Theorem 1.8, of degree `n < ω`. -/
@[blueprint "cor:random-series-prime"
  (phase := "Primality and factorisation for real exponents")
  (title := "Random series of finite Cantor degree are prime")
  (statement := /--
    Let $K$ be a field of characteristic $0$. Let $m,n\ge1$, let
    $\beta<\omega^n$, and let $b\in K((\mathbb R^{\le0}))$ be random. If
    \[
      \sup(b)=0,
      \qquad
      \operatorname{ot}(\operatorname{supp}(b))=\omega^n\cdot m+\beta,
    \]
    then $b$ is prime in $K((\mathbb R^{\le0}))$.
  -/)
  (proof := /--
    \cite[Theorem~1.8]{FLLM} makes $b$ irreducible. By
    \ref{cor:hahn-series-irreducible-is-prime}, every irreducible series in
    $K((\mathbb R^{\le0}))$ is prime.
  -/)]
theorem prime_of_isRandom {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) {b : Series K} (hb : IsRandom b)
    (hsup : supportSup b = 0)
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β) :
    Prime b :=
  Berarducci.prime_of_irreducible (irreducible_of_isRandom hn hm hβ hb hsup hot)

/-- For `b` as in `prime_of_isRandom`, `b + r` is prime for every `r` with `ot(r) < ω^n` and
`sup(b + r) = 0`. -/
@[blueprint "cor:random-series-small-perturbation"
  (phase := "Primality and factorisation for real exponents")
  (title := "Lower-order perturbations of random series are prime")
  (statement := /--
    Let $K$ be a field of characteristic $0$. Let $m,n\ge1$ and
    $\beta<\omega^n$. Suppose that $b\in K((\mathbb R^{\le0}))$ is random and
    \[
      \operatorname{ot}(\operatorname{supp}(b))=\omega^n\cdot m+\beta.
    \]
    If $r\in K((\mathbb R^{\le0}))$ satisfies
    \[
      \operatorname{ot}(\operatorname{supp}(r))<\omega^n,
      \qquad
      \sup(b+r)=0,
    \]
    then $b+r$ is prime in $K((\mathbb R^{\le0}))$.
  -/)
  (proof := /--
    \cite[Theorem~1.8]{FLLM} makes $b+r$ irreducible. Apply
    \ref{cor:hahn-series-irreducible-is-prime}.
  -/)]
theorem prime_add_of_isRandom {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) {b : Series K} (hb : IsRandom b)
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β)
    {r : Series K} (hr : (r : K⟦ℝ⟧).supportOrderType < Ordinal.omega0 ^ (n : Ordinal))
    (hsup : supportSup (b + r) = 0) :
    Prime (b + r) :=
  Berarducci.prime_of_irreducible (irreducible_add_of_isRandom hn hm hβ hb hot hr hsup)

/-- A random principal series of positive finite degree is prime: irreducible by FLLM24
Corollary 1.5, of degree below `ω`. -/
@[blueprint "cor:random-principal-series-prime"
  (phase := "Primality and factorisation for real exponents")
  (title := "Random principal series of positive finite degree are prime")
  (statement := /--
    Let $K$ be a field of characteristic $0$. Every random principal series
    $b\in K((\mathbb R^{\le0}))$ with
    \[
      0<\deg(b)<\omega
    \]
    is prime in $K((\mathbb R^{\le0}))$.
  -/)
  (proof := /--
    Write $\deg(b)=n$ with $1\le n<\omega$. \cite[Corollary~1.5]{FLLM} makes $b$
    irreducible, so \ref{cor:hahn-series-irreducible-is-prime} makes it prime.
  -/)]
theorem prime_of_isRandom_of_isPrincipal {b : Series K} (hb : IsRandom b) (hp : IsPrincipal b)
    (hpos : 0 < (b : K⟦ℝ⟧).degree)
    (hfin : (b : K⟦ℝ⟧).degree < (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal)) :
    Prime b := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hpos)
  have hfin' := hfin
  have hpos' := hpos
  rw [← hd] at hfin' hpos'
  obtain ⟨n, rfl⟩ := NatOrdinal.lt_omega0.mp (WithBot.coe_lt_coe.mp hfin')
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    subst h
    simp at hpos'
  exact Berarducci.prime_of_irreducible (irreducible_of_isRandom_of_isPrincipal hn hb hp hd.symm)

end Berarducci

end
