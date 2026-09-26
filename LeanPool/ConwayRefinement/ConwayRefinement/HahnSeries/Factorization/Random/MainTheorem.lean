/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.RandomBlocks

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree

/-!
# Irreducibility of random series of finite degree

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Theorem 1.8 for `α = n < ω`, and Corollary 1.5.

Theorem 1.8: let `b ∈ K((ℝ^{≤0}))` with `sup(b) = 0` and `ot(b) = m ω^n + β`, `m ≥ 1`,
`β < ω^n`. If `b` is random, then `b` is irreducible, and so is `b + r` for every `r` with
`ot(r) < ω^n` and `sup(b + r) = 0`. The proof is the one of the source, Corollary 4.13 for
`α = n`: the normal form of `b` gives `b = ∑ᵢ bᵢ t^{γᵢ} + r'` with `b₁, …, bₘ ∈ P_n` and
`deg(r') < n`; randomness of `b` makes the blocks mutually random, hence hereditarily
`rv_J`-independent; and Proposition 3.2 applies to `b + r = ∑ᵢ bᵢ t^{γᵢ} + (r' + r)`.

Corollary 1.5: a random principal series of degree `n ≥ 1` is irreducible, the case `m = 1`,
`β = 0`, `r = 0`. The source states Corollary 1.5 for every `n ∈ ℕ`; at `n = 0` a principal
series is a nonzero constant, a unit, and the statement is false as printed, so the corollary is
stated here for `n ≥ 1`.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- FLLM24, Theorem 1.8 for `α = n ≥ 1`, the perturbed form: if `b` is random with
`ot(b) = ω^n · m + β`, `m ≥ 1`, `β < ω^n`, then `b + r` is irreducible for every `r` with
`ot(r) < ω^n` and `sup(b + r) = 0`. -/
theorem irreducible_add_of_isRandom {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) {b : Series K} (hb : IsRandom b)
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β)
    {r : Series K} (hr : (r : K⟦ℝ⟧).supportOrderType < Ordinal.omega0 ^ (n : Ordinal))
    (hsup : supportSup (b + r) = 0) :
    Irreducible (b + r) := by
  obtain ⟨d⟩ := exists_blockDecomposition hn hβ hot
  have hQ : HereditarilyRVIndependent n d.block := d.hereditarilyRVIndependent_block hn hb
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max d.exponent
  have hr' : ((d.rest + r : Series K) : K⟦ℝ⟧).degree <
      ((n : NatOrdinal) : WithBot NatOrdinal) := by
    have hrdeg : (r : K⟦ℝ⟧).degree < ((n : NatOrdinal) : WithBot NatOrdinal) := by
      rw [degree_lt_coe_iff_supportOrderType_lt_wpow, NatOrdinal.val_wpow, NatOrdinal.val_natCast]
      exact hr
    rw [Subring.coe_add]
    exact (HahnSeries.degree_add_le _ _).trans_lt (max_lt d.rest_degree hrdeg)
  have heq : b + r = blockSum d.block d.exponent d.exponent_nonpos (d.rest + r) := by
    rw [blockSum_def, ← add_assoc, ← blockSum_def, ← d.eq_blockSum]
  rw [heq] at hsup ⊢
  exact irreducible_blockSum hn d.block_isPrincipal hQ d.exponent_nonpos
    d.exponent_strictMono.injective i₀ hi₀ hr' hsup

/-- FLLM24, Theorem 1.8 for `α = n ≥ 1`: a random series `b` with `sup(b) = 0` and
`ot(b) = ω^n · m + β`, `m ≥ 1`, `β < ω^n`, is irreducible. -/
theorem irreducible_of_isRandom {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {β : Ordinal}
    (hβ : β < Ordinal.omega0 ^ (n : Ordinal)) {b : Series K} (hb : IsRandom b)
    (hsup : supportSup b = 0)
    (hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * m + β) :
    Irreducible b := by
  have h := irreducible_add_of_isRandom hn hm hβ hb hot (r := 0)
    (by
      rw [ZeroMemClass.coe_zero, supportOrderType_zero]
      exact Ordinal.opow_pos _ Ordinal.omega0_pos)
    (by rw [add_zero]; exact hsup)
  rwa [add_zero] at h

/-- FLLM24, Corollary 1.5 for `n ≥ 1`: a random principal series of degree `n` is
irreducible. -/
theorem irreducible_of_isRandom_of_isPrincipal {n : ℕ} (hn : 1 ≤ n) {b : Series K}
    (hb : IsRandom b) (hp : IsPrincipal b)
    (hdeg : (b : K⟦ℝ⟧).degree = ((n : NatOrdinal) : WithBot NatOrdinal)) :
    Irreducible b := by
  have hot : (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (n : Ordinal) * (1 : ℕ) + 0 := by
    rw [Nat.cast_one, mul_one, add_zero]
    have h := hp.supportOrderType_eq_wpow_of_degree_eq hdeg
    rw [h, NatOrdinal.val_wpow, NatOrdinal.val_natCast]
  exact irreducible_of_isRandom hn le_rfl (Ordinal.opow_pos _ Ordinal.omega0_pos) hb
    hp.supportSup_eq_zero hot

end FLLM24

end
