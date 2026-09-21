/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.PolynomialPresentation

/-!
# Primes of degree one

A series of degree one is prime exactly when it has no non-unit divisor with finite support.
Primality below degree `ω` makes such a series primal, and a factorisation into two non-units
would, by the degree formula, give one factor of degree zero, that is, of finite support; an
irreducible primal element is prime. Conversely a prime is irreducible, so in `b = p q` with `p`
of finite support one factor is a unit, and it is not `q`: that would force `deg b = deg p = 0`.
-/

open scoped HahnSeries NatOrdinal

universe v

public section

namespace Berarducci

open Berarducci HahnSeries HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- An ordinal (in `NatOrdinal`) at most `1` is `0` or `1`. -/
private theorem natOrdinal_eq_zero_or_one_of_le_one {a : NatOrdinal} (h : a ≤ 1) :
    a = 0 ∨ a = 1 :=
  Order.le_one_iff.mp h

/-- A series of degree one is prime if and only if every finite-support divisor of it is a unit. -/
@[blueprint "cor:degree-one"
  (phase := "Primality and factorisation for real exponents")
  (title := "Primality criterion for series of degree one")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and
    $b\in K((\mathbb R^{\le 0}))$ a series with $\deg(b)=1$.  Then $b$ is prime
    in $K((\mathbb R^{\le 0}))$ if and only if every divisor of $b$ with finite
    support is a unit.
  -/)
  (proof := /--
  Suppose first that $b$ is prime and write $b=pq$ with $p$ of finite support.
  Irreducibility makes $p$ or $q$ a unit.  If $q$ were a unit, multiplicativity
  of the degree would give $\deg(p)=1$, contradicting the finite support of $p$;
  hence $p$ is a unit.  Conversely, assume that every finite-support divisor of
  $b$ is a unit.  In a factorisation $b=cd$ into nonzero factors, degree
  multiplicativity gives $\deg(c)+\deg(d)=1$, so one factor has degree $0$ and
  therefore finite support.  The hypothesis makes that factor a unit, proving
  that $b$ is irreducible.  Every series is primal by
  \ref{thm:hahn-series-primality}, so $b$ is prime.
  -/)]
theorem prime_iff_of_degree_eq_one {b : Series K}
    (hb : (b : K⟦ℝ⟧).degree = (1 : NatOrdinal)) :
    Prime b ↔ ∀ p : Series K, p ∣ b → (p : K⟦ℝ⟧).support.Finite → IsUnit p := by
  have hb0 : b ≠ 0 := fun h ↦ by
    rw [h] at hb; simp at hb
  have hbdeg : degreeValuation K b = (1 : NatOrdinal) := by rw [degreeValuation_apply, hb]
  constructor
  · -- a prime is irreducible, so in `b = p q` one factor is a unit; it is not `q`, since then
    -- `deg b = deg p = 0`
    intro hprime p hpb hpfin
    obtain ⟨q, rfl⟩ := hpb
    refine (hprime.irreducible.isUnit_or_isUnit rfl).resolve_right fun hq ↦ ?_
    have hpdeg : degreeValuation K p ≤ 0 := by
      rw [degreeValuation_apply]; exact degree_le_zero_iff.mpr hpfin
    have hmul := (degreeValuation K).map_mul p q
    rw [hbdeg, seriesDegree_eq_zero_of_isUnit hq, add_zero] at hmul
    exact absurd (hmul ▸ hpdeg) (by simp)
  · intro hdiv
    have hprimal : IsPrimal b := Berarducci.isPrimal b
    refine Irreducible.prime_of_isPrimal ⟨fun hu ↦ ?_, fun c d hcd ↦ ?_⟩ hprimal
    · have := seriesDegree_eq_zero_of_isUnit hu
      rw [hbdeg] at this
      exact absurd this (by simp)
    · -- a factorisation `b = c d` into non-units has a factor of degree zero
      by_contra hnot
      push Not at hnot
      have hc0 : c ≠ 0 := fun h ↦ hb0 (by rw [hcd, h, zero_mul])
      have hd0 : d ≠ 0 := fun h ↦ hb0 (by rw [hcd, h, mul_zero])
      have hsum : degreeValuation K c + degreeValuation K d = (1 : NatOrdinal) := by
        rw [← (degreeValuation K).map_mul, ← hcd, hbdeg]
      obtain ⟨γ, hγ⟩ := WithBot.ne_bot_iff_exists.mp
        ((degreeValuation K).map_ne_bot_of_ne_zero (degreeValuation_isSeparated K) hc0)
      obtain ⟨δ, hδ⟩ := WithBot.ne_bot_iff_exists.mp
        ((degreeValuation K).map_ne_bot_of_ne_zero (degreeValuation_isSeparated K) hd0)
      rw [← hγ, ← hδ, ← WithBot.coe_add, WithBot.coe_inj] at hsum
      have hγle : γ ≤ 1 := hsum ▸ (NatOrdinal.le_add_right : γ ≤ γ + δ)
      have hδle : δ ≤ 1 := hsum ▸ (NatOrdinal.le_add_left : δ ≤ γ + δ)
      -- the factor of degree zero has finite support, hence is a unit by hypothesis
      have hfin : ∀ {x : Series K}, degreeValuation K x = (0 : NatOrdinal) →
          (x : K⟦ℝ⟧).support.Finite := fun hx ↦ by
        rw [degreeValuation_apply] at hx
        exact degree_le_zero_iff.mp hx.le
      rcases natOrdinal_eq_zero_or_one_of_le_one hγle with hγ0 | hγ1
      · exact hnot.1 (hdiv c (Dvd.intro d hcd.symm) (hfin (by rw [← hγ, hγ0])))
      · rcases natOrdinal_eq_zero_or_one_of_le_one hδle with hδ0 | hδ1
        · exact hnot.2 (hdiv d (Dvd.intro_left c hcd.symm) (hfin (by rw [← hδ, hδ0])))
        · rw [hγ1, hδ1] at hsum
          exact absurd (add_left_cancel (a := (1 : NatOrdinal)) (hsum.trans (add_zero 1).symm))
            one_ne_zero

end Berarducci

end
